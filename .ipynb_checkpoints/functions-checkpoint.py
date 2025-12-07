from sage.sat.converters.polybori import CNFEncoder
from sage.sat.solvers.dimacs import DIMACS
from sage.sat.solvers import Glucose
from operator_gb import *
from sage.all import *
import time
import random
import warnings
from pysat.formula import CNF
from pysat.solvers import Cadical195
from collections import OrderedDict
from pysat.solvers import Minisat22, Solver
from pysat.pb import *
from .help_functions import *
import subprocess
import tempfile
from cadical import *
from itertools import product


#takes a list of polynomials obtained by the matrix, converts it to boolean and applies sat solver
def solve_system(polynomials, element=None):
    r"""
    Solves a system of Boolean polynomial equations.

    Input:
        - ``polynomials`` -- list of polynomials
        - ``element`` -- optional list of additional polynomials

    Output:
        A tuple containing:
            - sat_dict: satisfying assignment for original variables
            - e: CNFEncoder instance
            - solution: list of variable assignments (in DIMACS form)
            - solver: Cadical195 solver instance
            - cnf: CNF object
            - test: list of all processed polynomials
            - zipped: full variable assignment dict
     Example:
        sage: R.<x,y,z> = BooleanPolynomialRing()
        sage: polys = [x + y + 1, z + x*y]
        sage: solve_system(polys)
    """
    el = element or []

    # Gather all original variables (excluding tseytin-introduced ones)
    original_vars = {v for p in polynomials + el for v in p.variables()}

    # Apply Tseytin transformation if `element` is provided
    tseytin_list = []
    if el:
        polynomial, tseytin_list = tseytin(el)
        tseytin_list.append(polynomial)

    # Combine all polynomials to process
    all_polys = polynomials + tseytin_list

    # Collect all variables for BooleanPolynomialRing
    all_vars = sorted({v for p in all_polys for v in p.variables()})
    Ring = BooleanPolynomialRing(names=all_vars)

    # Convert to Boolean polynomials
    bool_polys = []
    for p in all_polys:
        if '^' in str(p):  # Convert Sage-style exponentiation
            p = SR(str(p).replace('^', '**'))
        bp = Ring(p)
        if bp not in (0, 1):
            bool_polys.append(bp)

    # Encode to CNF
    solver = DIMACS()
    encoder = CNFEncoder(solver, Ring)
    for poly in bool_polys:
        encoder.clauses_dense(poly)

    cnf = CNF(from_clauses=[clause[0] for clause in solver.clauses()])

    # Solve the CNF with Cadical
    solution = run_cadical_with_cnf(cnf)

    # Map solution back to variable names
    var_names = [str(var) for var in encoder.phi[1:]]  # skip phi[0]
    assignment = dict(zip(var_names, solution))

    # Filter only original variables (excluding Tseytin-introduced ones)
    sat_dict = {str(v): assignment[str(v)] for v in original_vars if str(v) in assignment}

    return sat_dict, encoder, solution, cnf, all_polys, assignment


def tseytin(polynomials):
    r"""
    Input:
        - ``polynomials`` -- list of symbolic expressions or polynomials

    Output:
        - Tseytin-transformed product of symbolic variables
        - List of equations relating new vars to the original polynomials

    Example:
        sage: x, y, z = var('x y z')
        sage: p1 = x^2 + 2*x + 1
        sage: p2 = y^2 - y + 1
        sage: p3 = z^3 + z^2 + z + 1
        sage: tseytin([p1, p2, p3])
    """
    symbolic_vars = [SR.var(f'k_{i}') for i in range(len(polynomials))]
    product = prod(symbolic_vars)
    equations = [k - p for k, p in zip(symbolic_vars, polynomials)]
    return product, equations

def first_sat_solution(assumptions, f, Q, dictionary):
    r"""
    Input:
        - `assumptions` -- A list of assumption polynomials
        - `f` -- A polynomial
        - `Q` -- A Quiver
        - `dictionary` -- A dictionary of matrix sizes

    Output:
        - A tuple containing:
            filtered: solution in matrix form (main output)
            symbolic_matrices, sol_dictionary, e, solution, solver, cnf, test, zipped
    Example:
        sage: R.<x,y> = FreeAlgebra(QQ)
        sage: Q = Quiver([('U', 'U', x), ('U', 'U', y)])
        sage: f = x*y
        sage: assumptions = [x + y]
        sage: dictionary = {'U':2}
        sage: first_sat_solution(assumptions, f, Q, dictionary)[0]
    """

    s = time.process_time()
    I = NCIdeal(assumptions)

    # Compatibility check (fused loop)
    for g in assumptions + [f]:
        if not Q.is_compatible(g):
            raise ValueError(f"{g} is not compatible with the quiver")

    # Convert assumption polynomials to matrices
    symbolic_matrices = {}
    matrices = []

    # Flattens polynomial into matrix form and caches symbolic variables for SAT encoding.
    def collect_matrix_data(poly):
        var_map = str
        matrix_sizes = [[dictionary[Q.target(var_map(v))[0]], dictionary[Q.source(var_map(v))[0]]] for v in poly.variables()]
        mat, mat_dict = poly_to_matrix(poly, matrix_sizes)
        for k, m in mat_dict.items():
            symbolic_matrices.setdefault(k, m)
        return [el for row in mat.rows() for el in row]

    # Process assumption matrices
    for p in assumptions:
        matrices.extend(collect_matrix_data(p))

    # Convert target polynomial f
    matrix_sizes = [
        [dictionary[Q.target(str(v))[0]], dictionary[Q.source(str(v))[0]]]
        for v in f.variables()
    ]
    f_matrix, matrix_list = poly_to_matrix(f, matrix_sizes)

    for key, m in matrix_list.items():
        if m not in symbolic_matrices.values():
            symbolic_matrices[key] = m

    f_matrix_flat = [el for row in f_matrix.rows() for el in row]
    #element = [1 - el for el in f_matrix_flat]
    element = [1 - SR(f"soft_{i+1}") * el for i, el in enumerate(f_matrix_flat)]

    # Solve the system
    sol_dictionary, e, solution, cnf, test, zipped = solve_system(matrices, element)

    # Evaluate symbolic matrices using solution
    sym_mat_copy = {}

    for key, m in symbolic_matrices.items():
        if '_' in key:  # skip auxiliary vars faster
            continue

        rows, cols = m.nrows(), m.ncols()
        m_copy = zero_matrix(rows, cols)

        last_entry_name = None  # only used for naming key

        for i in range(rows):
            for j in range(cols):
                v_str = str(m[i, j])
                m_copy[i, j] = 1 if sol_dictionary.get(v_str, 0) > 0 else 0
                last_entry_name = v_str  # updated every iteration, used after loop

        # determine how to name the matrix key
        parts = last_entry_name.split('_') if last_entry_name else []
        output_key = '_'.join(parts[:2]) if 'adj' in last_entry_name else parts[0]
        sym_mat_copy[output_key] = m_copy

    filtered = {k: v for k, v in sym_mat_copy.items() if not k.startswith('k')}

    # Remove Tseytin-introduced variables
    filtered = {
        key: value for key, value in sym_mat_copy.items()
        if not key.startswith('k')
    }

    return filtered, symbolic_matrices, sol_dictionary, e, solution, cnf, test, zipped

def run_cadical_with_cnf(cnf: CNF, cadical_path="cadical/build/cadical"):
    """
    Run the system-installed CaDiCaL binary on a PySAT CNF object
    and return a model identical to PySAT's Cadical195.get_model().
    
    Args:
        cnf (CNF): a PySAT CNF object
        cadical_path (str): path to the cadical binary
    
    Returns:
        list[int] if SAT
        None if UNSAT
    """
    # Write CNF to a temporary DIMACS file
    with tempfile.NamedTemporaryFile(mode="w", suffix=".cnf", delete=False) as tmp:
        cnf.to_file(tmp.name)
        cnf_file = tmp.name

    # Run cadical on the file
    result = subprocess.run(
        [cadical_path,"--seed=1234", cnf_file],
        capture_output=True,
        text=True
    )

    # Parse output
    status = None
    model = []
    for line in result.stdout.splitlines():
        if line.startswith("s "):
            status = line.split()[1]
        elif line.startswith("v "):
            lits = list(map(int, line.split()[1:]))
            if lits and lits[-1] == 0:
                lits = lits[:-1]
            model.extend(lits)

    if status == "SATISFIABLE":
        return model
    else:
        return None




def construct_counterexample(assumptions,claims,Q=None,dimensions=None,n=2,random_tries=0,verbosity=0,one_lifting=True):
    r"""
    Input:
        - ``assumptions`` -- A list of noncommutative polynomials
        - ``claims`` -- another polynomial list
        - ``Q`` -- a Quiver
        - ``dimensions`` -- a dictionary defining sizes of dopoly_to_matrixs
        - ``n`` -- a natural number,indicates if we want to lift to 2^n
        - ``random_tries`` -- and integer number. If 0 we try hensel lifting deterministic, if >0 we try hensel lifting not deterministic for random_tries number of                 tries
        - ``verbosity`` -- an integer number if >0 we output what the program does

    Output:
        - A counterexample in rational numbers if there exists one
    Example:
        sage: A.<x,y> = FreeAlgebra(QQ)
        sage: assumptions = [x*y]
        sage: claims = [x]
        sage: Q = Quiver([('U','U',x), ('U','U',y)])
        sage: dictionary = {'U':2}
        sage: n = 2
        sage: construct_counterexample(assumptions,claims,Q,dictionary,n)
    """
    start_time = time.process_time()
    deterministic = not random_tries

    if Q is None:
        Q, dimensions = generate_quiver_dict(assumptions, claims)

    assumptions, claims, Q, mapping = process_free_algebra_elements(assumptions, claims, Q)
    I = NCIdeal(assumptions)

    if verbosity > 0:
        print(f'Preprocessing done in {time.process_time() - start_time:.4f}s')
        print('Computing a first SAT solution...')

    (
        _filtered, symbolic_matrices, _sol_dict, e,
        _solution, cnf, _test, _zipped
    ) = first_sat_solution(assumptions, claims[0], Q, dimensions)
    string_phi = [str(x) for x in e.phi]
    vars_a = symbolic_matrices['a'].list()
    vars_a = [str(x) for x in vars_a]
    vars_a.remove('a_1_2')
    vars_a.remove('a_2_3')
    vars_a.remove('a_1_3')
    a_1_2_index =string_phi.index('a_1_2')
    cnf.append([a_1_2_index])
    a_2_3_index = string_phi.index('a_2_3')
    cnf.append([a_2_3_index])
    a_1_3_index =string_phi.index('a_1_3')
    cnf.append([a_1_3_index])
    indices = [string_phi.index(e) for e in vars_a]
    for i in indices:
        cnf.append([-i])
    if verbosity > 0:
        print(f'Initial SAT computation done in {time.process_time() - start_time:.4f}s')

    attempt = 0
    while True:
        solution = run_cadical_with_cnf(cnf)
        if solution == None:
            print("\nAll SAT solutions exhausted.")
            break
        sat_dict = extract_sat_dict(solution, e.phi[1:])
        filtered = build_matrix_model(solution, symbolic_matrices, sat_dict)
        success = False
        
        if n == 2 and one_lifting==True:
            try:
                lift =  one_lifting(assumptions, filtered, f=claims[0])
                if check_counterexample(assumptions, lift,claims, Q):
                    success = True
            except:
                continue
        else:
            for _ in range(1 + max(0, random_tries)):
                try:
                    lift = multi_lift_solution(assumptions, n, filtered,claims[0], deterministic)
                    if check_counterexample(assumptions, lift,claims, Q):
                        success = True
                        break
                except ArithmeticError:
                    continue

        if success:
            lift = reverse_mapping(lift, mapping)
            if verbosity > 0:
                print(f'\nCounterexample found on attempt #{attempt + 1}')
                for key, matrix in lift.items():
                    print(f'{key}:')
                    for row in matrix:
                        print(f'    {row}')
            return lift

        if verbosity > 0:
            print(f'\rAttempt #{attempt + 1}: Failed. Trying another SAT solution...', end='')
        attempt += 1
        cnf.append([-lit for lit in solution[:-1]])
    if verbosity > 0:
        print('\nNo counterexample found.')
    return None


def lift_solution(pol_arr,n,mat_dic,f=None,deterministic=True):
    r"""

    Input:
        - ``pol_arr`` -- array of polynomials
        - ``f`` -- a polynomial
        - ``n`` -- natural number
        - ``mat_dic`` -- matrices mod 2^n
        - ``deterministic`` -- boolean variable

    Output:
        Henself lifted matrix dic to 2^n+1
        
    Example:
        sage: A.<x,y> = FreeAlgebra(QQ)
        sage: Assumptions = [x*y]
        sage: f = x
        sage: Q = Quiver([('U','V',x), ('V','U',y)])
        sage: Dictionary = {'U': 2,'V': 2}
        sage: initial_solution = {'x': Matrix([[1, 1],[1, 1]]),'y': Matrix([[1, 1],[1, 1]])}
        sage: lift_solution(Assumptions,f,1,initial_solution,False)
    """
    #set_random_seed(99)
    #s = time.process_time()


    b_matrices = {}
    a_matrices1 = {}
    a_matrices = {}
    all_var = []

    for i, (key, mat) in enumerate(mat_dic.items()):
        var_name = f"b{i}"
        variable = var(var_name)
        M = create_symbolic_matrix(variable, mat.nrows(), mat.ncols())

        b_matrices[var_name] = M
        a_matrices1[key] = mat + 2**n * M
        all_var.extend(M.list())

    modulo = 2**(n+1)
    a_matrices.update({**a_matrices1, **{f"{k}_adj": v.transpose() for k, v in a_matrices1.items()}})
    # Use list comprehension for constructing matrix_array
    matrix_array = [poly_with_matrices(p, a_matrices) for p in pol_arr]
    flattend = [element for matrix in matrix_array for row in matrix for element in row]

    R1 = PolynomialRing(Integers(modulo), names=all_var)
    R2 = PolynomialRing(Integers(2), names=all_var, order='lex')
    R3 = PolynomialRing(ZZ, names=all_var)
    
    power = 2**n
    if f is not None:
        f_matrix = poly_with_matrices(f,a_matrices)

    mat_arr1 = []
    mat_arr2 = []
    for_vars = 0
    for mat in matrix_array:
        mat = mat.change_ring(R1)
        mat = mat.change_ring(R3)
        mat = mat / power
        mat = mat.change_ring(R2)
        mat_iter = [entry for row in mat.rows() for entry in row]
        mat_arr2.extend(mat_iter) 

    mat_arr1 = list(set(mat_arr2))

    C,m = Sequence(mat_arr1).coefficients_monomials()

    variables_in_solve_system = [var for var in m if var != 1]
    is_1 = any(var == 1 for var in m)

    if is_1:
        b = C[:, -1]              # RHS vector
        C = C[:, :-1]             # Coefficient matrix
        b = vector(R2, list(b))   # Convert to vector over GF(2)

        try:
            particular_sol = C.solve_right(b)
        except ValueError as e:
            raise ArithmeticError(f"Invalid arithmetic input: {e}")


    basis = C.right_kernel().basis()
    possible_solutions = basis.copy()
    if not is_1:
        zero_vec = vector(GF(2), [0]*C.ncols())
        possible_solutions = [zero_vec] + basis
    if is_1:
        possible_solutions = [tuple(a + b for a, b in zip(vec, particular_sol))for vec in possible_solutions]
    # Flatten f_matrix
    if f is not None:
        f_matrix = f_matrix.list()  # Faster and cleaner
    # Find variables NOT in the solved system
    unused_vars = list(all_var)
    for item in variables_in_solve_system:
        unused_vars.remove(SR(str(item)))
    # Convert them to R2 elements and map to 0
    dic_vars_not_in_sys = {R2(v): 0 for v in unused_vars}

    # Initialize variables (zipped and exit_loop used later)
    zipped = {}
    exit_loop = False
    if len(possible_solutions) == 0:
         raise ArithmeticError('No solution for this Lifting')
    if not deterministic:
    # Move random solution to front
        rand = randint(0, len(possible_solutions)-1)
        possible_solutions[0], possible_solutions[rand] = possible_solutions[rand], possible_solutions[0]

    for sol in possible_solutions:
        # Build substitution map
        zipped = {var: val for var, val in zip(variables_in_solve_system, sol)}
        zipped.update(dic_vars_not_in_sys)

        # Evaluate all polynomials in f_matrix
        if f is not None:
            for p in f_matrix:
                g = p
                variables = p.variables()
                for v in variables:
                    g = g.subs(SR(str(v)) == int(str(zipped[R2(v)])))

                value = int(str(g)) % modulo
                if value != 0:
                    exit_loop = True
        if exit_loop or f is None:
            break
        # Merge solution with default zeros
    zipped = dict(zip(variables_in_solve_system, possible_solutions[0]))
    zipped.update(dic_vars_not_in_sys)

    # Convert to a string-keyed dict with 0/1 values
    zipped1 = {str(k): int(v == 1) for k, v in zipped.items()}

    if exit_loop or f is None:
        for i, val in enumerate(mat_dic.values()):
            rows, cols = val.nrows(), val.ncols()
            for j in range(rows):
                for k in range(cols):
                    key = f"b{i}_{j+1}_{k+1}"
                    val[j, k] += 2**n * zipped1.get(key, 0)

        return mat_dic
    
    
def multi_lift_solution(pol_arr, m, mat_dic,f=None, deterministic=True):
    r"""
    Input:
        - ``pol_arr`` -- array of polynomials
        - ``f`` -- a polynomial
        - ``m`` -- natural number
        - ``mat_dic`` -- matrices mod 2^n
        - ``deterministic`` -- boolean variable

    Output:
        Hensel lifted matrix dic to 2^m

    Example:
        sage: A.<x,y> = FreeAlgebra(QQ)
        sage: Assumptions = [x*y]
        sage: f = x
        sage: Q = Quiver([('U','V',x), ('V','U',y)])
        sage: Dictionary = {'U': 2,'V': 2}
        sage: initial_solution = {'x': Matrix([[1, 1],[1, 1]]),'y': Matrix([[1, 1],[1, 1]])}
        sage: multi_lift_solution(Assumptions,f,4,initial_solution,True)
    """
    if check_counterexample(pol_arr, mat_dic,[f]):
        return mat_dic
    modulus = 2 ** m
    lift = mat_dic
    for i in range(1, m):
        lift = lift_solution(pol_arr, i, lift,f, deterministic)

    #Rational Reconstruction
    return {
        key: Matrix(QQ, [
            [rational_reconstruction(matrix[i, j], modulus) for j in range(matrix.ncols())]
            for i in range(matrix.nrows())
        ])
        for key, matrix in lift.items()
    }


def check_counterexample(assumptions, dictionary,claims=None, Q=None,transpose_in=False):
    r"""
    Input:
        - ``assumptions`` -- a list of polynomials
        - ``claims`` -- another list of polynomials
        - ``dictionary`` -- a solution to the system
        - ``Q`` -- a Quiver

    Output:
        True if the solution fulfills system else error

    Example:
        sage: A.<x,y> = FreeAlgebra(QQ)
        sage: assumptions = [x*y]
        sage: claims = [x]
        sage: Q = Quiver([('U','V',x), ('V','U',y)])

        # Case 1: False
        sage: dictionary_false = {
        ....:     'x': Matrix([[0, 0],[0, 0]]),
        ....:     'y': Matrix([[1, 1],[1, 1]])
        ....: }
        sage: print(check_counterexample(assumptions, claims, dictionary_false, Q))


        # Case 2: True
        sage: dictionary_true = {
        ....:     'x': Matrix([[1, 0],[0, 0]]),
        ....:     'y': Matrix([[0, 0],[0, 0]])
        ....: }
        sage: print(check_counterexample(assumptions, claims, dictionary_true, Q))
    """
    if claims is None:
        if Q is None:
            Q, _ = generate_quiver_dict(assumptions)
    if claims is not None:
        if Q is None:
            Q, _ = generate_quiver_dict(assumptions,claims)
    # Compatibility check for all polynomials
    for p in assumptions:
        if not Q.is_compatible(p):
                raise ValueError(f"{p} is not compatible with the quiver")

    if claims != None:
        for p in claims:
            if not Q.is_compatible(p):
                raise ValueError(f"{p} is not compatible with the quiver")
    

    # Build extended dictionary with transposes
    dictionary_full = {
        **dictionary,
        **{f"{key}_adj": val.transpose() for key, val in dictionary.items()}
    }

    # Check assumptions: all must be zero
    if any(not poly_with_matrices(p, dictionary_full).is_zero() for p in assumptions):
        return False
    if claims == None:
        return True

    # Check claims: if any is not zero, return True (counterexample)
    if claims != None:
        if any(not poly_with_matrices(p, dictionary_full).is_zero() for p in claims):
            return True

    return False



def groebner_test(equations):
    r"""
    Input:
        - ``equations`` -- list of polynomials

   Output:
       - Degrevlex gröbnerbasis of the polynomials

   Example:

        sage: L1.<x,y,z> = FreeAlgebra(QQ)
        sage: equations = [x^2 + y^2 - 1, x*y + 2]
        sage: groebner_test(equations)

   """
    s = time.process_time()
    var = set()
    for p in equations:
        var.update(p.variables())
    var = list(var)
    eqs = []
    Ring = PolynomialRing(QQ,names = var,order = 'degrevlex')
    i = 0
    for e in equations:
        eqs.append(Ring(e))
        i = i+1
    
    I = Ring.ideal(eqs)
    G = I.groebner_basis(algorithm = 'singular:slimgb')
    return G



def generate_poly_system(assumptions,claims=None,Q=None,dimensions=None):
    r"""
    Input:
        - ``assumptions`` -- Assumptions
        - ``f`` -- a polynom
        - ``Q`` -- a Quiver
        - ``dimensions`` -- a dictionary of matrix sizes

    Output:
        - polynomials that for the system to solve
    
    Example:
        sage: L.<x,y> = FreeAlgebra(QQ)
        sage: assumptions = [x*y]
        sage: Q = Quiver([('U','U',x), ('U','U',y)])
        sage: dimensions = {'U': 2}
        sage: claims = [x]
        sage: generate_poly_system(assumptions,claims,Q,dictionary)
    """
    s = time.process_time()
    claim = []
    if claims != None:
        claim.append(claims[0])
    else:
        claims = []
    if Q == None:
        Q,dictionary = generate_quiver_dict(assumptions,claims)
    assumptions,claims,Q,mapping = process_free_algebra_elements(assumptions ,claims, Q)
    for g in assumptions+claims: 
        if not Q.is_compatible(g):
            raise ValueError(str(g),   "is not compatible with the quiver")
    claim = []
    print(time.process_time()-s)
    if len(claims) >= 1:
        claim.append(claims[0])
    matrices = []
    symbolic_matrices = []
    for p in assumptions:
        matrix_sizes = []
        for v in p.variables():
            matrix_sizes.append([dimensions[Q.target(str(v))[0]],dimensions[Q.source(str(v))[0]]])
        matrix, matrix_list = poly_to_matrix(p,matrix_sizes)
        for m in matrix_list.values():
            if m not in symbolic_matrices:
                symbolic_matrices.append(m)
        matrix = [element for row in matrix.rows() for element in row]
        matrices.append(matrix)
    matrix_sizes = []
    matrices = [element for sublist in matrices for element in sublist]
    print(time.process_time()-s)
    if len(claims) >= 1:
        for p in claim:
            products = []
            for v in p.variables():
                matrix_sizes.append([dimensions[Q.target(str(v))[0]],dimensions[Q.source(str(v))[0]]])
            f_matrix, matrix_list = poly_to_matrix(p,matrix_sizes)
            for m in matrix_list.values():
                    if m not in symbolic_matrices:
                        symbolic_matrices.append(m)
            f_matrix = [element for row in f_matrix.rows() for element in row]
            for i in range(len(f_matrix)):
                products.append(1 - f_matrix[i])
            res,liste = tseytin(products)
            liste.append(res)
            matrices.extend(liste)
    print(time.process_time()-s)
    matrices = [x for x in matrices if x != 0]
    matrices = reverse_symbolic_polynomials(matrices, mapping)
    all_vars = list(set().union(*(p.variables() for p in matrices)))
    all_vars = [str(var) for var in all_vars]
    new_ring = FreeAlgebra(QQ, names=all_vars)
    matrices = [new_ring(str(p)) for p in matrices]
    return matrices


import re

def get_zeros(assumptions,fixed_matrix_name = "a", max_zeros=10, min_dim=2, max_dim=5, fix_type=0,lift_exp=2,deterministic=False,lift_tries=4):
    r"""
    Generate a list of quadratic boolean matrix zeros from a set of assumptions.

    Input:
        ``assumptions`` (list): List of polynomial assumptions.
        ``fixed_matrix_name`` (string): Matrix name we want to apply fix for (default "a")
        ``max_zeros`` (int, optional): Maximum number of zeros to return (default 10).
        ``min_dim`` (int, optional): Minimum matrix dimension to consider (default 2).
        ``max_dim`` (int, optional): Maximum matrix dimension to consider (default 5).
        ``fix_type`` (int, optional): Controls constraints on fixed matrix `fixed_matrix_name`:
            0 = no fixed ones,
            1 = at least one 1 per row,
            2 = at least one 1 per row and per column (default 0).
        ``lift_exp`` (int, optional): Exponent for lifting; actual lifting power is 2**lift_exp (default 2).
        ``deterministic`` (bool, optional): If True, use deterministic lifting (default False).
        ``lift_tries`` (int, optional): Number of attempts to lift each candidate solution (default 4).

    Returns:
        ``list``: List of dictionaries representing matrix zeros.

    Example:
        sage: L.<x,y> = FreeAlgebra(QQ)
        sage: assumptions = [x*x]
        sage: get_zeros(assumptions, max_zeros=2, max_dim=2, fix_type=1, lift_exp=3)
    """
    dim = min_dim
    all_vars = set()
    for elem in assumptions:
        all_vars.update(str(var) for var in elem.variables())

    all_matrices = []
    symbolic_matrices = {}
    Q, dictionary = generate_quiver_dict(assumptions)

    while dim <= max_dim:
        if dim >= 3:
            dictionary = generate_quiver_dict(assumptions, dim=dim)[1]

        matrices = []
        for p in assumptions:
            matrix_sizes = []
            for v in p.variables():
                matrix_sizes.append([dictionary[Q.target(str(v))[0]], dictionary[Q.source(str(v))[0]]])
            matrix, matrix_list = poly_to_matrix(p, matrix_sizes)
            for key, m in matrix_list.items():
                if m not in symbolic_matrices.values():
                    symbolic_matrices[key] = m
            matrix_flat = [element for row in matrix.rows() for element in row]
            matrices.append(matrix_flat)

        to_solve = [element for sublist in matrices for element in sublist]

        try:
            sat_dict, encoder, solution, cnf, all_polys, assignment = solve_system(to_solve)
        except TypeError:
            dim += 1
            continue

        fixed_matrix_name = "a"

        if fix_type > 0:
            a_entries_row = {}
            a_entries_col = {}

            for i, var in enumerate(encoder.phi[1:], start=1):
                name = str(var)
                if name.startswith(fixed_matrix_name + "_"):
                    m = re.match(rf"{fixed_matrix_name}_(\d+)_(\d+)", name)
                    if m:
                        row = int(m.group(1))
                        col = int(m.group(2))
                        if fix_type >= 1:
                            a_entries_row.setdefault(row, []).append(i)
                        if fix_type >= 2:
                            a_entries_col.setdefault(col, []).append(i)

            # Add CNF clauses
            if fix_type >= 1:
                for row, lits in a_entries_row.items():
                    if lits:
                        cnf.append(lits)

            if fix_type >= 2:
                for col, lits in a_entries_col.items():
                    if lits:
                        cnf.append(lits)

        # Solve repeatedly with run_cadical_with_cnf
        while True:
            solution = run_cadical_with_cnf(cnf)
            if solution is None:
                break

            # Build sat_dict from literals
            list_of_vars = encoder.phi[1:]
            sat_dict = {}
            for i in range(len(list_of_vars)):
                if list_of_vars[i] is not None and list_of_vars[i].degree() == 1:
                    sat_dict[str(list_of_vars[i])] = 1 if solution[i] > 0 else 0

            mats = get_matrices(sat_dict, all_vars, dim)
            if lift_exp == 2:
                if fix_type >= 3:
                    try:
                        one_sol_dict = one_lifting(assumptions,mats,idempotent=1)
                        if check_counterexample(assumptions, one_sol_dict, Q=None):
                            all_matrices.append(one_sol_dict)
                    except Exception as e:
                            pass
                else:
                    try:
                        one_sol_dict = one_lifting(assumptions,mats,idempotent=0)
                        if check_counterexample(assumptions, one_sol_dict, Q=None):
                            all_matrices.append(one_sol_dict)
                    except Exception as e:
                            pass
            else:
                for _ in range(lift_tries):
                    try:
                        one_sol_dict = multi_lift_solution(assumptions, lift_exp, mats, deterministic=False)
                        if check_counterexample(assumptions, one_sol_dict, Q=None):
                            all_matrices.append(one_sol_dict)
                            break
                    except Exception as e:
                        pass

            # Exclude current model
            exclude_clause = [-lit for lit in solution if lit != 0]
            cnf.append(exclude_clause)

            if len(all_matrices) >= max_zeros:
                # Pretty-print solutions before returning
                print(f"\n=== Found {len(all_matrices)} zero solutions ===")
                for idx, sol in enumerate(all_matrices):
                    print(f"\n--- Solution #{idx+1} ---")
                    for key, matrix in sol.items():
                        if key.endswith("_adj"):
                            continue
                        print(f"{key} =")
                        print(matrix)
                return all_matrices

        dim += 1

    # Pretty-print solutions before returning
    print(f"\n=== Found {len(all_matrices)} zero solutions ===")
    for idx, sol in enumerate(all_matrices):
        print(f"\n--- Solution #{idx+1} ---")
        for key, matrix in sol.items():
            if key.endswith("_adj"):
                continue
            print(f"{key} =")
            print(matrix)

    return all_matrices

def commutative_solution(commutative_polys, n=2):
    """
    Solve a commutative polynomial system using Cadical SAT solver,
    then perform Hensel lifting and rational reconstruction.

    INPUT:
        commutative_polys : list of commutative polynomials
        n                 : lifting power (mod 2^n)

    OUTPUT:
        rational_sol      : dictionary of rational solutions if certified
    """

    # Step 1: Get variable names from the polynomial ring
    varnames = commutative_polys[0].parent().variable_names()

    # Step 2: Solve the system modulo 2 (SAT-based approach)
    solve_out = solve_system(commutative_polys)
    sat_dict = solve_out[0]
    cnf = solve_out[3]
    current_solution = solve_out[2]
    print(current_solution)  # debug: see the initial SAT solution
    print(sat_dict)

    # Step 3: Build a full SAT solution including all variables
    # If a variable is missing in the SAT solution, assign 0
    full_sat_sol = {v: sat_dict.get(v, 0) for v in varnames}

    # Step 4: Perform multi-Hensel lifting and rational reconstruction
    rational_sol = None
    cert = False
    try:
        rational_sol = multi_hensel_lift_commutative(commutative_polys, full_sat_sol, n)
    except ArithmeticError:
        pass
    # Step 5: Certify the rational solution by checking it satisfies the original system
    if rational_sol != None:
        cert = certify_rational_lift(commutative_polys, rational_sol)

    # Step 6: Return the rational solution if certification passed
    if cert == True:
        return rational_sol


    while current_solution != None:
        cnf.append([-lit for lit in current_solution[:-1]])
        current_solution = run_cadical_with_cnf(cnf)
        if current_solution is None:
            return None
        full_sat_sol = build_full_sat_sol(varnames, current_solution)
        try:
            rational_sol = multi_hensel_lift_commutative(commutative_polys, full_sat_sol, n)
        except ArithmeticError:
            continue
        cert = certify_rational_lift(commutative_polys, rational_sol)

        if cert:
            return rational_sol
def multi_hensel_lift_commutative(polys, sat_sol, lift_power=4):
    """
    Multi-Hensel lift a commutative polynomial system from an integer SAT solution.

    INPUT:
        polys: list of commutative polynomials in a PolynomialRing
        sat_sol: dict mapping variable names (strings) to integer SAT solution
        lift_power: lift modulo 2^lift_power

    OUTPUT:
        lifted_sol: dict of lifted integer solutions modulo 2^lift_power
        rational_sol: dict of rational solutions after reconstruction
    """
    if not polys:
        raise ValueError("Polynomial system is empty.")

    # Step 1: Extract generators from the polynomial ring
    R = polys[0].parent()
    all_vars = list(R.gens())
    n_vars = len(all_vars)
    modulo = 2**lift_power

    # Step 2: Initial solution vector modulo 2 (Booleans from SAT)
    x_curr = vector([1 if sat_sol.get(str(v), 0) > 0 else 0 for v in all_vars])

    # Step 3: Hensel lifting loop
    for k in range(1, lift_power + 1):
        modk = 2**k

        # Build substitution dict for current solution
        subs_dict = {v: int(x) for v, x in zip(all_vars, x_curr)}

        # Compute residuals scaled by 2^(k-1) modulo 2
        residuals_mod2 = vector(GF(2), [
            ((int(p.subs(subs_dict)) // 2**(k-1)) % 2) for p in polys
        ])

        # Build Jacobian modulo 2
        J_rows = []
        for p in polys:
            row = [(int(diff(p, v).subs(subs_dict)) % 2) for v in all_vars]
            J_rows.append(row)
        J = Matrix(GF(2), J_rows)

        # Solve J * delta = residuals_mod2 modulo 2
        try:
            delta = J.solve_right(residuals_mod2)
        except ValueError:
            # fallback if singular: set corrections to 0
            delta = vector([0]*n_vars)

        # Update current solution modulo 2^k
        x_curr = vector([
            (int(val) + 2**(k-1) * int(d)) % modk for val, d in zip(x_curr, delta)
        ])

    # Step 4: Build lifted integer solution dictionary
    lifted_sol = {str(v): int(val) for v, val in zip(all_vars, x_curr)}

    # Step 5: Rational reconstruction for each variable
    rational_sol = {str(v): rational_reconstruction(int(val), modulo) for v, val in zip(all_vars, x_curr)}

    return rational_sol

def certify_rational_lift(polys, rational_sol):
    """
    Certify that a lifted solution over Q satisfies a commutative polynomial system.
    Exact check: no floating tolerance used.

    INPUT:
        polys        : list of commutative polynomials over QQ
        rational_sol : dict {var_name: rational-like} representing the solution
                       values may be QQ, Rational, int, or floats (floats will be
                       converted to exact rationals via QQ()).

    OUTPUT:
        True if all polynomials are exactly zero at the solution, False otherwise.
    """
    success = True
    R = polys[0].parent()   # polynomial ring
    all_vars = list(R.gens())

    # Build substitution dict using generator objects; convert values to QQ
    subs_rational = {}
    for v in all_vars:
        key1 = str(v)
        # allow either string keys or generator keys in rational_sol
        val = rational_sol.get(key1, rational_sol.get(v, 0))
        # Convert to exact rational in QQ. If already QQ/Rational/int, QQ(...) will preserve it.
        subs_rational[v] = QQ(val)

    for i, p in enumerate(polys):
        val = p.subs(subs_rational)   # should be exact QQ element
        # exact zero check
        if val != 0:
            print(f"Polynomial {i} failed: {p} -> {val}")
            success = False

    if success:
        print("All polynomials satisfied by the rational solution.")
    return success


def one_lifting(pol_arr, mat_dic, f=None,verbosity=0,idempotent=0):
    r"""
    Hensel lift a matrix solution for a system of polynomial equations.

    Input:
        - pol_arr -- list of polynomials (assumptions)
        - f       -- a polynomial (claim)
        - mat_dic -- dictionary of matrices modulo 2^n

    Output:
        Dictionary of lifted matrices modulo 2^(n+1)
    """
    start_time = time.process_time()
    # Initialize symbolic matrices for lifting
    b_matrices = {}      # stores the symbolic matrices
    a_matrices1 = {}     # stores mat + 2*M
    a_matrices = {}      # will include transposes as well
    all_var = []         # list of all symbolic variables

    for i, (key, mat) in enumerate(mat_dic.items()):
        rows, cols = mat.nrows(), mat.ncols()
        var_name = f"b{i}"

        bump_entries = []
        bump_vars = []
        for r in range(rows):
            row_vars = []
            for c in range(cols):
                if mat[r, c] % 2 == 1:  # only introduce a bump variable if entry is 1 mod 2
                    v = var(f"{var_name}_{r+1}_{c+1}")
                    row_vars.append(v)
                    bump_vars.append(v)
                else:
                    row_vars.append(0)  # fixed zero, no variable
            bump_entries.append(row_vars)

        M = matrix(bump_entries)
        b_matrices[var_name] = M
        a_matrices1[key] = mat + 2 * M
        all_var += bump_vars  # only the variables you actually created
    # Construct matrix dictionary including transposes
    modulo = 4
    a_matrices.update({**a_matrices1, **{f"{k}_adj": v.transpose() for k, v in a_matrices1.items()}})
    # Evaluate polynomials with symbolic matrices
    matrix_array = [poly_with_matrices(p, a_matrices) for p in pol_arr]

    # Polynomial rings for modular arithmetic
    R2 = PolynomialRing(Integers(2), names=all_var, order='lex')
    R3 = PolynomialRing(ZZ, names=all_var)
    power = 2
    if f is not None:
        f_matrix = poly_with_matrices(f, a_matrices)

    # Flatten matrices and change rings for modular computation
    mat_arr2 = []
    for mat in matrix_array:
        mat = (mat.change_ring(R3) / power).change_ring(R2)
        mat_arr2.extend(mat.list())
    # deduplicate
    seen = set()
    mat_arr1 = []
    for item in mat_arr2:
        if item not in seen:
            mat_arr1.append(item)
            seen.add(item)
    C, m = Sequence(mat_arr1).coefficients_monomials()

    # Identify variables involved in system
    variables_in_solve_system = [var for var in m if var != 1]
    is_1 = 1 in m
    # Solve linear system modulo 2
    if is_1:
        b = vector(R2, list(C[:, -1]))  # RHS vector
        C = C[:, :-1]                   # coefficient matrix
        try:
            particular_sol = C.solve_right(b)
        except ValueError as exp:
            raise ArithmeticError(f"Invalid arithmetic input: {exp}")

    # Compute kernel for free variables
    basis = C.right_kernel().basis()
    possible_solutions = basis
    if is_1:
        possible_solutions = [vec + particular_sol for vec in basis]

    # Flatten claim polynomial matrix for substitution
    if f is not None:
        f_matrix = f_matrix.list()

    # Identify variables not in solved system
    unused_vars = list(all_var)
    for item in variables_in_solve_system:
        unused_vars.remove(SR(str(item)))  # remove solved variables

    # Map unused variables to zero
    dic_vars_not_in_sys = {str(v): 0 for v in unused_vars}

    if not possible_solutions:
        raise ArithmeticError('No solution for this Lifting')

    # Compute all solutions in the span
    solutions = solutions_in_span(possible_solutions, mat_arr1, variables_in_solve_system)
    # Convert solution vectors to dictionaries
    solutions_dicts = [
        {str(var): int(val) for var, val in zip(variables_in_solve_system, v)}
        for v in solutions
    ]
    # Filter solutions that satisfy the claim polynomial f
    if f is not None:
        solutions_fullfill_f = []
        for sol in solutions_dicts:
            sol.update(dic_vars_not_in_sys)                     # add unused vars as 0
            subs_dict = {SR(str(k)): v for k, v in sol.items()}  # create substitution dict
            for p in f_matrix:
                g = p.subs(subs_dict)                            # substitute all variables
                value = int(str(g)) % modulo
                if value != 0:
                    solutions_fullfill_f.append(sol)
                    break
        if solutions_fullfill_f and all(v == 0 for v in solutions_fullfill_f[0].values()):
            del solutions_fullfill_f[0]  # Remove the trivial all-zero solution
    else:
        for sol in solutions_dicts:
            sol.update(dic_vars_not_in_sys)
        solutions_fullfill_f = solutions_dicts
    # Construct lifted matrices for each solution
    #if verbosity >= 1:
        #print(f'We have {len(solutions_fullfill_f)} of {len(solutions)} solutions that work')
    for sol in solutions_fullfill_f:
        val_mat = []

        for i, val in enumerate(mat_dic.values()):
            val_copy = matrix(val)
            rows, cols = val_copy.nrows(), val_copy.ncols()

            bump = matrix([[2 * sol.get(f"b{i}_{r+1}_{c+1}", 0)
                             for c in range(cols)] for r in range(rows)])
            val_copy += bump
            val_mat.append(val_copy)

        # Replace 3 by -1
        for mat in val_mat:
            rows, cols = mat.nrows(), mat.ncols()
            for i in range(rows):
                for j in range(cols):
                    if mat[i, j] == 3:
                        mat[i, j] = -1

        # Build candidate dictionary
        candidate = {k: val_mat[i] for i, k in enumerate(mat_dic.keys())}
        def is_idempotent(candidate, fixed_matrix_name="a"):
            A = candidate[fixed_matrix_name]
            return A * A == A
        if idempotent:
            if check_counterexample(pol_arr, candidate) and not is_idempotent(candidate, "a"):
                last_dict = candidate
                break
        else:
            if check_counterexample(pol_arr, candidate):
                last_dict = candidate
                break

    # If none worked, raise an error
    if 'last_dict' not in locals():
        raise ArithmeticError("No valid lifted solution found.")

    return last_dict

def many_sat(pol_arr, claim,Q,dictionary,how_many=10):
    assumptions1, claims1, Q1, mapping = process_free_algebra_elements(pol_arr, claim, Q)
    outputs = first_sat_solution(assumptions1,claims1[0], Q1, dictionary)
    sat_solution = outputs[0]
    cnf = outputs[5]
    e =outputs[3]
    symbolic_matrices = outputs[1]
    solution = outputs[4]
    def extract_sat_dict(model, vars_list):
        return {
            str(var): model[i]
            for i, var in enumerate(vars_list)
            if var != None and var.degree() == 1
        }
    def build_matrix_model(model, symbolic_matrices, sat_dict):
        result = {}
        for key, m in symbolic_matrices.items():
            if '_' not in key:  # skip adjoints
                rows, cols = m.nrows(), m.ncols()
                m_copy = zero_matrix(rows, cols)
                for i in range(rows):
                    for j in range(cols):
                        var_name = str(m[i][j])
                        if sat_dict.get(var_name, 0) > 0:
                            m_copy[i, j] = 1
                result[key] = m_copy
        return {k: v for k, v in result.items() if not k.startswith('k')}
    for i in range(how_many):
        try:
            real_sol = one_lifting(assumptions1,claims1[0],sat_solution)
        except ArithmeticError:
            print('No Solution for this one')
        cnf.append([-lit for lit in solution[:]])
        solution=run_cadical_with_cnf(cnf)
        if solution is None:
            break
        sat_dict = extract_sat_dict(solution, e.phi[1:])
        sat_solution = build_matrix_model(solution, symbolic_matrices, sat_dict)
        print(sat_solution)
