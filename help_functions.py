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
from .functions import *
from itertools import product
from sage.all import GF, vector



#takes the variable name, rows and cols and returns a mastrix of the given size where variables name depens on the input name
def create_symbolic_matrix(name, rows, cols):
    r"""
    Input:
        - ``name`` -- the variable name
        - ``rows`` -- number of rows
        - ``cols`` -- number of columns

    Output: a matrix of the given size where variables name depends on the input name

    Example:
        sage: A.<x,y,x_adj> = FreeAlgebra(QQ)
        sage: m = create_symbolic_matrix(x, 2, 2)
        sage: n= create_symbolic_matrix(y, 2, 2)
        sage: j = create_symbolic_matrix(x_adj, 2, 2)
        sage: print([m,n,j])
    """
    #Create a symbolic matrix with entries named as name[i][j].
    if "_" in str(name):
        parts = str(name).split("_")
        variable = SR(parts[0])
        mat =  Matrix(SR, rows, cols, lambda i, j: var(f"{variable}_{i+1}_{j+1}"))
        return mat.transpose()
    else:
        return Matrix(SR, rows, cols, lambda i, j: var(f"{name}_{i+1}_{j+1}"))

def substitute_matrices(mon, matrix_list):
    r"""
    Input:
        - ``mon`` -- a monomial
        - ``matrix_list`` -- matrix for each variable

    Output:
        result of multiplication of the matrices considering the monomial

    Example:
        sage: A.<x,y,z> = FreeAlgebra(QQ)
        sage: poly = x*y
        sage: substitute_matrices(poly,{str(x) : create_symbolic_matrix(x, 4 ,2),str(y) : create_symbolic_matrix(y, 2 ,4)})
    """
    # Convert monomial to list of variables
    extended_monomial = list(mon.leading_support())
    # Get the list of matrices to multiply
    list_to_multiply = [matrix_list[str(v[0])] for v in extended_monomial]

    # Multiply matrices
    if not list_to_multiply:
        raise ValueError("Monomial is empty.")
    result = list_to_multiply[0]
    for mat in list_to_multiply[1:]:
        result *= mat

    return result
def substitute_matrices1(mon, matrix_list):
    r"""
    Input:
        - ``mon`` -- a monomial
        - ``matrix_list`` -- matrix for each variable

    Output:
        result of multiplication of the matrices considering the monomial

    Example:
        sage: A.<x,y,z> = FreeAlgebra(QQ)
        sage: poly = x*y
        sage: substitute_matrices(poly,{str(x) : create_symbolic_matrix(x, 4 ,2),str(y) : create_symbolic_matrix(y, 2 ,4)})
    """
    # Convert monomial to list of variables, expanding multiplicities
    support = mon.leading_support()
    extended_monomial = []
    for var, power in support:
        extended_monomial.extend([str(var)] * power)

    # Get the list of matrices to multiply
    list_to_multiply = [matrix_list[v] for v in extended_monomial]

    # Multiply matrices
    if not list_to_multiply:
        raise ValueError("Monomial is empty.")
    result = list_to_multiply[0]
    for mat in list_to_multiply[1:]:
        result *= mat

    return result

def process_free_algebra_elements(assumptions ,claims, quiver, replacement="UNDERSCORE"):
    r"""
    Process a list of free algebra elements by modifying variable names.
    
    Input:
        ``assumptions``: List of polynomials from a free algebra.
        ``claims``: another list
        ``quiver``: a Quiver
        ``replacement``: Replacement string for underscores. Default is "UNDERSCORE".
        
    Returns:
        modified assumptions, claims and quiver (getting rid of '_') and the replacement mapping
    """
    # Convert all elements to strings and collect variables
    all_vars = []
    quiver_dict = quiver.to_dict()
    for key in quiver_dict.keys():
        for tupel in quiver_dict[key]:
            all_vars.append(str(tupel[1]))
    # Create a mapping of variable names
    mapping = {}
    updated_vars = set()

    for var in all_vars:
        if "adj" in var:
            # Replace all underscores except the last one
            parts = var.rsplit("_", 1)
            new_var = parts[0].replace("_", replacement) + ("_" + parts[1] if len(parts) > 1 else "")
        else:
            # Replace all underscores normally
            new_var = var.replace("_", replacement)
        mapping[var] = new_var
        updated_vars.add(new_var)

    # Create a new free algebra ring with updated variable names
    updated_vars = sorted(updated_vars)  # Ensure consistent ordering
    new_ring = FreeAlgebra(QQ, names=updated_vars)

    # Replace variables in the original elements using the mapping
    updated_assumptions = []
    for elem in assumptions:
        updated_elem_str = str(elem)
        for old_var, new_var in mapping.items():
            updated_elem_str = updated_elem_str.replace(old_var, new_var)
        updated_assumptions.append(new_ring(updated_elem_str))
    
    updated_claims = []
    for elem in claims:
        updated_elem_str = str(elem)
        for old_var, new_var in mapping.items():
            updated_elem_str = updated_elem_str.replace(old_var, new_var)
        updated_claims.append(new_ring(updated_elem_str))
        
        
    updated_quiver = []
    for key in quiver_dict.keys():
        for tupel in quiver_dict[key]:
            updated_quiver.append((key,tupel[0],new_ring(mapping[str(tupel[1])])))

    return updated_assumptions,updated_claims, Quiver(updated_quiver), mapping

def generate_quiver_dict(assumptions,claims=[],quiver=None,dim=2):
    r"""
    Input:
        - ``assumptions`` -- list of polynomials
        - ``claims`` -- list of polynomials
        - ``quiver`` -- OPTIONAL: a quiver if only dictionary is needed
        - ``dim`` -- OPTIONAL: Dimension of dictionary
   Output:
       - Quiver and dicitonary

   Example:

        sage: A.<x,y> = FreeAlgebra(QQ)
        sage: Assumptions = [x*y]
        sage: f = x
        sage: Q = Quiver([('U', 'U', 'x'), ('U', 'U', 'y')])
        sage: generate_quiver_dict(Assumptions,[f],Q,dim=3)
   """
    if dim == 2:
        all_vars = set()
        elements = assumptions + claims
        for elem in elements:
            all_vars.update(str(var) for var in elem.variables())
        quiver = []
        quiver.extend([('U', 'U', var) for var in all_vars])
        quiver = Quiver(quiver)
        dictionary = {'U': 2}
    else:
        dictionary = {'U': dim}
    return quiver,dictionary

def poly_to_matrix(p, matrix_sizes):
    r"""
    Input:
        - ``p`` -- a polynomial
        - ``matrix_sizes`` -- list [[n,m],[],..] of matrix sizes for each variable

    Output:
        Resulting matrix when you plug them into the polynomial

    Example:
        sage: A.<x,y,z> = FreeAlgebra(QQ)
        sage: matrix,matrix_list = poly_to_matrix(z+y+1,[[2,2],[2,2]]) 
    """
    # creates symbolic matrices for each variable
    var = p.variables()
    matrix_list = {str(var[i]): create_symbolic_matrix(var[i], matrix_sizes[i][0], matrix_sizes[i][1])
                   for i in range(len(var))}
    # iterates through monomials and returns result of multiplication of matrices for each monomial
    monomials_list = p.monomials()
    const = 1 in monomials_list

    if const:
        monomials = [m for m in monomials if m != 1]

    matrix_monomials = [substitute_matrices1(mon, matrix_list) for mon in monomials_list]

    # Adds all solutions up with coefficients
    terms = p.terms()
    for i in range(len(matrix_monomials)):
        matrix_monomials[i] = terms[i].coefficients()[0] * matrix_monomials[i]

    # Combine monomial matrices into a single solution
    if matrix_monomials:
        solution = sum(matrix_monomials)
    else:
        solution = None  # might be constant-only

    # If const in polynomial we have to add an identity matrix
    if const:
        coefficient_list = p.coefficients()
        c = coefficient_list[0]
        if solution is None:
            size = matrix_sizes[0][0]
            solution = c * identity_matrix(size)
        else:
            if solution.nrows() != solution.ncols():
                raise ValueError("Calculation not possible")
            solution += c * identity_matrix(solution.nrows())

    return solution, matrix_list

def poly_with_matrices(p, matrix_dict):
    r"""
    Input:
        - ``p`` -- a polynomial
        - ``matrix_dict`` -- a dictionary with matrices for each variable of the polynomial p (instead of dictionary of matrix sizes as in poly_to_matrix)

    Output:
        Resulting matrix when you plug them into the polynomial

    """

    matrix_list = matrix_dict
    monomials_list = p.monomials()
    const = False

    if monomials_list[len(monomials_list)-1] == 1:
        const = True
        monomials_list.remove(1)

    matrix_monomials= []
    for mon in monomials_list:
        matrix_monomials.append(substitute_matrices1(mon, matrix_list))

    terms = p.terms()
    for i in range(len(matrix_monomials)):
        matrix_monomials[i] = terms[i].coefficients()[0] * matrix_monomials[i]
    if len(matrix_monomials) == 1:
        solution = matrix_monomials[0]
    elif len(matrix_monomials) == 2:
        solution = matrix_monomials[0] +  matrix_monomials[1]
    else:
        solution = matrix_monomials[0] + matrix_monomials[1]
        for i in range(len(matrix_monomials) - 2):
            solution = solution + matrix_monomials[i+2]


    if const == True:
        if solution.nrows() != solution.ncols():
            raise ValueError("Calculation not possible")
        coefficient_list = p.coefficients()
        c = coefficient_list[0]
        solution =  solution + c * identity_matrix(solution.nrows())
    return solution


def reverse_mapping(dictionary,mapping):
    r"""
    Reverses the mapping we introduced
    """
    dict_reversed = {}
    mapping_rev =  {v: k for k, v in mapping.items()}
    for key in dictionary.keys():
        new_key = mapping_rev[str(key)]
        dict_reversed[new_key] = dictionary[key]
    return dict_reversed

def reverse_symbolic_polynomials(symbolic_elements, mapping):
    """
    Reverse the process of updating variable names in symbolic polynomials.
    
    Input:
        ``symbolic_elements`` (list): List of symbolic polynomials.
        ``mapping`` (dict): Dictionary of old variable names to new variable names.
        
    Returns:
        ``list``: List of symbolic polynomials in the original variable names.
    """
    # Reverse the mapping dictionary
    reverse_mapping = {new_var: old_var for old_var, new_var in mapping.items()}

    # Replace updated variable names with the original ones in each polynomial
    reverted_polynomials = []
    for poly in symbolic_elements:
        poly_str = str(poly)
        for new_var, old_var in reverse_mapping.items():
            poly_str = poly_str.replace(new_var, old_var)
        # Convert back to symbolic polynomial
        reverted_polynomials.append(SR(poly_str))

    return reverted_polynomials

def get_matrices(dictionary,variables,dim):
    """
    Convert a dictionary of SAT solver solutions into matrices.
    
    Input:
        ``dictionary`` (dict): Dictionary containing SAT solutions.
        ``var`` (list): List of variable names.
        ``dim`` (int): Dimension of the square matrices.
        
    Returns:
        ``dict``: Dictionary of matrices corresponding to the SAT solutions.
    """
    matrices = {str(var): MatrixSpace(ZZ, dim, dim)(0) for var in variables}
    # Fill the matrices
    for key, value in dictionary.items():
        parts = key.split('_')
        var, row, col = parts[0], int(parts[1]) - 1, int(parts[2]) - 1  # Convert to 0-based index

        # Assign 1 for True, 0 for False
        matrices[str(var)][row, col] = int(value)
        matrices[str(var)+'_adj'] =  matrices[str(var)].transpose()

    # Print results
    return matrices

def sat_check_counterexample(assumptions,claims,mod,dictionary,Q=None):
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
        sage: Assumptions = [x*y]
        sage: f = x
        sage: Q = Quiver([('U','V',x), ('V','U',y)])
        sage: Dictionary = {'U': 2,'V': 2}
        sage: possible_solution = multi_lift_solution(Assumptions,f,2,first_sat_solution(Assumptions,f,Q,Dictionary)[0],True)
        sage: check_counterexample(Assumptions,[f],possible_solution,Q)
    """
    if Q == None:
        Q,dictionary1 = generate_quiver_dict(assumptions,claims)
        
    for g in assumptions: 
        if not Q.is_compatible(g):
            raise ValueError(str(g),   "is not compatible with the quiver")
            
    for f in claims:
        if not Q.is_compatible(f):
               raise ValueError(str(f),  "is not compatible with the quiver")

    dictionary_full = {}
    for key,value in dictionary.items():
        dictionary_full[key] = value
        dictionary_full[str(key) + '_adj'] = value.transpose()
    
    for p in assumptions:
        if not (poly_with_matrices(p,dictionary_full)%mod).is_zero():
            return False
            
    for p in claims:
        if not (poly_with_matrices(p,dictionary_full)%mod).is_zero():
            return True
       
    return False

#Builds a concrete dictionary of binary matrices (0/1) from the symbolic matrices and the SAT variable assignment.
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
    
#extracts important variables and its solution values
def extract_sat_dict(model, vars_list):
    return {
        str(var): model[i]
        for i, var in enumerate(vars_list)
        if var != None and var.degree() == 1
    }

def build_full_sat_sol(varnames, model):
        sol = {}
        for i, var in enumerate(varnames):
            lit = i + 1
            if lit in model:
                sol[var] = 1
            elif -lit in model:
                sol[var] = 0
            else:
                sol[var] = 0
        return sol

def solutions_in_span(basis, polys,variables, field=GF(2)):
    """
    Find all linear combinations of basis vectors that satisfy a list of Sage polynomials.
    
    basis : list of Sage vectors over 'field'
    polys : list of Sage polynomials (from the same polynomial ring)
    field : default GF(2)
    
    Returns: list of tuples (coefficients, resulting vector)
    """
    n = len(basis)
    dim = len(basis[0]) if basis else 0
    
    solutions = []
    
    for coeffs in product(field, repeat=n):
        # form linear combination
        v = vector(field, [0]*dim)
        for c, b in zip(coeffs, basis):
            if c != 0:
                v += c*b
        
        # create dictionary mapping variables -> vector entries
        subs_dict = {var: val for var, val in zip(variables, v)}
        # check all polynomials
        if all(p.subs(subs_dict) == 0 for p in polys):
            #solutions.append((coeffs, v))
            solutions.append( v)
    
    return solutions
