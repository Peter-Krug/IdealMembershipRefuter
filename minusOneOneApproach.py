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

def substitute_and_simplify(polynomials):
    r"""
    substitute_and_simplify(polynomials)

    Given a list of multivariate polynomials, this function replaces each variable 
    with the difference of two new variables representing its positive and negative parts:
    ``x -> x_pos - x_neg``, ``y -> y_pos - y_neg``, etc.

    Input:
        - ``polynomials`` -- a list of polynomials over a rational field (QQ),
          assumed to be from the same parent ring.

    Output:
        - A list of new polynomials with the variables substituted using the 
          transformation: ``x → x_pos - x_neg``, and so on for all variables in the input.

    Example:
        sage: R.<x,y> = PolynomialRing(QQ)
        sage: f = x^2 + x*y + 1
        sage: substitute_and_simplify([f])
        [(x_pos - x_neg)^2 + (x_pos - x_neg)*(y_pos - y_neg) + 1]

    Note:
        The returned polynomials are in a new polynomial ring that includes all original
        variables and their `_pos` and `_neg` counterparts.
"""
    # Gather all variables used in the polynomials
    gens = polynomials[0].parent().gens()
    gens_str = [str(gen) for gen in gens]
    # Build substitution dictionary: x -> x_pos - x_neg
    subs_pos = [f"{var}_pos" for var in gens]
    subs_neg = [f"{var}_neg" for var in gens]
    
    Ring = PolynomialRing(QQ,names = gens_str + subs_pos + subs_neg)
    subs = {Ring(gens[i]): Ring(subs_pos[i]) - Ring(subs_neg[i]) for i in range(len(gens))}
    new_polys = [Ring(p) for p in polynomials]
    
    # Apply substitution and simplify
    simplified = [p.subs(subs) for p in new_polys]
    
    return simplified

def tseytin_substitution(polynomials):
    r"""
    tseytin_substitution(polynomials)

    Applies a Tseytin-style substitution to a list of polynomials by replacing 
    each monomial of total degree > 1 with a new auxiliary variable (e.g., j0, j1, ...).

    Input:
        - ``polynomials`` -- a list of polynomials over QQ (rational field), all from
          the same parent ring.

    Output:
        - A tuple ``(new_polynomials, mapping)``, where:
            * ``new_polynomials`` is a list of polynomials with higher-degree monomials
              replaced by fresh symbolic variables j0, j1, ...
            * ``mapping`` is a dictionary that maps each introduced j-variable (e.g. 'j0') 
              to the monomial it replaced (as a symbolic expression).

    Example:
        sage: R.<x, y> = PolynomialRing(QQ)
        sage: f = x^2 + x*y + y
        sage: new_polys, mapping = tseytin_substitution([f])
        sage: new_polys
        [j0 + j1 + y]
        sage: mapping
        {'j0': x^2, 'j1': x*y}

    Notes:
        - This substitution rewrites monomials of degree > 1, preserving linear structure.
        - The resulting polynomials are in a new ring including the original variables and
          all new j-variables.
        - The original-to-substitute monomial map is inverted before returning.
"""
    start = time.process_time()
    monomial_to_j = OrderedDict()                               # mapping: monomial -> k_i
    j_variables = []               # list of created k_i variables
    j_counter = 0                  # to keep naming consistent
    new_polynomials = []
    all_vars = polynomials[0].parent().gens()
    all_vars_str = [str(var) for var in all_vars]
    for poly in polynomials:
        poly_terms = []
        coeff= poly.coefficients()
        monomials = poly.monomials()
        for monomial in monomials:  # break the polynomial into terms
            if monomial.degree() > 1:
                if monomial not in monomial_to_j:
                    j_name = f'j{j_counter}'
                    monomial_to_j[monomial] = j_name
                    j_variables.append(j_name)
                    j_counter += 1
                    # substitute monomial with its corresponding j_i
    R = PolynomialRing(QQ,names = all_vars_str + j_variables)
    Ring = BooleanPolynomialRing(names = all_vars_str + j_variables)
    subs = {Ring(str(key)): Ring(str(val)) for key, val in monomial_to_j.items()}
    poly_list = []
    #effizienter als subs(), weil subs so riesig
    
    for poly in polynomials:
        monomials = poly.monomials()
        coeffs = poly.coefficients()
        terms = []

        for mon, coef in zip(monomials, coeffs):
            if mon.degree() > 1:
                term = f"{coef}*{subs[Ring(str(mon))]}"
            else:
                term = str(coef * mon)
            if coef > 0 and terms:
                term = '+' + term
            terms.append(term)

        p_str = ''.join(terms)
        poly_list.append(R(p_str))
    # Convert monomial->k_i map into k_i->monomial map as specified
    #j_to_monomial = {Ring(str(v)): Ring(str(j)) for j, v in monomial_to_j.items()}
    j_to_monomial = {v: j for j, v in subs.items()}
    return poly_list, j_to_monomial


def pb_enc(tseytin_polys, dictionary_vars_to_lits=None, n=1):
    r"""
    pb_enc(tseytin_polys, dictionary_vars_to_lits=None, n=1)

    Encodes a list of Tseytin-transformed polynomials into pseudo-Boolean (PB) constraints,
    and converts those constraints into CNF clauses using a PB-to-CNF encoder (e.g., PySAT's PBEnc).

    Input:
        - ``tseytin_polys`` -- a list of polynomials (usually the output of tseytin_substitution),
          assumed to be linear or pseudo-Boolean in form.
        - ``dictionary_vars_to_lits`` (optional) -- a dictionary mapping symbolic variables
          (from the polynomials) to integer literals used in CNF clauses. If not provided,
          a new mapping will be created starting from literal ``n``.
        - ``n`` (optional, default: 1) -- the starting literal index for variable-to-literal
          mapping if a dictionary is not supplied.

    Output:
        - A tuple ``(clauses, variable_map)``, where:
            * ``clauses`` is a list of lists of integers representing the CNF clauses generated
              from the pseudo-Boolean encodings.
            * ``variable_map`` is a dictionary mapping each symbolic variable to its assigned
              integer literal.

    Example:
        sage: R.<x, y> = PolynomialRing(QQ)
        sage: tseytin_polys, mapping = tseytin_substitution([x*y + x + y - 1])
        sage: clauses, var_map = pb_enc(tseytin_polys)

    Notes:
        - This function uses PySAT's PBEnc module to perform the encoding. Ensure PySAT is installed.
        - The function handles negative constant terms by flipping signs, as PBEnc expects inequalities
          of the form ``sum(coeffs * lits) == bound``.
        - The returned CNF clauses can be directly fed to SAT solvers like MiniSat, Glucose, or others.

"""
    start = time.process_time()
    
    if dictionary_vars_to_lits is None:
        dictionary_vars_to_lits = {}

    all_clauses = []
    all_vars_list = list(tseytin_polys[0].parent().gens())
    
    # Initialize variable mapping starting from n
    count = 0
    for var in all_vars_list:
        if var not in dictionary_vars_to_lits:
            dictionary_vars_to_lits[var] = n + count
            count += 1
    
    top = n
    
    print(f"Initialization time: {time.process_time() - start:.4f}s")

    # Iterate through polynomials and encode to pseudo-Boolean constraints
    cnf1 = CNF()
    for poly in tseytin_polys:
        if poly.constant_coefficient() > 0:
            poly = -poly

        coeffs = poly.coefficients()
        monomials = poly.monomials()

        const = 0
        if monomials and monomials[-1].is_constant():
            const = -coeffs[-1]
            monomials = monomials[:-1]
            coeffs = coeffs[:-1]

        lits = [dictionary_vars_to_lits[m] for m in monomials]

        cnf = PBEnc.equals(lits=lits, weights=coeffs, top_id=top, bound=const)

        max_lit = max(abs(lit) for clause in cnf.clauses for lit in clause)
        top = max(top, max_lit + 1)

        cnf1.extend(cnf)
        all_clauses.append(cnf.clauses)

    print(f"Total time: {time.process_time() - start:.4f}s")
    return all_clauses, dictionary_vars_to_lits
