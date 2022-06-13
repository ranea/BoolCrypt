"""Find affine self-equivalences (ASE) of an implicit function of the permuted modular addition."""
import collections
import itertools
import math
import sys
import datetime
import warnings

from boolcrypt.utilities import (
    get_time, get_smart_print, get_symbolic_anf, BooleanPolynomialRing, anf2matrix
)
from boolcrypt.functionalequations import find_fixed_vars, solve_functional_equation
from boolcrypt.modularaddition import get_implicit_modadd_anf

import sage.all


def find_self_equivalence(
    central_anf, num_input_vars, bpr,
    left_equiv_degree=1, right_equiv_degree=1, equiv_ct_terms=True,
    add_invertibility_equations=False,
    verbose=False, debug=False, filename=None, **solve_args
):
    """Similar to functionalequations.find_equivalence,
    but with mandatory bpr argument and other minor changes."""
    prefix_left_equiv_coeffs, prefix_right_equiv_coeffs = "b", "a"
    left_anf = right_anf = central_anf

    assert not isinstance(left_anf, sage.rings.polynomial.pbori.pbori.BooleanPolynomial)
    assert not isinstance(right_anf, sage.rings.polynomial.pbori.pbori.BooleanPolynomial)

    assert add_invertibility_equations in [False, "right", "left", "both"]

    assert solve_args.get("ignore_initial_parsing", False) is not True
    initial_fixed_vars = solve_args.get("initial_fixed_vars", {})
    initial_fixed_vars = collections.OrderedDict(
        [(k, v) for k, v in initial_fixed_vars.items() if str(k).startswith(prefix_left_equiv_coeffs) or str(k).startswith(prefix_right_equiv_coeffs)])

    left_input_vars = right_input_vars = bpr.gens()[:num_input_vars]

    for v in itertools.chain(left_input_vars, right_input_vars):
        assert not str(v).startswith(prefix_left_equiv_coeffs)
        assert not str(v).startswith(prefix_right_equiv_coeffs)
        assert str(v).startswith("x")
    assert not prefix_left_equiv_coeffs.startswith("x")
    assert not prefix_right_equiv_coeffs.startswith("x")

    # f2 and f0 square
    assert len(left_anf) == len(right_anf)
    assert len(right_input_vars) == len(left_input_vars)

    f2 = get_symbolic_anf(left_equiv_degree, len(left_anf), len(right_anf), ct_terms=equiv_ct_terms,
                          prefix_inputs="x", prefix_coeffs=prefix_left_equiv_coeffs, bpr=bpr, coeff2expr=initial_fixed_vars)
    f1 = left_anf
    f0 = get_symbolic_anf(right_equiv_degree, len(right_input_vars), len(left_input_vars), ct_terms=equiv_ct_terms,
                          prefix_inputs="x", prefix_coeffs=prefix_right_equiv_coeffs, bpr=bpr, coeff2expr=initial_fixed_vars)
    f2_input_vars = [bpr("x" + str(i)) for i in range(len(left_anf))]
    f1_input_vars = left_input_vars
    f0_input_vars = [bpr("x" + str(i)) for i in range(len(right_input_vars))]

    g0 = right_anf
    g0_input_vars = right_input_vars

    lhs_anfs = [f0, f1, f2]
    lhs_input_vars = [f0_input_vars, f1_input_vars, f2_input_vars]

    rhs_anfs = [g0]
    rhs_input_vars = [g0_input_vars]

    initial_equations = []
    if add_invertibility_equations in ["right", "both"]:
        assert right_equiv_degree == 1
        initial_equations.append(bpr(anf2matrix(f0, f0_input_vars).determinant()) + bpr(1))
    if add_invertibility_equations in ["left", "both"]:
        assert left_equiv_degree == 1
        initial_equations.append(bpr(anf2matrix(f2, f2_input_vars).determinant()) + bpr(1))

    new_kwargs = solve_args.copy()
    if "num_sat_solutions" not in new_kwargs:
        new_kwargs["num_sat_solutions"] = 1
    if "return_mode" not in new_kwargs:
        new_kwargs["return_mode"] = "list_anfs"
    if "initial_equations" in new_kwargs:
        new_kwargs["initial_equations"].extend(initial_equations)
    else:
        new_kwargs["initial_equations"] = initial_equations

    try:
        result = solve_functional_equation(
            lhs_anfs, rhs_anfs, lhs_input_vars, rhs_input_vars, bpr=bpr,
            verbose=verbose, debug=debug, filename=filename, **new_kwargs
        )
    except ValueError as e:
        get_smart_print(filename)(f"No solution found ({e})")
        return None
    else:
        if "return_mode" not in solve_args and "num_sat_solutions" not in solve_args:
            if solve_args.get("return_total_num_solutions", False):
                get_smart_print(filename)("ignoring return_total_num_solutions")
            return result[0][0][0], result[0][0][2]  # return f0, f2
        else:
            return result


def find_ase_implicit_pmodadd_3passes(wordsize, check, threads, verbose, debug, filename):
    """Find all affine self-equivalences of the implicit of pmodadd for a fixed wordsize"""
    assert wordsize <= 6

    verbose = verbose or debug

    ws = wordsize
    permuted = 1

    if filename is True:
        now = datetime.datetime.now()
        now = "{}D{}H{}M".format(now.day, now.hour, now.minute)
        filename = f"result-find_ase_implicit_pmodadd_3passes-w{ws}-{now}.txt"

    implicit_modadd_anf = get_implicit_modadd_anf(ws, permuted=permuted)
    num_inputs_implicit_modadd_anf = 4*ws if permuted else 3*ws

    deg = 1
    ct_terms = True

    smart_print = get_smart_print(filename)

    # creating bpr

    left_se_varnames = get_symbolic_anf(
        deg, len(implicit_modadd_anf), len(implicit_modadd_anf), ct_terms=ct_terms,
        prefix_inputs="x", prefix_coeffs="b", return_varnames=True)
    right_se_varnames = get_symbolic_anf(
        deg, num_inputs_implicit_modadd_anf, num_inputs_implicit_modadd_anf, ct_terms=ct_terms,
        prefix_inputs="x", prefix_coeffs="a", return_varnames=True)
    assert num_inputs_implicit_modadd_anf >= len(implicit_modadd_anf)
    all_varnames = right_se_varnames + left_se_varnames[len(implicit_modadd_anf):]
    bpr = BooleanPolynomialRing(names=all_varnames)

    implicit_modadd_anf = [bpr(f) for f in implicit_modadd_anf]

    # 1st pass - find linear fixed vars from raw equations

    initial_fixed_vars = {}
    smart_print(f"initial_fixed_vars: {initial_fixed_vars}\n")

    smart_print(f"{get_time()} | finding raw equations")

    invertibility = False
    solve_args = {
        "return_mode": "raw_equations",
        "only_linear_fixed_vars": True,  # set deglex as the order
        "initial_fixed_vars": initial_fixed_vars,
    }
    raw_equations = find_self_equivalence(
        implicit_modadd_anf, num_inputs_implicit_modadd_anf, bpr,
        #
        left_equiv_degree=deg, right_equiv_degree=deg, equiv_ct_terms=ct_terms,
        #
        add_invertibility_equations=invertibility,
        #
        threads=threads,
        verbose=False, debug=False, filename=filename,
        #
        **solve_args
    )

    smart_print(f"\n{get_time()} | finding linear fixed variables from raw equations")

    initial_fixed_vars, _ = find_fixed_vars(
        raw_equations, only_linear=True,  initial_r_mode="gauss", repeat_with_r_mode="gauss",
        initial_fixed_vars={bpr(k): bpr(v) for k, v in initial_fixed_vars.items()},
        bpr=bpr, check=True, verbose=verbose, debug=debug, filename=filename)

    # if ws == 2:
    #     for (k, v) in [('b1_1', 1), ('b3_1', 0), ('b2_1', 0), ('b0_1', 0), ('a6_5', 0), ('a6_1', 0), ('a4_5', 0), ('a4_1', 0), ('a2_5', 0), ('a2_1', 0), ('a0_5', 0), ('a0_1', 0), ('a6_3', 'a6_7'), ('a4_3', 'a4_7'), ('a3_5', 'a7_5'), ('a3_3', 'a3_7 + a7_3 + a7_7'), ('a3_2', 'a3_4 + a3_6 + a7_2 + a7_4 + a7_6'), ('a3_1', 'a7_1'), ('a3_0', 'a3_4 + a7_0 + a7_4'), ('a2_7', 'a4_7'), ('a2_6', 'a4_6'), ('a2_4', 'a4_0 + a4_2 + a4_4 + a4_6 + a6_0 + a6_2 + a6_6'), ('a2_3', 'a4_7'), ('a2_2', 'a4_0 + a4_2 + a4_4 + a6_0 + a6_4'), ('a2_0', 'a4_0 + a4_2 + a4_4 + a4_6 + a6_2 + a6_4 + a6_6'), ('a1_5', 'a5_5 + a7_5 + 1'), ('a1_1', 'a5_1 + a7_1 + 1'), ('a0_7', 'a4_7'), ('a0_6', 'a4_6'), ('a0_4', 'a4_4 + a6_0 + a6_2 + a6_6'), ('a0_3', 'a4_7'), ('a0_2', 'a4_2 + a6_0 + a6_4'), ('a0_0', 'a4_0 + a6_2 + a6_4 + a6_6')]:
    #         initial_fixed_vars[bpr(k)] = bpr(v)
    # if ws == 3:
    #     red_eqs = ['a0_0 + a6_0 + a9_3 + a9_6 + a9_9', 'a0_1 + a6_4 + a6_7 + a6_10 + a9_4 + a9_7 + a9_10', 'a0_2', 'a0_3 + a6_3 + a9_0 + a9_6', 'a0_4 + a6_4 + a9_4 + a9_10', 'a0_5 + a6_11', 'a0_6 + a6_6 + a9_0 + a9_3 + a9_9', 'a0_7 + a6_7 + a9_7', 'a0_8', 'a0_9 + a6_9', 'a0_10 + a6_10', 'a0_11 + a6_11', 'a1_0 + a1_3 + a1_6 + a7_0 + a7_3 + a7_6', 'a1_1 + a1_4 + a1_7 + a7_10 + 1', 'a1_2 + b1_2', 'a1_5 + a7_11 + b1_2', 'a1_8 + b1_2', 'a1_9 + a7_9', 'a1_10 + a7_10', 'a1_11 + a7_11', 'a2_1 + a2_4 + a2_7 + a2_10 + a8_1 + a8_4 + a8_7 + a8_10 + a11_1 + a11_4 + a11_7 + a11_10', 'a2_2 + a8_2 + a11_2 + 1', 'a2_5 + a2_11 + a8_5 + a8_11 + a11_5 + a11_11 + 1', 'a2_8 + a8_8 + a11_8 + 1', 'a3_0 + a6_0 + a6_3 + a6_6 + a6_9 + a9_3 + a9_6 + a9_9', 'a3_1 + a9_4 + a9_7 + a9_10', 'a3_2', 'a3_3 + a6_0 + a6_3 + a6_6 + a9_0 + a9_6', 'a3_4 + a6_10 + a9_4 + a9_10', 'a3_5 + a6_11', 'a3_6 + a6_0 + a6_3 + a6_6 + a6_9 + a9_0 + a9_3 + a9_9', 'a3_7 + a9_7', 'a3_8', 'a3_9 + a6_9', 'a3_10 + a6_10', 'a3_11 + a6_11', 'a4_0 + a7_0 + a7_3 + a7_6 + a7_9 + a10_3 + a10_6 + a10_9', 'a4_1 + a10_4 + a10_7 + a10_10 + 1', 'a4_2 + b1_2', 'a4_3 + a7_0 + a7_3 + a7_6 + a10_0 + a10_6', 'a4_4 + a7_10 + a10_4 + a10_10', 'a4_5 + a7_11 + b1_2', 'a4_6 + a7_0 + a7_3 + a7_6 + a7_9 + a10_0 + a10_3 + a10_9', 'a4_7 + a10_7', 'a4_8 + b1_2', 'a4_9 + a7_9', 'a4_10 + a7_10', 'a4_11 + a7_11', 'a5_0 + a5_6 + a11_0 + a11_6', 'a5_1 + a11_1', 'a5_2 + a11_2', 'a5_3 + a5_6 + a5_9 + a11_3 + a11_6 + a11_9', 'a5_4 + a5_10 + a11_4 + a11_10', 'a5_5 + a5_11 + a11_5 + a11_11', 'a5_7 + a11_7', 'a5_8 + a11_8', 'a6_1 + a6_4 + a6_7 + a6_10', 'a6_2', 'a6_5 + a6_11', 'a6_8', 'a7_1 + a7_4 + a7_7 + a7_10 + 1', 'a7_2 + b1_2', 'a7_5 + a7_11 + b1_2', 'a7_8 + b1_2', 'a9_1 + a9_4 + a9_7 + a9_10', 'a9_2', 'a9_5 + a9_11', 'a9_8', 'a10_1 + a10_4 + a10_7 + a10_10 + 1', 'a10_2 + b1_2', 'a10_5 + a10_11 + b1_2', 'a10_8 + b1_2', 'b0_1', 'b0_2', 'b1_1 + 1', 'b2_1', 'b2_2 + 1', 'b3_1', 'b3_2', 'b4_1', 'b4_2', 'b5_1', 'b5_2']
    #     red_eqs = [bpr(eq) for eq in red_eqs]
    #     initial_fixed_vars, _ = find_fixed_vars(
    #         red_eqs, only_linear=True, initial_r_mode=None, repeat_with_r_mode="gauss",
    #         initial_fixed_vars=initial_fixed_vars,
    #         bpr=bpr, check=True, verbose=verbose, debug=debug, filename=filename)

    # 2nd pass - find redundant equations

    smart_print(f"\n{get_time()} | finding redundant equations")

    invertibility = False  # if needed, add extra equations from _get_lowdeg_inv_equations
    num_sat_solutions = 512
    solve_args = {
        "reduction_mode": "gauss",
        "only_linear_fixed_vars": True,
        "num_sat_solutions": num_sat_solutions,
        "return_mode": "lincomb_solutions",
        "find_linear_combinations_in_solutions": True,
        "initial_fixed_vars": initial_fixed_vars,
        "num_sols_per_base_sol_to_check": 0,
        "return_total_num_solutions": True,
        # "ignore_initial_parsing": True,  # not allowed in find_equivalence
        "check_find_fixed_vars": check,
    }
    redundant_equations = find_self_equivalence(
        implicit_modadd_anf, num_inputs_implicit_modadd_anf, bpr,
        #
        left_equiv_degree=deg, right_equiv_degree=deg, equiv_ct_terms=ct_terms,
        #
        add_invertibility_equations=invertibility,
        #
        threads=threads,
        verbose=verbose, debug=debug, filename=filename,
        #
        **solve_args
    )

    smart_print(f"\nredundant equations found ({len(redundant_equations)}): "
                f"{[str(x) for x in redundant_equations]}")

    if len(redundant_equations) == 0:
        warnings.warn("no redundant equation found")

    if len(redundant_equations) >= 1:
        smart_print(f"\n{get_time()} | filtering redundant equations")
        solve_args = {
            "reduction_mode": "gauss",
            "only_linear_fixed_vars": True,
            "return_mode": "symbolic_anf",
            "find_redundant_equations": redundant_equations,
            "initial_fixed_vars": initial_fixed_vars,
            # "ignore_initial_parsing": True,  # not allowed in find_equivalence
            "check_find_fixed_vars": False,
        }
        redundant_equations = find_self_equivalence(
            implicit_modadd_anf, num_inputs_implicit_modadd_anf, bpr,
            #
            left_equiv_degree=deg, right_equiv_degree=deg, equiv_ct_terms=ct_terms,
            #
            add_invertibility_equations=invertibility,
            #
            threads=threads,
            verbose=verbose, debug=debug, filename=filename,
            #
            **solve_args
        )

        redundant_equations = list(redundant_equations)  # BooleanPolynomialVector no extend

        smart_print(f"\nvalid redundant equations found ({len(redundant_equations)}): "
                    f"{[str(x) for x in redundant_equations]}")

    # 3nd pass - find redundant equations

    smart_print(f"\n{get_time()} | finding redundant equations (2nd time)")

    initial_fixed_vars, initial_equations = find_fixed_vars(
        redundant_equations, only_linear=True,  initial_r_mode=None, repeat_with_r_mode="gauss",
        initial_fixed_vars=initial_fixed_vars,
        bpr=bpr, check=True, verbose=verbose, debug=debug, filename=filename)

    invertibility = "right"  # both == right
    num_sat_solutions = 256
    solve_args = {
        "reduction_mode": "gauss",
        "only_linear_fixed_vars": True,
        "num_sat_solutions": num_sat_solutions,
        "return_mode": "lincomb_solutions",
        "find_linear_combinations_in_solutions": True,
        "initial_fixed_vars": initial_fixed_vars,
        "initial_equations": initial_equations,
        "num_sols_per_base_sol_to_check": 0,
        "return_total_num_solutions": True,
        # "ignore_initial_parsing": True,  # not allowed in find_equivalence
        "check_find_fixed_vars": check,
    }
    redundant_equations = find_self_equivalence(
        implicit_modadd_anf, num_inputs_implicit_modadd_anf, bpr,
        #
        left_equiv_degree=deg, right_equiv_degree=deg, equiv_ct_terms=ct_terms,
        #
        add_invertibility_equations=invertibility,
        #
        threads=threads,
        verbose=verbose, debug=debug, filename=filename,
        #
        **solve_args
    )

    smart_print(f"\nredundant equations found ({len(redundant_equations)}): "
                f"{[str(x) for x in redundant_equations]}")

    if len(redundant_equations) == 0:
        warnings.warn("no redundant equation found")

    if len(redundant_equations) >= 1:
        smart_print(f"\n{get_time()} | filtering redundant equations")
        solve_args = {
            "reduction_mode": "gauss",
            "only_linear_fixed_vars": True,
            "return_mode": "symbolic_anf",
            "find_redundant_equations": redundant_equations,
            "initial_fixed_vars": initial_fixed_vars,
            "initial_equations": initial_equations,
            # "ignore_initial_parsing": True,  # not allowed in find_equivalence
            "check_find_fixed_vars": False,
        }
        redundant_equations = find_self_equivalence(
            implicit_modadd_anf, num_inputs_implicit_modadd_anf, bpr,
            #
            left_equiv_degree=deg, right_equiv_degree=deg, equiv_ct_terms=ct_terms,
            #
            add_invertibility_equations=invertibility,
            #
            threads=threads,
            verbose=verbose, debug=debug, filename=filename,
            #
            **solve_args
        )

        redundant_equations = list(redundant_equations)  # BooleanPolynomialVector no extend

        smart_print(f"\nvalid redundant equations found ({len(redundant_equations)}): "
                    f"{[str(x) for x in redundant_equations]}")

    # 4rd pass - find symbolic coeffs

    smart_print(f"\n{get_time()} | solving final pass")

    initial_fixed_vars, initial_equations = find_fixed_vars(
        redundant_equations, only_linear=True,  initial_r_mode=None, repeat_with_r_mode="gauss",
        initial_fixed_vars=initial_fixed_vars,
        bpr=bpr, check=True, verbose=verbose, debug=debug, filename=filename)

    num_sat_solutions = sage.all.infinity
    invertibility = "right"  # both == right
    solve_args = {
        "reduction_mode": "gauss",
        "only_linear_fixed_vars": False,
        "num_sat_solutions": num_sat_solutions,
        "return_mode": "symbolic_coeffs",
        "initial_fixed_vars": initial_fixed_vars,
        "initial_equations": initial_equations,
        "find_linear_combinations_in_solutions": True,
        "num_sols_per_base_sol_to_check": 0,
        "return_total_num_solutions": True,
        # "ignore_initial_parsing": True,  # not allowed in find_equivalence
        "check_find_fixed_vars": False,
    }
    symbolic_coeffs, equations, num_total_solutions = find_self_equivalence(
        implicit_modadd_anf, num_inputs_implicit_modadd_anf, bpr,
        #
        left_equiv_degree=deg, right_equiv_degree=deg, equiv_ct_terms=ct_terms,
        #
        add_invertibility_equations=invertibility,
        #
        threads=threads,
        verbose=verbose, debug=debug, filename=filename,
        #
        **solve_args
    )

    smart_print("\nnum_total_solutions:", num_total_solutions,
                None if num_total_solutions is None
                else f"= 2^({math.log2(num_total_solutions)})")

    variables = list(reversed([v for v in bpr.gens()[4*ws:] if v not in symbolic_coeffs]))
    smart_print(f"non-fixed variables ({len(variables)} out of {len(bpr.gens()[4*ws:])}): {variables}")

    smart_print("equations:")
    for eq in equations:
        smart_print(f"\t{eq}")

    smart_print(f"symbolic_coeffs = {symbolic_coeffs}\n")

    return symbolic_coeffs, equations, num_total_solutions


if __name__ == '__main__':
    sys.setrecursionlimit(sys.getrecursionlimit()*1000)

    wordsize = 2
    check = True
    threads = 2

    verbose = True
    debug = False
    filename = None

    symbolic_coeffs, _, _ = find_ase_implicit_pmodadd_3passes(wordsize, check, threads, verbose, debug, filename)
