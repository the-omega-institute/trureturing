"""Directed endpoint and conservative form caps; Grams and signs stay unpaid.

Requires Python 3.10+ and python-flint 0.9.0. Reuse the existing derivative
supplier definitions; neither its old grid nor translation producer runs.
"""

import argparse
import hashlib
import importlib.util
import json
import sys
from pathlib import Path

import flint
from flint import arb, ctx, fmpq


def upper_record(value):
    if not value.is_finite():
        raise ValueError("Finite endpoint constant required")
    cap = value.upper()
    return {"display": str(cap), "dyadic": [str(x) for x in cap.man_exp()]}


def moment(power, rate, start, terms):
    """Enclose the positive series sum n^power exp(-rate*n^2)."""
    if not rate > 0 or start < 1 or terms < start:
        raise ValueError("Positive rate and nonempty retained series required")
    total = sum((arb(n**power) * (-rate*n*n).exp()
                 for n in range(start, terms+1)), arb(0))
    first = terms+1
    ratio = arb(fmpq(first+1, first))**power * (-rate*(2*first+1)).exp()
    if not ratio < 1:
        raise ValueError("Geometric remainder ratio must be certified below one")
    tail = arb(first**power) * (-rate*first*first).exp() / (1-ratio)
    lo, hi = total.lower(), (total+tail).upper()
    return arb((lo+hi)/2, ((hi-lo)/2).upper())


def produce(canonical, precision, terms):
    if precision < 128 or terms < 6:
        raise ValueError("At least 128 bits and six retained terms required")
    if sys.version_info < (3, 10) or flint.__version__ != "0.9.0":
        raise ValueError("Python 3.10+ and python-flint 0.9.0 are required")
    ctx.prec = precision
    pi = arb.pi()
    translation = canonical / "theta_translation_bounds.py"
    spec = importlib.util.spec_from_file_location("endpoint_translation_supplier", translation)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    derivative, constants, derivative_hash = module.derivative_supplier(
        canonical / "derivative_bandwidth.py")
    scope = derivative.__globals__
    wc0, wc1 = constants[0], scope["scalar_constant"](1)
    coeff = scope["coeff"]

    A, tc, rb = arb(fmpq(3, 2)), arb(2).log()/2, arb(4).log()
    rho, kappa = arb(fmpq(1, 16)), 3/(2*pi)
    rate, ua = pi * arb(fmpq(1, 3)).cos(), (2*(A-tc)).exp()
    shifted = {p: (rate*ua).exp()*moment(p, rate*ua, 2, terms)
               for p in (2, 4, 6)}
    qstar = (2*pi*ua*shifted[4]+3*shifted[2])/(2*pi*ua-3)
    if not qstar < arb(fmpq(1, 6)) or not 3*rate*ua > 2:
        raise ValueError("Original relative-tail conditions not certified")
    D0 = kappa+(ua+kappa)*qstar
    D1 = (2*kappa+2*kappa*shifted[2]
          +2*pi*ua*ua*(shifted[6]-shifted[4])
          +2*kappa*pi*ua*(shifted[4]-shifted[2]))
    L = 1-kappa/ua
    if not L > 0:
        raise ValueError("Positive real relative denominator required")
    fA, Lminus, Lplus = (1+(-A).exp()).sqrt(), 1+2*D0*(-2*A).exp(), 1+D0*(-2*A).exp()
    B0 = Lminus/(2*L.sqrt()) + (-A).exp() * (
        2*D0/L.sqrt()+D0/(L.sqrt()*(L.sqrt()+1)))
    B1 = Lminus/(2*L.sqrt()) + (-A).exp()*fA * (
        2*D1/L.sqrt()+Lminus*D1/(2*L**arb(fmpq(3, 2))))
    Bplus0 = fA*Lplus/L.sqrt()
    Bplus1 = ((-A).exp()*Lplus/2+fA*D1*(-2*A).exp())/L.sqrt()
    Bplus1 += fA*Lplus*D1*(-2*A).exp()/(2*L**arb(fmpq(3, 2)))

    def integral(power, decay):
        order = arb(fmpq(power, 2))
        return decay**(-order)*order.gamma()/2

    def exterior(power, decay, spatial_start):
        order = arb(fmpq(power, 2))
        return decay**(-order)*(decay*(2*spatial_start).exp()).gamma_upper(order)/2

    g0 = integral(5, rate).sqrt()
    g1 = (arb(fmpq(25, 4))*integral(5, rate)
          +5*pi*integral(7, rate)+pi*pi*integral(9, rate)).sqrt()
    h0 = integral(3, rate).sqrt()
    h1 = (arb(fmpq(25, 4))*integral(3, rate)
          +5*pi*integral(5, rate)+pi*pi*integral(7, rate)).sqrt()
    profile = (g0*g0+g1*g1).sqrt()
    dominant = ((B0*h0)**2+(B0*h1+B1*h0)**2).sqrt()
    X = A+tc
    moments = {p: moment(p, rate, 1, terms) for p in (2, 4, 6)}
    numerator = []
    for j in (0, 1):
        value = arb(0)
        for exponent, prefactor, degree in ((fmpq(9, 2), 4*pi*pi, 4),
                                            (fmpq(5, 2), 6*pi, 2)):
            for k, coefficient in enumerate(coeff[j, exponent]):
                value += (prefactor*(arb(exponent)*X).exp()
                          *arb(abs(coefficient))*(pi*(2*X).exp())**k
                          *moments[degree+2*k])
        numerator.append(value)
    gamma1 = wc1/18
    minimum = 18*(-pi*(2*A).exp()).exp()
    Vc = (2*wc0*(arb(fmpq(9, 2))*A).exp()*(A/2).cosh()).sqrt()
    Lc = gamma1*(4*A).exp()/2+arb(fmpq(1, 4))
    H0 = Vc*numerator[0]/minimum
    H1 = Vc*((Lc+gamma1*(4*A).exp())*numerator[0]+numerator[1])/minimum
    inverse_factor = (arb(fmpq(9, 2))*tc).exp()/pi
    compact = inverse_factor*(A*(H0*H0+H1*H1)).sqrt()

    bs = arb(fmpq(3, 8))
    zeta = pi/2-bs
    # Full positive-line maxima also bound the restricted maxima on u >= 1.
    # Do not evaluate at a rounded maximizer: that could undershoot the peak.
    maxima = [(power/zeta)**power*arb(-power).exp() for power in (1, 3)]
    K0 = wc0.sqrt()*maxima[0]
    K1 = wc0.sqrt()*(gamma1/2+arb(fmpq(1, 4)))*maxima[1]
    edge_rate = (-2*bs).exp()
    integer_edge_sum = edge_rate/(1-edge_rate)**2-edge_rate
    prime_B_cap = 2*K0*K0*integer_edge_sum
    wf2_terms = 128
    M2_partial = sum((arb(2)/(2*arb(k)+arb(fmpq(1, 2)))**3
                      for k in range(wf2_terms+1)), arb(0))
    M2_tail = 1/(2*(2*arb(wf2_terms)+arb(fmpq(1, 2)))**2)
    M2_cap = M2_partial+M2_tail
    c0_cap = arb(fmpq(3, 2))+prime_B_cap+2*M2_cap*K1*K1*edge_rate
    c1_cap = 2*M2_cap*K0*K0*edge_rate
    ground_h1 = (1+(K0/2+2*K1)**2
                 *(2*bs)**arb(fmpq(-1, 2))*(2*bs).gamma_upper(arb(fmpq(1, 2)))).sqrt()
    centering = inverse_factor*(tc/2).cosh()*ground_h1
    beta = 4*(1-rho)/(1+rho)**2-1
    Ew = 4/(1-rho)+1
    u0, u1 = arb(fmpq(5, 2))*Bplus0+Bplus1, pi*Ew*Bplus0
    wrong = (9*tc).exp()*(
        (Bplus0*Bplus0+u0*u0)*exterior(5, pi*beta, A)
        +2*u0*u1*exterior(7, pi*beta, A)
        +u1*u1*exterior(9, pi*beta, A)).sqrt()
    ideal_compact = A.sqrt()*(arb(fmpq(5, 2))*A).exp()*(
        1+(arb(fmpq(5, 2))+pi*(2*(A-rb)).exp())**2).sqrt()
    ideal_wrong = ((1+(arb(fmpq(5, 2))+pi*(-2*rb).exp())**2)/5).sqrt()
    slow = (arb(2).sqrt()*dominant).upper()
    fast = (arb(2).sqrt()*(compact+wrong+ideal_compact+ideal_wrong)+centering).upper()
    coarse = (slow+fast).upper()
    g = integral(5, pi).sqrt()
    a0 = arb(2).sqrt()*g
    overlap = (rate/2).gamma_upper(0)/2
    Qcoarse = (4*g0*coarse+coarse*coarse*(-rb).exp()
              +4*(rb+overlap)*(-4*rb).exp()).upper()
    coarse_threshold = max(rb.upper(), (4*Qcoarse/(a0*a0)).log().upper())
    coarse_integer = coarse_threshold.ceil().unique_fmpz()
    if coarse_integer is None:
        raise ValueError("A unique coarse integer threshold is required")
    Ctheta = 2*slow
    Qtheta = (4*g0*Ctheta+Ctheta*Ctheta*(-rb).exp()
              +4*(rb+overlap)*(-4*rb).exp()).upper()
    threshold = max(rb.upper(), (arb(fmpq(2, 3))*(fast/slow).log()).upper(),
                    (4*Qtheta/(a0*a0)).log().upper())
    integer_threshold = threshold.ceil().unique_fmpz()
    if integer_threshold is None:
        raise ValueError("A unique integer normalization threshold is required")
    Rstar = int(integer_threshold)+1
    if not fast*(arb(fmpq(-3, 2))*Rstar).exp() <= slow:
        raise ValueError("Balanced decay threshold must be certified")
    if not Qtheta*arb(-Rstar).exp() < a0*a0/4:
        raise ValueError("Actual bilinear normalization disk not certified")
    alpha = arb(3).sqrt()/2
    Cnormalized = (Ctheta/(alpha*a0)+2*profile*Qtheta/(alpha*a0**3)).upper()
    Ntheta = ((2*profile+Ctheta*arb(-Rstar).exp())/(alpha*a0)).upper()
    d, R0 = arb(fmpq(1, 16)), Rstar+1
    form_kernel_factor = arb(2).sqrt()*max(g0.upper(), g1.upper())
    form_kernel_factor += a0*Cnormalized*(-(arb(R0)-d)).exp()
    positive_tail = (2*(arb(fmpq(25, 4))*exterior(8, pi, arb(0))
                         +5*pi*exterior(10, pi, arb(0))
                         +pi*pi*exterior(12, pi, arb(0)))).sqrt()
    negative_tail = arb(fmpq(2, 25)).sqrt()*(arb(fmpq(5, 2))+pi)
    form_tail_factor = positive_tail+negative_tail+g*Cnormalized
    cF_cap = (c0_cap+c1_cap).sqrt()
    form_kernel_numeric = (2*(c0_cap*g0*g0+c1_cap*g1*g1)).sqrt()
    form_kernel_numeric += a0*cF_cap*Cnormalized*(-(arb(R0)-d)).exp()
    form_tail_numeric = (2*(c0_cap*exterior(8, pi, arb(0))
        +c1_cap*(arb(fmpq(25, 4))*exterior(8, pi, arb(0))
                  +5*pi*exterior(10, pi, arb(0))
                  +pi*pi*exterior(12, pi, arb(0))))).sqrt()
    form_tail_numeric += (arb(fmpq(2, 25))*(
        c0_cap+c1_cap*(arb(fmpq(5, 2))+pi)**2)).sqrt()+g*Cnormalized*cF_cap
    values = {"relative_D0": D0, "relative_D1": D1, "Cslow": slow, "Cfast": fast, "Ctheta": Ctheta,
              "Qtheta": Qtheta, "Cnormalized": Cnormalized, "Ntheta": Ntheta,
              "form_kernel_factor": form_kernel_factor, "form_tail_factor": form_tail_factor,
              "zero_free_relative_radius": Qtheta*arb(-Rstar).exp()/(a0*a0)}
    return {
        "scope": "Conditional original-theta endpoint and conservative WF2/form caps; actual Grams and signs remain unpaid.",
        "runtime": {"python": sys.version.split()[0], "python_flint": flint.__version__,
                    "precision_bits": precision},
        "retained_moment_terms": terms,
        "supplier_sha256": {"derivative_bandwidth.py": derivative_hash,
                            "theta_translation_bounds.py": hashlib.sha256(translation.read_bytes()).hexdigest()},
        "old_derivative_grid_executed": False,
        "old_translation_producer_executed": False,
        "Rstar_sufficient_integer": Rstar,
        "coarse_threshold_comparison": int(coarse_integer)+1,
        "coarse_normalized_cap_comparison": upper_record(
            coarse/(alpha*a0)+2*profile*Qcoarse/(alpha*a0**3)),
        "bound_choice": "Keep e^-R and e^(-5R/2) allowances separate; balance only after the certified threshold.",
        "R0": R0, "analytic_disk_radius": "1/16",
        "outer_strip": "1/6", "inner_strip": "1/8", "spatial_split": "3/2",
        "bounds": {name: upper_record(value) for name, value in values.items()},
        "form_factor_contract": "Mtheta <= form_kernel_factor*sqrt(c0+c1); Cd <= form_tail_factor*sqrt(c0+c1). Conservative enlarged WF2 coefficients supply absolute caps, not exact norms or optimal coefficients.",
        "WF2": {
            "moment_retained_terms": wf2_terms+1,
            "moment_tail_contract": "sum_{k>K} 2/(2k+1/2)^3 <= 1/[2(2K+1/2)^2]",
            "complete_prime_B_contract": "Both shifted directions; all prime powers dominated by integer edges: ||B|| <= 2 K0^2 [r/(1-r)^2-r], r=exp(-3/4)",
            "supremum_contract": "||s||_infinity^2 <= K0^2 exp(-3/4); ||s_prime||_infinity^2 <= K1^2 exp(-3/4)",
            "caps": {name: upper_record(value) for name, value in {
                "M2": M2_cap, "complete_prime_B_norm": prime_B_cap,
                "c0": c0_cap, "c1": c1_cap,
                "form_kernel_absolute": form_kernel_numeric,
                "form_tail_absolute": form_tail_numeric}.items()},
        },
        "normalization_disk_certified_from_paper_bound": True,
        "numerical_actual_columns_or_grams_acquired": False,
        "Lean_certification": False,
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--canonical", type=Path, default=Path(__file__).resolve().parent)
    parser.add_argument("--precision", type=int, default=256)
    parser.add_argument("--terms", type=int, default=6)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    result = produce(args.canonical.resolve(), args.precision, args.terms)
    args.output.write_text(json.dumps(result, indent=2)+"\n")
    print(json.dumps({key: result[key] for key in
                      ("Rstar_sufficient_integer", "R0", "bounds")}, indent=2))


if __name__ == "__main__":
    main()
