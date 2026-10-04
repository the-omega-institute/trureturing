# Exact Krasniqi boundary-contact certificate

These assets support the uniform lower bound and its ordinary analytic consequence in [KrasniqiBoundaryContact](../../develop/theory/KrasniqiBoundaryContact.md). They certify a continuum of parameters by exact rational Bernstein coefficients, rather than by parameter sampling.

From the project root, run:

```sh
python3 -B docs/reports/krasniqi-boundary-contact/audit_exact.py
```

From any other working directory, invoke the script by its path. Its default certificate directory is the script's own directory. An explicit directory can be supplied with `--certificate-dir PATH`. Python's standard library is the only dependency. The script reads inputs and prints one JSON result; it writes no files. Optimized Python (`-O`) is rejected because assertions are part of its checks. Malformed data, incomplete partitions, failed coefficient comparisons, or inconsistent metadata produce a nonzero exit.

`P6-certificate.json` gives the full 238-leaf closed partition of $[1,7/3]\times[0,1]\times[0,16]$, encoded by coordinate/half pairs. The 134 positive leaves have global exact minimum $6583/11943936$. The 104 excluded leaves use negative upper bounds for the relaxed parameter expression (87), the squared source bound (1), or $a+c-2$ (16). Both children include the split face. The maximum depth is 17.

`tail-certificate.json` gives one positive leaf for $\partial_tP_6(a,c,16)$ on the entire parameter rectangle, with exact minimum $45599851/571536000$. The analytic proof uses positivity of $P_6''$ to extend the lower bound beyond 16.

`audit_exact.py` reconstructs $q_0,\ldots,q_9$ by multiplying truncated exponential series, then checks every literal recurrence equation and $q_1,q_2$. It constructs $P_6$, its tail derivative, and the exclusion polynomials from those definitions. It verifies complete prefix-free binary coverage, computes exact affine-to-Bernstein coefficients, re-expands the conversion identities coefficient by coefficient, checks every positivity/exclusion direction, and bounds the logarithmic relaxation error with the exact 24-term series for $\log3$. No opaque polynomial arrays or floating-point computations are used.

The two certificate files are mathematical result data produced by the project research. The verifier is the independent exact-arithmetic implementation supplied with that research, adapted for portable read-only invocation and strict input checking. The definitions and source conditions come from Krasniqi, arXiv:2609.28707v1; citation and license details are in the [Library note](../../../Library/Analytic/krasniqi2026bernsteinboundary.md). Project-authored prose, code, and rational data use the repository's Apache-2.0 license. The external article is cited, not redistributed.

The verifier establishes only the rational polynomial comparisons, log enclosure, and partition coverage. The ordinary proof additionally supplies dominated differentiation, sign-switch positivity, Taylor's remainder, the tail argument, and contact uniqueness. A full Lean-kernel settlement remains open: it still requires the literal family and Bernstein definition, source-faithful regularized Laplace/moment identities, the attained-boundary existence and strict parameter restrictions, integrability and differentiation bridges, tensor Bernstein bounds and this exact partition, Taylor's inequality, and the all-$b$ contact argument with accepted axiom closure. These assets carry no Lean, freezing, coverage, or Problems-resolution claim.
