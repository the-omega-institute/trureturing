# Chiral anomalies and charge rigidity in four dimensions

## Abstract

Local anomaly cancellation, charge quantization, and Weyl traces for one generation.

Write n = N_c for the number of colors and y = (y_Q, y_u, y_d, y_L, y_e, y_n) for one generation in all-left-handed notation. The u, d, e, and n singlets are charge conjugates of the right-handed particles. The four local equations are 2y_Q + y_u + y_d = 0, ny_Q + y_L = 0, 2ny_Q + ny_u + ny_d + 2y_L + y_e + y_n = 0, and 2ny_Q³ + ny_u³ + ny_d³ + 2y_L³ + y_e³ + y_n³ = 0. The algebraic classifications use a field of characteristic zero.

**Theorem 1.1 (Factorization of the cubic).**

Lean statement: `D5/S3/Quantum/Gauge/ChiralAnomalyRigidity4D.cubic_anomaly_factorization`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/ChiralAnomalyRigidity4D.cubic_anomaly_factorization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Over any field, impose the three linear equations and put t = y_u + y_Q and w = y_e − ny_Q. The cubic polynomial is exactly 6ny_Q(w − t)(w + t).

**Theorem 1.2 (The three anomaly-free planes).**

Lean statement: `D5/S3/Quantum/Gauge/ChiralAnomalyRigidity4D.anomaly_free_planes_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/ChiralAnomalyRigidity4D.anomaly_free_planes_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For n ≥ 1, all four equations hold exactly on the union of the planes Π₊(a,t) = (a, t − a, −t − a, −na, na − t, na + t), Π₋(a,t) = (a, t − a, −t − a, −na, na + t, na − t), and Π₀(b,c) = (0, b, −b, 0, c, −c), with parameters in the field.

**Theorem 1.3 (The color equation at one color).**

Lean statement: `D5/S3/Quantum/Gauge/ChiralAnomalyRigidity4D.nc_one_counterexample`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/ChiralAnomalyRigidity4D.nc_one_counterexample` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At n = 1, (1, 1, −1, −1, 0, 0) satisfies the weak, mixed gravitational, and cubic equations and lies outside the union of the three planes.

**Theorem 1.4 (The three lines with neutral singlet).**

Lean statement: `D5/S3/Quantum/Gauge/ChiralAnomalyRigidity4D.anomaly_free_lines_without_nuR_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/ChiralAnomalyRigidity4D.anomaly_free_lines_without_nuR_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For n ≥ 1, the four anomalies vanish and y_n = 0 exactly on the lines a(1, −(n + 1), n − 1, −n, 2n, 0), a(1, n − 1, −(n + 1), −n, 2n, 0), and (0, b, −b, 0, 0, 0).

**Theorem 1.5 (Dirac Yukawa equations on Π₊).**

Lean statement: `D5/S3/Quantum/Gauge/ChiralAnomalyRigidity4D.dirac_yukawa_pi_plus_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/ChiralAnomalyRigidity4D.dirac_yukawa_pi_plus_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Over any field, with Higgs hypercharge h, the four equations y_Q + h + y_u = 0, y_Q − h + y_d = 0, y_L − h + y_e = 0, and y_L + h + y_n = 0 hold on Π₊(a,t) exactly when t = −h.

**Theorem 1.6 (The Dirac B−L family).**

Lean statement: `D5/S3/Quantum/Gauge/ChiralAnomalyRigidity4D.dirac_yukawa_bl_family_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/ChiralAnomalyRigidity4D.dirac_yukawa_bl_family_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* K. S. Babu and R. N. Mohapatra (1989). *Is there a connection between quantization of electric charge and a Majorana neutrino?*. DOI: [10.1103/PhysRevLett.63.938](https://doi.org/10.1103/PhysRevLett.63.938). URL: <https://doi.org/10.1103/PhysRevLett.63.938>.

*Commentary.*

For n ≥ 1, the anomalies and the four Dirac Yukawa equations vanish exactly when y = Y₀ + ε(1/n, −1/n, −1/n, −1, 1, 1) for a unique field element ε, where Y₀ = Π₊(h/n, −h). The vector multiplying ε is B−L in the all-left-handed convention.

**Theorem 1.7 (Majorana quantization).**

Lean statement: `D5/S3/Quantum/Gauge/ChiralAnomalyRigidity4D.majorana_restores_charge_quantization`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/ChiralAnomalyRigidity4D.majorana_restores_charge_quantization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* K. S. Babu and R. N. Mohapatra (1989). *Is there a connection between quantization of electric charge and a Majorana neutrino?*. DOI: [10.1103/PhysRevLett.63.938](https://doi.org/10.1103/PhysRevLett.63.938). URL: <https://doi.org/10.1103/PhysRevLett.63.938>.

*Commentary.*

For n ≥ 1, the anomalies, Dirac Yukawa equations, and Majorana equation 2y_n = 0 hold exactly when y = Π₊(h/n, −h). The Majorana equation sets ε = 0. At h = 1/2 these give particle charges ((n + 1)/(2n), −(n − 1)/(2n), 0, −1) and generation sum zero.

**Theorem 1.8 (The electric charges along the Dirac family).**

Lean statement: `D5/S3/Quantum/Gauge/ChiralAnomalyRigidity4D.dirac_family_electric_charges`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/ChiralAnomalyRigidity4D.dirac_family_electric_charges` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At h = 1/2 and n ≥ 1, the particle charges u, d, ν, e are ((n + 1)/(2n) + ε/n, −(n − 1)/(2n) + ε/n, −ε, −1 − ε). The generation sum n(Q_u + Q_d) + Q_ν + Q_e vanishes for every ε.

**Theorem 1.9 (Three colors from fixed quark weights).**

Lean statement: `D5/S3/Quantum/Gauge/ChiralAnomalyRigidity4D.quark_charges_uniquely_select_nc_three`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/ChiralAnomalyRigidity4D.quark_charges_uniquely_select_nc_three` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For n ≥ 1, set (y_Q, y_u, y_d) = (1/6, −2/3, 1/3) and y_n = 0. The anomalies vanish exactly when n = 3, y_L = −1/2, and y_e = 1. The linear equations give y_L = −n/6 and y_e = n/3, and the cubic becomes n(n − 3)(n + 3)/36. At three colors the weights are those of the finite spectral triple.

**Theorem 1.10 (Weyl traces on the quantized family).**

Lean statement: `D5/S3/Quantum/Gauge/ChiralAnomalyRigidity4D.weyl_traces_quantized`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/ChiralAnomalyRigidity4D.weyl_traces_quantized` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For n ≥ 1 and h = 1/2, the one-generation Weyl traces at Y₀ are Tr(T_c²) = 2, Tr(T₃²) = (n + 1)/2, Tr(T₃Y) = 0, Tr(Y²) = (n + 1)(n + 2)/(2n), and Tr(Q²) = (n + 1)²/n. The mixed trace vanishes for every hypercharge assignment. Use fundamental color normalization 1/2, continued algebraically to n = 1. The ratio Tr(T₃²)/(Tr(T₃²) + Tr(Y²)) gives the curve s_anom(n) = n/(2(n + 1)).

**Theorem 1.11 (Three colors from equal Weyl traces).**

Lean statement: `D5/S3/Quantum/Gauge/ChiralAnomalyRigidity4D.weyl_arc_trace_nc_three_and_weinberg_angle`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/ChiralAnomalyRigidity4D.weyl_arc_trace_nc_three_and_weinberg_angle` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The color and weak generator traces agree exactly at n = 3, where k_Y = Tr(Y²)/Tr(T₃²) = 5/3 on the quantized family and s_anom(3) = 3/8.

**Theorem 1.12 (The fixed-charge mixing curve).**

Lean statement: `D5/S3/Quantum/Gauge/ChiralAnomalyRigidity4D.fixed_charge_weak_mixing`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/ChiralAnomalyRigidity4D.fixed_charge_weak_mixing` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

With the rational hypercharge table of the finite spectral triple and n quark colors, the ratio Tr(T₃²)/(Tr(T₃²) + Tr(Y²)) is s_fixed(n) = 9(n + 1)/(4(9 + 5n)).

**Theorem 1.13 (Difference of the mixing curves).**

Lean statement: `D5/S3/Quantum/Gauge/ChiralAnomalyRigidity4D.weinberg_angle_difference`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/ChiralAnomalyRigidity4D.weinberg_angle_difference` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For natural n, s_anom(n) − s_fixed(n) = (n − 3)(n + 3)/(4(n + 1)(9 + 5n)).

**Theorem 1.14 (The mixing-curve intersection).**

Lean statement: `D5/S3/Quantum/Gauge/ChiralAnomalyRigidity4D.weinberg_angle_intersection_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/ChiralAnomalyRigidity4D.weinberg_angle_intersection_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For natural n, the curves agree exactly at n = 3. Their common value is 3/8.

## References

- Truth anchor: `D5/S3/Quantum/Gauge/ChiralAnomalyRigidity4D.anomaly_free_lines_without_nuR_iff`
- Truth anchor: `D5/S3/Quantum/Gauge/ChiralAnomalyRigidity4D.anomaly_free_planes_iff`
- Truth anchor: `D5/S3/Quantum/Gauge/ChiralAnomalyRigidity4D.cubic_anomaly_factorization`
- Truth anchor: `D5/S3/Quantum/Gauge/ChiralAnomalyRigidity4D.dirac_family_electric_charges`
- Truth anchor: `D5/S3/Quantum/Gauge/ChiralAnomalyRigidity4D.dirac_yukawa_bl_family_iff`
- Truth anchor: `D5/S3/Quantum/Gauge/ChiralAnomalyRigidity4D.dirac_yukawa_pi_plus_iff`
- Truth anchor: `D5/S3/Quantum/Gauge/ChiralAnomalyRigidity4D.fixed_charge_weak_mixing`
- Truth anchor: `D5/S3/Quantum/Gauge/ChiralAnomalyRigidity4D.majorana_restores_charge_quantization`
- Truth anchor: `D5/S3/Quantum/Gauge/ChiralAnomalyRigidity4D.nc_one_counterexample`
- Truth anchor: `D5/S3/Quantum/Gauge/ChiralAnomalyRigidity4D.quark_charges_uniquely_select_nc_three`
- Truth anchor: `D5/S3/Quantum/Gauge/ChiralAnomalyRigidity4D.weinberg_angle_difference`
- Truth anchor: `D5/S3/Quantum/Gauge/ChiralAnomalyRigidity4D.weinberg_angle_intersection_iff`
- Truth anchor: `D5/S3/Quantum/Gauge/ChiralAnomalyRigidity4D.weyl_arc_trace_nc_three_and_weinberg_angle`
- Truth anchor: `D5/S3/Quantum/Gauge/ChiralAnomalyRigidity4D.weyl_traces_quantized`
- Dependency: [D5/S3/Quantum/Gauge/FiniteSpectralTripleSM](FiniteSpectralTripleSM.md)
