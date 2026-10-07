# Packing Bounds

## Abstract

Uniform constants and completion of lattice packing.

Uniform constants and completion of lattice packing. The results below relate packing bounds to the stochastic ellipsoid construction.

**Theorem 1.1 (r0 le qrt).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Completion/PackingBounds.r0_le_qrt`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Completion/PackingBounds.r0_le_qrt` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

r₀ ≤ 8/q. log n/n ≤ 4/q³ ≤ 1/(9q²) because q ≥ 36, and the square root of the right-hand side is 1/(3q).

**Theorem 1.2 (eta le qrt).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Completion/PackingBounds.eta_le_qrt`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Completion/PackingBounds.eta_le_qrt` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

η ≤ 1/q. η ≤ √2/n³ ≤ 2/q¹² ≤ 1/q.

**Theorem 1.3 (card UT pos).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Completion/PackingBounds.card_UT_pos`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Completion/PackingBounds.card_UT_pos` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

card (UT n) > 0.

**Theorem 1.4 (eta pos).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Completion/PackingBounds.eta_pos`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Completion/PackingBounds.eta_pos` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

η > 0: η² = 2·h·card·n and all three factors are positive.

**Theorem 1.5 (fail Total nonneg).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Completion/PackingBounds.failTotal_nonneg`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Completion/PackingBounds.failTotal_nonneg` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

failTotal is nonnegative.

**Theorem 1.6 (kappa upper).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Completion/PackingBounds.kappa_upper`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Completion/PackingBounds.kappa_upper` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

1/mm² ≤ 1 + 8u, hence (1/2 + 2rr)/mm² ≤ 1/2 + 12u + 2rr.

**Theorem 1.7 (cq of Z).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Completion/PackingBounds.cq_of_Z`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Completion/PackingBounds.cq_of_Z` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

1/(2Z²) ≥ 1/2 − 4u − 3δ whenever 1 ≤ Z and Z² ≤ 1 + 8u + 6δ.

**Theorem 1.8 (cq lower).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Completion/PackingBounds.cq_lower`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Completion/PackingBounds.cq_lower` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

1/2 − 1/(2·MM²(1+δ)²) ≤ 4u + 3δ at MM ≤ 1 + 2u.

**Theorem 1.9 (drift Cen le).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Completion/PackingBounds.driftCen_le`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Completion/PackingBounds.driftCen_le` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

driftCen ≤ κ((1+ε)·K·c²·dim + (1+1/ε)(c₃η)²) — TruncSumMean.integral_sum_sqTrunc_le on the truncated sum, the (1+1/ε) piece kept as it stands. This is the companion of TruncSumMean.driftCen_ge, in the direction hbudget needs.

**Theorem 1.10 (measure Real compl lt tau le cut).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Completion/PackingBounds.measureReal_compl_lt_tau_le_cut`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Completion/PackingBounds.measureReal_compl_lt_tau_le_cut` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

On goodCut … K the stopping time exceeds K, so it exceeds every k ≤ K.

**Theorem 1.11 (h S of int Weight cut).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Completion/PackingBounds.hS_of_intWeight_cut`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Completion/PackingBounds.hS_of_intWeight_cut` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

hS at the cut index. GoodPathBounds.hS_of_intWeight with the {k < τ} total collapsed against goodCut … K — the event whose count the tail side does supply.

**Theorem 1.12 (good Cut fail le).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Completion/PackingBounds.goodCut_fail_le`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Completion/PackingBounds.goodCut_fail_le` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The goodCut failure is failTotal — goodPathCut's own union bound, extracted.

**Theorem 1.13 (num Steps mul step eq).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Completion/PackingBounds.numSteps_mul_step_eq`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Completion/PackingBounds.numSteps_mul_step_eq` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

N·X = T·dim·(1 − 50/n) at the adopted parameters — TruncSumMean.driftCen_ge_adopted's own identity, extracted so a shorter horizon can use it.

**Theorem 1.14 (step mul dim le one).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Completion/PackingBounds.step_mul_dim_le_one`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Completion/PackingBounds.step_mul_dim_le_one` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

One step of the drift is at most 1: c²·dim = h·card ≤ n²/n⁹.

**Theorem 1.15 (log div le).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Completion/PackingBounds.log_div_le`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Completion/PackingBounds.log_div_le` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

log n/n ≤ 1/200 — sharper than AdoptedConstants95.log_ratio_le, and what the short-horizon hLb needs: log n ≤ 4q and n = q⁴ give log n/n ≤ 4/q³ ≤ 4/50 653.

**Theorem 1.16 (h Lb of bounds cut).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Completion/PackingBounds.hLb_of_bounds_cut`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Completion/PackingBounds.hLb_of_bounds_cut` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

hLb with the drift horizon one step short of N — the two 4·log n cancel.

**Theorem 1.17 (theta Tight comb B le).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Completion/PackingBounds.thetaTight_combB_le`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Completion/PackingBounds.thetaTight_combB_le` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The combined threshold is n-free at B m = B₀/n².

**Theorem 1.18 (count ratio q).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Completion/PackingBounds.count_ratio_q`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Completion/PackingBounds.count_ratio_q` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The count ratio, with the q³ kept. c₃'' = n²·q³, so a terminal weight θT ≤ Kc·n² gives a Markov ratio 2·Kc/q³ — the q³ is what makes log n · pcnt bounded.

**Theorem 1.19 (horizon mul card le).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Completion/PackingBounds.horizon_mul_card_le`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Completion/PackingBounds.horizon_mul_card_le` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

T·dim ≤ 16·log n — the companion of TruncSumMean.horizon_mul_card_ge.

**Theorem 1.20 (fail Total le inv).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Completion/PackingBounds.failTotal_le_inv`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Completion/PackingBounds.failTotal_le_inv` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

failTotal n pcnt ≤ pcnt + 1/(1000·n).

**Theorem 1.21 (theta Tight le 2800000).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Completion/PackingBounds.thetaTight_le_2800000`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Completion/PackingBounds.thetaTight_le_2800000` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The threshold at B₀ = 140, as a number: 3308·(32e² + 560) ≤ 2.64·10⁶.

**Theorem 1.22 (shortfall le twenty).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Completion/PackingBounds.shortfall_le_twenty`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Completion/PackingBounds.shortfall_le_twenty` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The shortfall total at t' = s' = 1, with both variance terms below 1.

**Theorem 1.23 (qrt le self).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Completion/PackingBounds.qrt_le_self`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Completion/PackingBounds.qrt_le_self` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

q ≤ q⁴ for q ≥ 37.

**Theorem 1.24 (delta le two div).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Completion/PackingBounds.delta_le_two_div`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Completion/PackingBounds.delta_le_two_div` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

η/m ≤ 2/q from η ≤ 1/q and m ≥ 1/2.

**Theorem 1.25 (rr le twelve).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Completion/PackingBounds.rr_le_twelve`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Completion/PackingBounds.rr_le_twelve` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

2·rr = 4η + 4c₃η ≤ 12/q.

**Theorem 1.26 (rm ge).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Completion/PackingBounds.rm_ge`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Completion/PackingBounds.rm_ge` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

(1+c₃)η ≤ rr·m at rr = 2(1+c₃)η and m ≥ 1/2.

**Theorem 1.27 (twenty k div sq le).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Completion/PackingBounds.twenty_k_div_sq_le`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Completion/PackingBounds.twenty_k_div_sq_le` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

20000/q² ≤ 15 at q ≥ 37.

**Theorem 1.28 (gap le).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Completion/PackingBounds.gap_le`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Completion/PackingBounds.gap_le` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The gap, as bare arithmetic: κ(1+ε) − cq ≤ 183·(1/q) ≤ 200·(1/q).

**Theorem 1.29 (rhs identity).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Completion/PackingBounds.rhs_identity`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Completion/PackingBounds.rhs_identity` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The numerator identity. S = K·dim − Θ/h − dim·(K·pbad) and L = logDet A₀ − (driftCen + 1) − 1, so driftRHS_acc − L + 20 is the term list num_le_const bounds.

**Theorem 1.30 (kp le six).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Completion/PackingBounds.kp_le_six`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Completion/PackingBounds.kp_le_six` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

κ(1+ε) ≤ 6 at κ ≤ 5, ε ≤ 1/5.

**Theorem 1.31 (twenty k div cube le).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Completion/PackingBounds.twenty_k_div_cube_le`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Completion/PackingBounds.twenty_k_div_cube_le` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

20000/q³ ≤ 0.396 at q ≥ 37 (measured 0.394 8; the ceiling is chosen above it).

**Theorem 1.32 (vterm le).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Completion/PackingBounds.vterm_le`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Completion/PackingBounds.vterm_le` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

K·c²·(n/m²) ≤ 1: K·h ≤ T = 16 log n/n², n/m² ≤ 4n, and log n/n ≤ 1/200.

**Theorem 1.33 (wterm le).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Completion/PackingBounds.wterm_le`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Completion/PackingBounds.wterm_le` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

K·(η²/2)² ≤ 1: η²/2 = h·card·n, h ≤ n⁻⁹, card ≤ n², and K·h ≤ 16 log n/n².

## References

- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Completion/PackingBounds.card_UT_pos`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Completion/PackingBounds.count_ratio_q`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Completion/PackingBounds.cq_lower`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Completion/PackingBounds.cq_of_Z`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Completion/PackingBounds.delta_le_two_div`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Completion/PackingBounds.driftCen_le`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Completion/PackingBounds.eta_le_qrt`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Completion/PackingBounds.eta_pos`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Completion/PackingBounds.failTotal_le_inv`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Completion/PackingBounds.failTotal_nonneg`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Completion/PackingBounds.gap_le`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Completion/PackingBounds.goodCut_fail_le`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Completion/PackingBounds.hLb_of_bounds_cut`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Completion/PackingBounds.hS_of_intWeight_cut`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Completion/PackingBounds.horizon_mul_card_le`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Completion/PackingBounds.kappa_upper`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Completion/PackingBounds.kp_le_six`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Completion/PackingBounds.log_div_le`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Completion/PackingBounds.measureReal_compl_lt_tau_le_cut`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Completion/PackingBounds.numSteps_mul_step_eq`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Completion/PackingBounds.qrt_le_self`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Completion/PackingBounds.r0_le_qrt`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Completion/PackingBounds.rhs_identity`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Completion/PackingBounds.rm_ge`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Completion/PackingBounds.rr_le_twelve`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Completion/PackingBounds.shortfall_le_twenty`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Completion/PackingBounds.step_mul_dim_le_one`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Completion/PackingBounds.thetaTight_combB_le`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Completion/PackingBounds.thetaTight_le_2800000`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Completion/PackingBounds.twenty_k_div_cube_le`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Completion/PackingBounds.twenty_k_div_sq_le`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Completion/PackingBounds.vterm_le`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Completion/PackingBounds.wterm_le`
- Dependency: [D5/S3/Arith/Lattices/Klartag/Completion/AdoptedConstants95](AdoptedConstants95.md)
- Dependency: [D5/S3/Arith/Lattices/Klartag/Completion/FailTotalBound99](FailTotalBound99.md)
- Dependency: [D5/S3/Arith/Lattices/Klartag/Completion/Theorem2R5](Theorem2R5.md)
- Dependency: [D5/S3/Arith/Lattices/Klartag/Contact/CutVariance](../Contact/CutVariance.md)
- Dependency: [D5/S3/Arith/Lattices/Klartag/Contact/ThetaIntegrated99](../Contact/ThetaIntegrated99.md)
- Dependency: [D5/S3/Arith/Lattices/Klartag/Tail/TailWiring](../Tail/TailWiring.md)
- Dependency: [D5/S3/Arith/Lattices/Klartag/Walk/ChainShortfall](../Walk/ChainShortfall.md)
