# Both states nondiagonal in the same basis

## Abstract

A common orthogonal change of basis makes both states nondiagonal while preserving the Tsallis ordering reversal.

This supplement answers Supriyo Dutta's question of 3 November 2026. The mathematical note is by Haobo Ma and Wenlin Zhang, licensed CC BY 4.0. It supplements the existing Maity-Furuichi-Dutta ordering refutation and does not resolve another conjecture. Supriyo Dutta is distinct from Soumyojyoti Dutta and Tushar in other correspondence.

**Definition 1.1 (The common change of basis).**

Lean statement: `D5/S3/Divergence/MaityFuruichiDuttaNondiagonalSupplement.U`

*Formalization.* `D5/S3/Divergence/MaityFuruichiDuttaNondiagonalSupplement.U` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

U = (1/sqrt(2)) [[1,1],[1,-1]] is real, self-adjoint and orthogonal.

Complete Lean statement: def U : Matrix (Fin 2) (Fin 2) ℂ :=   (1 / Real.sqrt 2 : ℝ) • !![1, 1; 1, -1]

**Definition 1.2 (The first nondiagonal state).**

Lean statement: `D5/S3/Divergence/MaityFuruichiDuttaNondiagonalSupplement.rhohat`

*Formalization.* `D5/S3/Divergence/MaityFuruichiDuttaNondiagonalSupplement.rhohat` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

rhohat = (1/10) [[5,3],[3,5]]. Both off-diagonal entries are 3/10.

Complete Lean statement: def rhohat : Matrix (Fin 2) (Fin 2) ℂ := !![1/2, 3/10; 3/10, 1/2]

**Definition 1.3 (The second nondiagonal state).**

Lean statement: `D5/S3/Divergence/MaityFuruichiDuttaNondiagonalSupplement.sigmahat`

*Formalization.* `D5/S3/Divergence/MaityFuruichiDuttaNondiagonalSupplement.sigmahat` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

sigmahat = (1/250) [[125+12 sqrt(6),-69],[-69,125-12 sqrt(6)]]. Both off-diagonal entries are -69/250.

Complete Lean statement: def sigmahat : Matrix (Fin 2) (Fin 2) ℂ :=   !![((125 + 12 * Real.sqrt 6) / 250 : ℝ), -69/250;       -69/250, ((125 - 12 * Real.sqrt 6) / 250 : ℝ)]

**Theorem 1.4 (The three actual source functions are unitarily invariant).**

Lean statement: `D5/S3/Divergence/MaityFuruichiDuttaNondiagonalSupplement.functions_unitary`

*Proof.* Machine-checked in Lean as `D5/S3/Divergence/MaityFuruichiDuttaNondiagonalSupplement.functions_unitary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The same unitary conjugates both arguments. Every real spectral function commutes with this conjugation, and cyclicity preserves its trace. Consequently the existing renyiRZ, B2 and tsallis definitions retain their values, for all parameters. On positive definite states these functions use positive spectral calculus. The extension to arbitrary matrices in the statement follows the total cfc convention, which is zero outside its predicate.

Complete Lean statement: theorem functions_unitary {n : ℕ} (u : unitary (Matrix (Fin n) (Fin n) ℂ))     (ρ σ : Matrix (Fin n) (Fin n) ℂ) (α r z q : ℝ) :     let e := Unitary.conjStarAlgAut ℂ _ u     renyiRZ α r z (e ρ) (e σ) = renyiRZ α r z ρ σ ∧     B2 α q (e ρ) (e σ) = B2 α q ρ σ ∧     tsallis α (e ρ) (e σ) = tsallis α ρ σ

**Theorem 1.5 (Density, determinants, entries and noncommutation).**

Lean statement: `D5/S3/Divergence/MaityFuruichiDuttaNondiagonalSupplement.matrix_facts`

*Proof.* Machine-checked in Lean as `D5/S3/Divergence/MaityFuruichiDuttaNondiagonalSupplement.matrix_facts` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Both matrices are positive definite with trace one and determinant 4/25. The (0,1) entry of their commutator is -18 sqrt(6)/625, which is nonzero. Thus they are noncommuting density matrices with nonzero off-diagonal entries in this common basis.

Complete Lean statement: theorem matrix_facts :     rhohat.PosDef ∧ rhohat.trace = 1 ∧ sigmahat.PosDef ∧ sigmahat.trace = 1 ∧     rhohat.det = 4/25 ∧ sigmahat.det = 4/25 ∧     rhohat 0 1 = 3/10 ∧ rhohat 1 0 = 3/10 ∧     sigmahat 0 1 = -69/250 ∧ sigmahat 1 0 = -69/250 ∧     (rhohat * sigmahat - sigmahat * rhohat) 0 1 = (-18 * Real.sqrt 6 / 625 : ℝ) ∧     rhohat * sigmahat ≠ sigmahat * rhohat

**Theorem 1.6 (The two eigenvalues).**

Lean statement: `D5/S3/Divergence/MaityFuruichiDuttaNondiagonalSupplement.characteristic_polynomials`

*Proof.* Machine-checked in Lean as `D5/S3/Divergence/MaityFuruichiDuttaNondiagonalSupplement.characteristic_polynomials` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each characteristic polynomial is (X-4/5)(X-1/5), so each state has eigenvalues 4/5 and 1/5, each with multiplicity one.

Complete Lean statement: theorem characteristic_polynomials :     rhohat.charpoly = (Polynomial.X - Polynomial.C (4/5:ℂ)) * (Polynomial.X - Polynomial.C (1/5:ℂ)) ∧     sigmahat.charpoly = (Polynomial.X - Polynomial.C (4/5:ℂ)) * (Polynomial.X - Polynomial.C (1/5:ℂ))

**Theorem 1.7 (One orthogonal matrix conjugates the entire pair).**

Lean statement: `D5/S3/Divergence/MaityFuruichiDuttaNondiagonalSupplement.common_orthogonal_conjugation`

*Proof.* Machine-checked in Lean as `D5/S3/Divergence/MaityFuruichiDuttaNondiagonalSupplement.common_orthogonal_conjugation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The original states are rho = diag(4/5,1/5) and sigma = (1/125) [[28,6 sqrt(6)],[6 sqrt(6),97]]. The displayed rhohat and sigmahat equal U rho U* and U sigma U*. Every real spectral function is covariant, including the powers and deformed logarithm occurring in all three source functions. The commutator is conjugated by that same U. Nondiagonality depends on the common basis; the bound values and noncommutation are invariant.

Complete Lean statement: theorem common_orthogonal_conjugation :     star U = U ∧ U * U = 1 ∧     rhohat = U * rho * star U ∧ sigmahat = U * sigma * star U ∧     (∀ (f : ℝ → ℝ) (X : Matrix (Fin 2) (Fin 2) ℂ),       cfc f (U * X * star U) = U * cfc f X * star U) ∧     rhohat * sigmahat - sigmahat * rhohat = U * (rho * sigma - sigma * rho) * star U

**Theorem 1.8 (The source parameters are admissible).**

Lean statement: `D5/S3/Divergence/MaityFuruichiDuttaNondiagonalSupplement.parameter_conditions`

*Proof.* Machine-checked in Lean as `D5/S3/Divergence/MaityFuruichiDuttaNondiagonalSupplement.parameter_conditions` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At alpha = r = 1/2, z = 2 and q = 1, all five source conditions hold: 0 <= alpha, alpha < 1, r is nonzero, z > 0 and q > 1-alpha.

Complete Lean statement: theorem parameter_conditions :     (0:ℝ) ≤ 1/2 ∧ (1/2:ℝ) < 1 ∧ (1/2:ℝ) ≠ 0 ∧ (0:ℝ) < 2 ∧ (1-(1/2:ℝ)) < 1

**Theorem 1.9 (The spectral sandwiches).**

Lean statement: `D5/S3/Divergence/MaityFuruichiDuttaNondiagonalSupplement.spectral_quantities`

*Proof.* Machine-checked in Lean as `D5/S3/Divergence/MaityFuruichiDuttaNondiagonalSupplement.spectral_quantities` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The fidelity trace F for the nondiagonal pair is exactly (2117+288 sqrt(2))/3125. The inverse-power sandwich is U A U*, where A = (1/25) [[7,3 sqrt(6)],[3 sqrt(6),97]] is the original inverse-power sandwich. These identities transport the actual spectral expressions used by the bounds.

Complete Lean statement: theorem spectral_quantities :     (trace (cfc (fun x:ℝ => x^(2:ℝ))       (cfc (fun x:ℝ => x^(1/8:ℝ)) sigmahat *         cfc (fun x:ℝ => x^(1/4:ℝ)) rhohat *         cfc (fun x:ℝ => x^(1/8:ℝ)) sigmahat))).re =       (2117 + 288 * Real.sqrt 2) / 3125 ∧     cfc (fun x:ℝ => x^(-(1/2:ℝ))) rhohat * sigmahat *       cfc (fun x:ℝ => x^(-(1/2:ℝ))) rhohat = U * A * star U

**Theorem 1.10 (Exact values and the strict chain).**

Lean statement: `D5/S3/Divergence/MaityFuruichiDuttaNondiagonalSupplement.exact_values_and_bounds`

*Proof.* Machine-checked in Lean as `D5/S3/Divergence/MaityFuruichiDuttaNondiagonalSupplement.exact_values_and_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The old exact sandwich trace (2117+288 sqrt(2))/3125 gives B1 = renyiRZ = 4(1-sqrt((2117+288 sqrt(2))/3125)). The existing positive square-root calculation gives B2 = 2-20/sqrt(154). Transport by the common U gives B2 < 2/5 < B1. The two-point functional calculus also gives the new exact value D = tsallis(1/2,rhohat,sigmahat) = 48/125. Since 1250^2 < 154*101^2, D < B2 < B1. Thus both individual upper bounds hold at this pair while their proposed relative order fails.

Complete Lean statement: theorem exact_values_and_bounds :     renyiRZ (1/2) (1/2) 2 rhohat sigmahat =       4 * (1 - Real.sqrt ((2117 + 288 * Real.sqrt 2) / 3125)) ∧     B2 (1/2) 1 rhohat sigmahat = 2 - 20 / Real.sqrt 154 ∧     tsallis (1/2) rhohat sigmahat = 48/125 ∧     B2 (1/2) 1 rhohat sigmahat < 2/5 ∧     (2/5:ℝ) < renyiRZ (1/2) (1/2) 2 rhohat sigmahat ∧     tsallis (1/2) rhohat sigmahat < B2 (1/2) 1 rhohat sigmahat ∧     B2 (1/2) 1 rhohat sigmahat < renyiRZ (1/2) (1/2) 2 rhohat sigmahat

**Definition 1.11 (The old ordering restricted to this nondiagonal setting).**

Lean statement: `D5/S3/Divergence/MaityFuruichiDuttaNondiagonalSupplement.claim`

*Formalization.* `D5/S3/Divergence/MaityFuruichiDuttaNondiagonalSupplement.claim` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This is the already refuted comparison B1 <= B2, restricted to positive definite noncommuting qubit states with trace one and nonzero (0,1) entries in the same basis, at the displayed source parameters. It introduces no new conjecture.

Complete Lean statement: def claim : Prop := ∀ ρ σ : Matrix (Fin 2) (Fin 2) ℂ,   ρ.PosDef → ρ.trace = 1 → σ.PosDef → σ.trace = 1 → ρ * σ ≠ σ * ρ →   ρ 0 1 ≠ 0 → σ 0 1 ≠ 0 →   renyiRZ (1/2) (1/2) 2 ρ σ ≤ B2 (1/2) 1 ρ σ

**Theorem 1.12 (The same reversal persists with both states nondiagonal).**

Lean statement: `D5/S3/Divergence/MaityFuruichiDuttaNondiagonalSupplement.result`

*Proof.* Machine-checked in Lean as `D5/S3/Divergence/MaityFuruichiDuttaNondiagonalSupplement.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The explicit states meet every hypothesis of the restricted comparison, and their strict bound reversal contradicts its conclusion. This says nothing about other parameter choices or the source's commuting comparison.

Complete Lean statement: theorem result : ¬ claim

## References

- Truth anchor: `D5/S3/Divergence/MaityFuruichiDuttaNondiagonalSupplement.U`
- Truth anchor: `D5/S3/Divergence/MaityFuruichiDuttaNondiagonalSupplement.characteristic_polynomials`
- Truth anchor: `D5/S3/Divergence/MaityFuruichiDuttaNondiagonalSupplement.claim`
- Truth anchor: `D5/S3/Divergence/MaityFuruichiDuttaNondiagonalSupplement.common_orthogonal_conjugation`
- Truth anchor: `D5/S3/Divergence/MaityFuruichiDuttaNondiagonalSupplement.exact_values_and_bounds`
- Truth anchor: `D5/S3/Divergence/MaityFuruichiDuttaNondiagonalSupplement.functions_unitary`
- Truth anchor: `D5/S3/Divergence/MaityFuruichiDuttaNondiagonalSupplement.matrix_facts`
- Truth anchor: `D5/S3/Divergence/MaityFuruichiDuttaNondiagonalSupplement.parameter_conditions`
- Truth anchor: `D5/S3/Divergence/MaityFuruichiDuttaNondiagonalSupplement.result`
- Truth anchor: `D5/S3/Divergence/MaityFuruichiDuttaNondiagonalSupplement.rhohat`
- Truth anchor: `D5/S3/Divergence/MaityFuruichiDuttaNondiagonalSupplement.sigmahat`
- Truth anchor: `D5/S3/Divergence/MaityFuruichiDuttaNondiagonalSupplement.spectral_quantities`
- Dependency: [D5/S3/Divergence/MaityFuruichiDuttaOrderingRefutation](MaityFuruichiDuttaOrderingRefutation.md)
