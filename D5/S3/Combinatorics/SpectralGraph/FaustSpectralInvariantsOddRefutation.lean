/- GID: D5/S3/Combinatorics/SpectralGraph/FaustSpectralInvariantsOddRefutation
   generality: I
   mirror-B: D5/B/S3/Combinatorics/SpectralGraph/FaustSpectralInvariantsOddRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Combinatorics/SpectralGraph/FaustSpectralInvariantsOddRefutation.claim; result=D5/S3/Combinatorics/SpectralGraph/FaustSpectralInvariantsOddRefutation.result; claim=D5/S3/Combinatorics/SpectralGraph/FaustSpectralInvariantsOddRefutation.claim
   digest: A nonzero fifteen-site point has equal Jacobian columns. -/

/-
proof_shape: content: eval_pderiv_subst, floquet_transfer, floquet15_transfer,
  characteristic_equal, membership, specialized_derivative_zero, specialized_derivative_five,
  jacobian_columns, singular, result.
proof_shape: bind-only: floquet_map, zeta_map, membership_of_zeta_map_zero, eval_specialized,
  block_trace, block_det, block_trace_equal, trace_cube_eq, periodic_product, free_product,
  membership_from_characteristic, pPrime_subst, shift_adjacent, floquet_shift,
  universalZeta_rename_of_invariance, universalZeta_shift, universalEquation_rename,
  universalEquation_shift, potential_shift, eval_pderiv_shift.
Definition rows have proof_shape: bind-only; they introduce the data used in the proofs.
escape_witness: none.
admission_basis: open-problem-resolution (#19188; Refuted).
Direct frozen dependencies: D5/S0/Observation/MatrixTracePowerSum.trace_pow_add_two;
sha256:c3a059dba6dacff2daf43a6483f3e2bb7036930561a43d038fdbb8225d03adff.
All helper theorems are private and consumed by result.
The public result is the designated refutation result (`basis=refutes`) and is exempt
from four-slot escape registration (CLAUDE.md §3.9).
The public definitions use the expressions recorded in #19188. Their namespace follows
the module path. Regularity means a nonzero Jacobian determinant; no separate
local-algebra multiplicity theorem is asserted.
The Floquet expression is retained verbatim from #19188; the private consumed
floquet_transfer proof identifies its polynomial matrix with negative cycleDiag
and applies the cyclic determinant identity.
-/

import D5.S3.Combinatorics.SpectralGraph.CyclicTridiagonalTransferTrace
import D5.S0.Observation.MatrixTracePowerSum
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Analysis.Complex.Polynomial.Basic

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 200000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

section

/-! Binding conventions for M. Faust, L. Friedman, G. O'Malley, R. Ramos and A. Sharma, "Algebraic Properties of the
Ideal of Spectral Invariants for the Discrete Laplacian", arXiv:2602.08304v1, Section 2 (the Floquet matrix `L_V = L_V(1)`
and `D_V(λ)`), Section 4 (the specialization `U` and the ideal `I' = ⟨p'_1, …, p'_m⟩`) and Section 5, Conjecture 3 (odd
clause). Indices are `0`-based. -/

namespace D5.S3.Combinatorics.SpectralGraph.FaustSpectralInvariantsOddRefutation

open MvPolynomial

/-- The Floquet matrix `L_V = L_V(1)` of the discrete Laplacian on the `n`-cycle with potential `V`: diagonal `V`,
entries `1` between cyclically adjacent sites (the corner entries `z^{-1}` and `z` at `z = 1`), and `0` elsewhere. -/
def floquetMatrix {R : Type*} [CommRing R] (n : ℕ) (V : Fin n → R) : Matrix (Fin n) (Fin n) R :=
  fun i j => if i = j then V i else if (i.val + 1) % n = j.val ∨ (j.val + 1) % n = i.val then (1 : R) else (0 : R)

/-- `D_V(λ)`, the characteristic polynomial `det(L_V − λ I)` of the Floquet matrix. -/
noncomputable def floquetCharPoly {R : Type*} [CommRing R] (n : ℕ) (V : Fin n → R) : Polynomial R :=
  ((floquetMatrix n V).map (Polynomial.C (R := R)) - (Polynomial.X : Polynomial R) • (1 : Matrix (Fin n) (Fin n) (Polynomial R))).det

/-- The specialized potential `U = (u_1, …, u_m, 0, −u_m, …, −u_1)` for `n = 2m + 1`, with indeterminates `u_j`. -/
noncomputable def specializedPotential (m : ℕ) : Fin (2 * m + 1) → MvPolynomial (Fin m) ℂ := fun j =>
  if h : j.val < m then X ⟨j.val, h⟩
  else if h' : j.val = m then 0
  else -X ⟨2 * m - j.val, by omega⟩

/-- `ζ_U = D_U(λ) − D_𝟎(λ)` for the specialized potential. -/
noncomputable def zeta (m : ℕ) : Polynomial (MvPolynomial (Fin m) ℂ) :=
  floquetCharPoly (2 * m + 1) (specializedPotential m) - floquetCharPoly (2 * m + 1) (fun _ => 0)

/-- `p'_k = (−1)^{n+k} [λ^{n−2k}] ζ_U` with `n = 2m + 1`, for `k = 1, …, m`. -/
noncomputable def pPrime (m : ℕ) (k : ℕ) : MvPolynomial (Fin m) ℂ :=
  (-1) ^ (2 * m + 1 + k) * (zeta m).coeff (2 * m + 1 - 2 * k)

/-- A point of the zero set `V(I')`. -/
def InVariety (m : ℕ) (u : Fin m → ℂ) : Prop :=
  ∀ k ∈ Finset.Icc 1 m, eval u (pPrime m k) = 0

/-- The Jacobian matrix `(∂p'_{k+1}/∂u_j)(u)` of the generators of `I'`. -/
noncomputable def jacobianAt (m : ℕ) (u : Fin m → ℂ) : Matrix (Fin m) (Fin m) ℂ :=
  fun k j => eval u (pderiv j (pPrime m (k.val + 1)))

/-- A point of `V(I')` is regular when it has multiplicity one with respect to the defining ideal `I'` (Section 3 counts
multiplicity for the defining ideal, not its radical). For the `m` generators of `I'` in `m` variables this is the
invertibility of their Jacobian matrix at the point. -/
def IsRegularPoint (m : ℕ) (u : Fin m → ℂ) : Prop :=
  (jacobianAt m u).det ≠ 0

/-- Conjecture 3, odd clause: "When q is odd, then V(I') has only regular nonzero points", for every odd `q = 2m + 1 > 3`. -/
def claim : Prop :=
  ∀ m : ℕ, 2 ≤ m → ∀ u : Fin m → ℂ, u ≠ 0 → InVariety m u → IsRegularPoint m u

end D5.S3.Combinatorics.SpectralGraph.FaustSpectralInvariantsOddRefutation
end

section

open MvPolynomial
noncomputable section
namespace D5.S3.Combinatorics.SpectralGraph.FaustSpectralInvariantsOddRefutation

variable {R σ τ : Type*} [CommRing R] [Fintype σ] [DecidableEq σ]

private theorem eval_pderiv_subst (g : σ → MvPolynomial τ R) (u : τ → R)
    (j : τ) (p : MvPolynomial σ R) :
    eval u (pderiv j (eval₂Hom C g p)) =
      ∑ i : σ, eval (fun k => eval u (g k)) (pderiv i p) *
        eval u (pderiv j (g i)) := by
    induction p using MvPolynomial.induction_on with
    | C r => simp [pderiv_C]
    | add p q hp hq =>
        simp only [map_add, hp, hq, add_mul, Finset.sum_add_distrib]
    | mul_X p k hp =>
        have hpi (i : σ) :
            eval (fun k => eval u (g k))
              (Pi.single (M := fun _ : σ => MvPolynomial σ R) i 1 k) =
                if k = i then 1 else 0 := by
          by_cases h : k = i <;> simp [Pi.single_apply, h]
        simp only [map_mul, eval₂Hom_X', pderiv_mul, map_add,
          pderiv_X, eval_X, hpi]
        rw [hp]
        rw [show eval u (eval₂Hom C g p) = eval (fun k => eval u (g k)) p from (eval_assoc g u p).symm]
        simp only [add_mul, Finset.sum_add_distrib, mul_ite, mul_one, mul_zero, zero_mul,
          ite_mul, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
        rw [Finset.sum_mul]
        congr 1
        apply Finset.sum_congr rfl
        intro i hi
        ring

end D5.S3.Combinatorics.SpectralGraph.FaustSpectralInvariantsOddRefutation
end
end

section

open MvPolynomial
noncomputable section
namespace D5.S3.Combinatorics.SpectralGraph.FaustSpectralInvariantsOddRefutation

variable {R S : Type*} [CommRing R] [CommRing S]

private theorem floquet_map (f : R →+* S) (n : ℕ) (V : Fin n → R) :
    (floquetCharPoly n V).map f = floquetCharPoly n (fun i => f (V i)) := by
    unfold floquetCharPoly
    rw [← Polynomial.coe_mapRingHom, RingHom.map_det]
    congr 1
    ext i j : 2
    by_cases hij : i = j
    · subst j
      simp [floquetMatrix, Matrix.map_apply, Matrix.sub_apply, Matrix.smul_apply,
        Matrix.one_apply, Polynomial.map_sub]
    · by_cases ha : (i.val+1)%n = j.val ∨ (j.val+1)%n = i.val
      all_goals simp [floquetMatrix, Matrix.map_apply, Matrix.sub_apply, Matrix.smul_apply,
        Matrix.one_apply, hij, ha]

end D5.S3.Combinatorics.SpectralGraph.FaustSpectralInvariantsOddRefutation
end
end
set_option maxHeartbeats 300000
set_option maxRecDepth 10000
noncomputable section
open scoped BigOperators Matrix
open Polynomial
namespace D5.S3.Combinatorics.SpectralGraph.FaustSpectralInvariantsOddRefutation
open D5.S3.Combinatorics.SpectralGraph.CyclicTridiagonalTransferTrace
private theorem floquet_transfer {R : Type*} [CommRing R] (n : ℕ) (V : Fin (n+3) → R) :
    floquetCharPoly (n+3) V =
      (-1 : Polynomial R)^(n+3) *
        ((evolution (fun j => (Polynomial.X : Polynomial R) -
          Polynomial.C (V ⟨j % (n+3), Nat.mod_lt _ (by omega)⟩)) (n+3)).trace - 2) := by
    let d : ℕ → Polynomial R := fun j => Polynomial.X - Polynomial.C (V ⟨j % (n+3), Nat.mod_lt _ (by omega)⟩)
    have hm : (floquetMatrix (n+3) V).map Polynomial.C -
        (Polynomial.X : Polynomial R) • (1 : Matrix (Fin (n+3)) (Fin (n+3)) (Polynomial R)) =
        -cycleDiag (n+3) d := by
      ext i j : 2
      by_cases hij : i = j
      · subst j
        simp [floquetMatrix, cycleDiag_apply, d, Matrix.map_apply, Matrix.sub_apply,
          Matrix.smul_apply, Matrix.one_apply, Nat.mod_eq_of_lt i.isLt]
      · simp only [Matrix.map_apply, Matrix.sub_apply, Matrix.smul_apply,
          Matrix.one_apply, Matrix.neg_apply, floquetMatrix, cycleDiag_apply, hij, ite_false,
          smul_eq_mul, mul_zero, sub_zero]
        split_ifs <;> simp
    change _ = (-1 : Polynomial R)^(n+3) * ((evolution d (n+3)).trace - 2)
    calc
      floquetCharPoly (n+3) V = (-cycleDiag (n+3) d).det := congrArg Matrix.det hm
      _ = (-1 : Polynomial R)^(n+3) * (cycleDiag (n+3) d).det := by
        rw [Matrix.det_neg, Fintype.card_fin]
      _ = _ := congrArg (fun x => (-1 : Polynomial R)^(n+3) * x)
        (cycleDiag_det_transfer n d)


private lemma zeta_map (m : ℕ) (u : Fin m → ℂ) :
    (zeta m).map (MvPolynomial.eval u) =
      floquetCharPoly (2*m+1) (fun j => MvPolynomial.eval u (specializedPotential m j)) -
        floquetCharPoly (2*m+1) (fun _ : Fin (2*m+1) => (0 : ℂ)) := by
    unfold zeta
    rw [Polynomial.map_sub]
    exact congrArg₂ (· - ·)
      (floquet_map (MvPolynomial.eval u) _ _)
      (by simpa only [map_zero] using floquet_map (MvPolynomial.eval u) (2*m+1) (fun _ => 0))

private lemma membership_of_zeta_map_zero (m : ℕ) (u : Fin m → ℂ)
    (hz : (zeta m).map (MvPolynomial.eval u) = 0) : InVariety m u := by
    intro k hk
    have hc := congrArg (fun p : Polynomial ℂ => p.coeff (2*m+1-2*k)) hz
    simp only [Polynomial.coeff_map, Polynomial.coeff_zero] at hc
    simp only [pPrime, map_mul, hc, mul_zero]

end D5.S3.Combinatorics.SpectralGraph.FaustSpectralInvariantsOddRefutation
end


set_option backward.isDefEq.respectTransparency true

noncomputable section
open scoped BigOperators Matrix
open Polynomial
namespace D5.S3.Combinatorics.SpectralGraph.FaustSpectralInvariantsOddRefutation
open D5.S3.Combinatorics.SpectralGraph.CyclicTridiagonalTransferTrace
attribute [local irreducible] floquetCharPoly Matrix.det

private theorem floquet15_transfer {R : Type*} [CommRing R] (V : Fin 15 → R) :
    floquetCharPoly 15 V =
      -((evolution (fun j => (Polynomial.X : Polynomial R) -
          Polynomial.C (V ⟨j % 15, by omega⟩)) 15).trace - 2) := by
  have h := floquet_transfer 12 V
  have hs : (-1 : Polynomial R)^15 = -1 := by norm_num
  exact h.trans ((congrArg (fun c : Polynomial R => c *
    ((evolution (fun j => (Polynomial.X : Polynomial R) -
      Polynomial.C (V ⟨j % 15, by omega⟩)) 15).trace - 2)) hs).trans (neg_one_mul _))

private def point (a : ℂ) : Fin 7 → ℂ := ![a, Complex.I*a, 0, -Complex.I*a, -a, a, Complex.I*a]

private def potential (a b : ℂ) : Fin 15 → ℂ :=
  ![a,b,0,-b,-a,a,b,0,-b,-a,a,b,0,-b,-a]

private lemma eval_specialized (a : ℂ) :
    (fun j => MvPolynomial.eval (point a) (specializedPotential 7 j)) =
      potential a (Complex.I*a) := by
    funext j
    fin_cases j <;> simp [specializedPotential, point, potential]

private def block (a b : ℂ) : Matrix (Fin 2) (Fin 2) (Polynomial ℂ) :=
  evolution (fun j => Polynomial.X - Polynomial.C
    ((![a, b, 0, -b, -a] : Fin 5 → ℂ) ⟨j % 5, by omega⟩)) 5

private lemma block_trace (a b : ℂ) :
    (block a b).trace = Polynomial.X^5-Polynomial.C (5+a^2+b^2)*Polynomial.X^3+
      Polynomial.C (5+a^2*b^2+2*a^2-2*a*b+b^2)*Polynomial.X := by
    norm_num [block, evolution, transfer, Matrix.trace_fin_two, Matrix.mul_apply,
      Fin.sum_univ_two]
    simp only [map_ofNat]
    ring

private lemma block_det (a b : ℂ) : (block a b).det = 1 := by
    exact evolution_det _ _

private lemma block_trace_equal (a : ℂ) (ha : a^2 = 1-2*Complex.I) :
    (block a (Complex.I*a)).trace = (block 0 0).trace := by
    have hb : (Complex.I*a)^2 = -a^2 := by rw [mul_pow, Complex.I_sq]; ring
    have h1 : a^2+(Complex.I*a)^2 = 0 := add_eq_zero_iff_eq_neg'.mpr hb
    have h2 : a^2*(Complex.I*a)^2+2*a^2-2*a*(Complex.I*a)+(Complex.I*a)^2 = 0 := by
      rw [hb]
      linear_combination -a^2 * ha
    rw [block_trace, block_trace]
    have hc1 : 5+a^2+(Complex.I*a)^2 = (5:ℂ) := by linear_combination h1
    have hc2 : 5+a^2*(Complex.I*a)^2+2*a^2-2*a*(Complex.I*a)+(Complex.I*a)^2 = (5:ℂ) := by
      linear_combination h2
    rw [hc1, hc2]
    norm_num

private lemma trace_cube_eq {R : Type*} [CommRing R] (A B : Matrix (Fin 2) (Fin 2) R)
    (hA : A.det = 1) (hB : B.det = 1) (ht : A.trace = B.trace) :
    (A^3).trace = (B^3).trace := by
    rw [show 3 = 1+2 from rfl,
      D5.S0.Observation.MatrixTracePowerSum.trace_pow_add_two A 1,
      D5.S0.Observation.MatrixTracePowerSum.trace_pow_add_two B 1]
    rw [show 1+1 = 0+2 from rfl,
      D5.S0.Observation.MatrixTracePowerSum.trace_pow_add_two A 0,
      D5.S0.Observation.MatrixTracePowerSum.trace_pow_add_two B 0]
    simp [hA, hB, ht]

private lemma periodic_product (a b : ℂ) :
    evolution (fun j => (Polynomial.X : Polynomial ℂ)-Polynomial.C (potential a b ⟨j%15, by omega⟩)) 15 =
      block a b ^ 3 := by
    simp only [block, evolution, potential]
    norm_num
    simp only [pow_succ, pow_zero, mul_one]
    noncomm_ring

private lemma free_product :
    evolution (fun _ => (Polynomial.X : Polynomial ℂ)) 15 = block 0 0 ^ 3 := by
    have hpot : potential 0 0 = fun _ => 0 := by
      funext i
      fin_cases i <;> simp [potential]
    simpa [hpot] using periodic_product 0 0

private lemma characteristic_equal (a : ℂ) (ha : a^2 = 1-2*Complex.I) :
    floquetCharPoly 15 (potential a (Complex.I*a)) =
      floquetCharPoly 15 (fun _ : Fin 15 => (0:ℂ)) := by
    rw [floquet15_transfer, floquet15_transfer, periodic_product]
    simp only [map_zero, sub_zero]
    rw [free_product]
    exact congrArg (fun x : Polynomial ℂ => -(x-2))
      (trace_cube_eq _ _ (block_det _ _) (block_det _ _) (block_trace_equal a ha))


end D5.S3.Combinatorics.SpectralGraph.FaustSpectralInvariantsOddRefutation
end
set_option maxRecDepth 200
noncomputable section
namespace D5.S3.Combinatorics.SpectralGraph.FaustSpectralInvariantsOddRefutation
attribute [local irreducible] floquetCharPoly Matrix.det

private lemma membership_from_characteristic (m : ℕ) (u : Fin m → ℂ)
    (V : Fin (2*m+1) → ℂ)
    (hV : (fun j => MvPolynomial.eval u (specializedPotential m j)) = V)
    (hD : floquetCharPoly (2*m+1) V = floquetCharPoly (2*m+1) (fun _ => (0:ℂ))) :
    InVariety m u := by
    apply membership_of_zeta_map_zero m u
    calc
      (zeta m).map (MvPolynomial.eval u) =
          floquetCharPoly (2*m+1) (fun j => MvPolynomial.eval u (specializedPotential m j)) -
            floquetCharPoly (2*m+1) (fun _ => (0:ℂ)) := zeta_map m u
      _ = floquetCharPoly (2*m+1) V -
            floquetCharPoly (2*m+1) (fun _ => (0:ℂ)) :=
          congrArg (fun W : Fin (2*m+1) → ℂ => floquetCharPoly (2*m+1) W -
            floquetCharPoly (2*m+1) (fun _ => (0:ℂ))) hV
      _ = 0 := sub_eq_zero.mpr hD


private lemma membership (a : ℂ) (ha : a^2 = 1-2*Complex.I) : InVariety 7 (point a) := by
  exact membership_from_characteristic 7 (point a) (potential a (Complex.I*a))
    (eval_specialized a) (characteristic_equal a ha)

end D5.S3.Combinatorics.SpectralGraph.FaustSpectralInvariantsOddRefutation
end


set_option maxRecDepth 500

noncomputable section
open scoped BigOperators Matrix
open MvPolynomial
namespace D5.S3.Combinatorics.SpectralGraph.FaustSpectralInvariantsOddRefutation
attribute [local irreducible] floquetCharPoly Matrix.det

private def universalZeta (n : ℕ) : Polynomial (MvPolynomial (Fin n) ℂ) :=
  floquetCharPoly n (fun j => X j) - floquetCharPoly n (fun _ => 0)

private def universalEquation (m k : ℕ) : MvPolynomial (Fin (2*m+1)) ℂ :=
  (-1)^(2*m+1+k) * (universalZeta (2*m+1)).coeff (2*m+1-2*k)

private lemma pPrime_subst (m k : ℕ) :
    pPrime m k = eval₂Hom C (specializedPotential m) (universalEquation m k) := by
  let f := eval₂Hom C (specializedPotential m)
  have hz : (universalZeta (2*m+1)).map f = zeta m := by
    rw [universalZeta, Polynomial.map_sub, floquet_map, floquet_map]
    simp [f, zeta]
  have hc := congrArg (fun p => p.coeff (2*m+1-2*k)) hz
  simp only [Polynomial.coeff_map] at hc
  simp only [universalEquation, map_mul, map_pow, map_neg, map_one, pPrime]
  rw [hc]


private lemma shift_adjacent (i j : Fin 15) :
    ((((Equiv.addRight (5 : Fin 15)) i).val+1)%15 = ((Equiv.addRight (5 : Fin 15)) j).val ∨ (((Equiv.addRight (5 : Fin 15)) j).val+1)%15 = ((Equiv.addRight (5 : Fin 15)) i).val) ↔
    ((i.val+1)%15 = j.val ∨ (j.val+1)%15 = i.val) := by
  have h : ∀ i j : Fin 15,
      ((((Equiv.addRight (5 : Fin 15)) i).val+1)%15 = ((Equiv.addRight (5 : Fin 15)) j).val ∨ (((Equiv.addRight (5 : Fin 15)) j).val+1)%15 = ((Equiv.addRight (5 : Fin 15)) i).val) ↔
      ((i.val+1)%15 = j.val ∨ (j.val+1)%15 = i.val) := by decide +kernel
  exact h i j

private lemma floquet_shift {R : Type*} [CommRing R] (V : Fin 15 → R) :
    floquetCharPoly 15 (fun i => V ((Equiv.addRight (5 : Fin 15)) i)) = floquetCharPoly 15 V := by
  unfold floquetCharPoly
  have hm : (floquetMatrix 15 (fun i => V ((Equiv.addRight (5 : Fin 15)) i))).map Polynomial.C -
      (Polynomial.X : Polynomial R) • (1 : Matrix (Fin 15) (Fin 15) (Polynomial R)) =
      ((floquetMatrix 15 V).map Polynomial.C -
          (Polynomial.X : Polynomial R) • (1 : Matrix (Fin 15) (Fin 15) (Polynomial R))).submatrix (Equiv.addRight (5 : Fin 15)) (Equiv.addRight (5 : Fin 15)) := by
    ext i j : 2
    simp only [Matrix.submatrix_apply, Matrix.map_apply, Matrix.sub_apply,
      Matrix.smul_apply, Matrix.one_apply, floquetMatrix, (Equiv.addRight (5 : Fin 15)).injective.eq_iff,
      shift_adjacent]
  exact (congrArg Matrix.det hm).trans (Matrix.det_submatrix_equiv_self (Equiv.addRight (5 : Fin 15)) _)

private lemma universalZeta_rename_of_invariance (n : ℕ) (e : Fin n → Fin n)
    (h : ∀ V : Fin n → MvPolynomial (Fin n) ℂ,
      floquetCharPoly n (fun i => V (e i)) = floquetCharPoly n V) :
    (universalZeta n).map (rename e).toRingHom = universalZeta n := by
  unfold universalZeta
  rw [Polynomial.map_sub, floquet_map, floquet_map]
  have hx (i : Fin n) : (rename e).toRingHom (X i) = (X (e i) : MvPolynomial (Fin n) ℂ) :=
    rename_X e i
  simp only [hx, map_zero]
  exact congrArg (fun z => z - floquetCharPoly n (fun _ => (0 : MvPolynomial (Fin n) ℂ)))
    (h (fun i => X i))


private lemma universalZeta_shift :
    (universalZeta 15).map (rename (Equiv.addRight (5 : Fin 15))).toRingHom = universalZeta 15 := by
  exact universalZeta_rename_of_invariance 15 (Equiv.addRight (5 : Fin 15)) (fun V => floquet_shift V)

private lemma universalEquation_rename (m : ℕ) (e : Fin (2*m+1) → Fin (2*m+1))
    (hz : (universalZeta (2*m+1)).map (rename e).toRingHom = universalZeta (2*m+1))
    (k : ℕ) : rename e (universalEquation m k) = universalEquation m k := by
  have hc := congrArg (fun p => p.coeff (2*m+1-2*k)) hz
  simp only [Polynomial.coeff_map] at hc
  simp only [universalEquation, map_mul, map_pow, map_neg, map_one]
  exact congrArg (fun z : MvPolynomial (Fin (2*m+1)) ℂ => (-1)^(2*m+1+k)*z) hc


private lemma universalEquation_shift (k : ℕ) :
    rename (Equiv.addRight (5 : Fin 15)) (universalEquation 7 k) = universalEquation 7 k := by
  exact universalEquation_rename 7 (Equiv.addRight (5 : Fin 15)) universalZeta_shift k

private lemma potential_shift (a b : ℂ) :
    (fun i => potential a b ((Equiv.addRight (5 : Fin 15)) i)) = potential a b := by
  exact List.ofFn_inj.mp rfl

private lemma eval_pderiv_shift (p : MvPolynomial (Fin 15) ℂ) (hp : rename (Equiv.addRight (5 : Fin 15)) p = p)
    (a b : ℂ) (j : Fin 15) :
    eval (potential a b) (pderiv ((Equiv.addRight (5 : Fin 15)) j) p) = eval (potential a b) (pderiv j p) := by
  have h := congrArg (eval (potential a b)) (pderiv_rename (Equiv.addRight (5 : Fin 15)).injective j p)
  rw [hp] at h
  simpa only [eval_rename, Function.comp_def, potential_shift] using h

private lemma specialized_derivative_zero (p : MvPolynomial (Fin 15) ℂ) (a : ℂ) :
    eval (point a) (pderiv (0 : Fin 7) (eval₂Hom C (specializedPotential 7) p)) =
      eval (potential a (Complex.I*a)) (pderiv 0 p) -
        eval (potential a (Complex.I*a)) (pderiv 14 p) := by
  rw [eval_pderiv_subst, eval_specialized]
  simp [Fin.sum_univ_succ, specializedPotential, pderiv_C, Pi.single_apply, sub_eq_add_neg]

private lemma specialized_derivative_five (p : MvPolynomial (Fin 15) ℂ) (a : ℂ) :
    eval (point a) (pderiv (5 : Fin 7) (eval₂Hom C (specializedPotential 7) p)) =
      eval (potential a (Complex.I*a)) (pderiv 5 p) -
        eval (potential a (Complex.I*a)) (pderiv 9 p) := by
  rw [eval_pderiv_subst, eval_specialized]
  simp [Fin.sum_univ_succ, specializedPotential, pderiv_C, Pi.single_apply, sub_eq_add_neg]

/-- The period-five fixed point of the fifteen-cycle has equal specialized Jacobian columns. -/
private theorem jacobian_columns (a : ℂ) (k : Fin 7) :
    jacobianAt 7 (point a) k 0 = jacobianAt 7 (point a) k 5 := by
  simp only [jacobianAt, pPrime_subst, specialized_derivative_zero, specialized_derivative_five]
  have h0 := eval_pderiv_shift (universalEquation 7 (k.val+1))
    (universalEquation_shift _) a (Complex.I*a) 0
  have h9 := eval_pderiv_shift (universalEquation 7 (k.val+1))
    (universalEquation_shift _) a (Complex.I*a) 9
  exact congrArg₂ (· - ·) h0.symm h9

private lemma singular (a : ℂ) : (jacobianAt 7 (point a)).det = 0 := by
  exact Matrix.det_zero_of_column_eq (by decide : (0:Fin 7) ≠ 5) (jacobian_columns a)

end D5.S3.Combinatorics.SpectralGraph.FaustSpectralInvariantsOddRefutation

end


namespace D5.S3.Combinatorics.SpectralGraph.FaustSpectralInvariantsOddRefutation
attribute [local irreducible] floquetCharPoly Matrix.det

theorem result : ¬ claim := by
  obtain ⟨a, ha⟩ := IsAlgClosed.exists_pow_nat_eq (1-2*Complex.I) (by norm_num : 0 < 2)
  have hane : a ≠ 0 := by
    intro h
    have he := congrArg Complex.re ha
    simp [h] at he
  have hu : point a ≠ 0 := by
    intro h
    have he := congrFun h 0
    simp [point] at he
    exact hane he
  intro h
  exact h 7 (by norm_num) (point a) hu (membership a ha) (singular a)

end D5.S3.Combinatorics.SpectralGraph.FaustSpectralInvariantsOddRefutation
