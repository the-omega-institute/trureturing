/- GID: D5/S3/VertexAlgebra/Lattice/Orbifold/P48qMovingPairIterate
   generality: I
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The moving-pair iterate comparison in native current and binomial coordinates. -/

import D5.S3.VertexAlgebra.Lattice.Orbifold.ThirdTwistedQuadratic
import D5.S3.VertexAlgebra.Lattice.Orbifold.ThirdEigenspacePairingDraft
import D5.S3.VertexAlgebra.LatticeActualConformalState

/-! Bakalov–Kac (3.13) at n = -1 for a normalized order-three moving pair. -/

set_option autoImplicit false

noncomputable section

namespace D5.S3.VertexAlgebra.Lattice.Orbifold.ThirdTwistedIterate

open LatticeGeneratingFieldLocality LatticeAllStateField LatticeAllStateReconstruction
open LatticeActualConformalState LatticeSugawaraCurrents
open ThirdCoverIntegerFactor ThirdCoverComplement ThirdTwistedQuadratic
open scoped BigOperators VertexOperator

/-- The actual lattice current state in a complex coefficient direction. -/
def currentAlong (D : LatticeData) (u : Fin D.rank → ℂ) : Carrier D :=
  ∑ i, u i • currentState D i

private theorem basis_current_product (D : LatticeData) (i j : Fin D.rank)
    (n : ℤ) (hn : 0 ≤ n) :
    mu D (currentState D i) n (currentState D j) =
      if n = 1 then (D.G i j : ℂ) • vacuum D else 0 := by
  have hz := stateField_creativity D (currentState D i) n hn
  rw [current_state_field, neutralField_ncoeff] at hz
  have hc := current_state_creation D j
  rw [neutralField_ncoeff] at hc
  have h := LinearMap.congr_fun (neutralMode_heisenberg D i j n (-1)) (vacuum D)
  simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply,
    Module.End.one_apply, hz, hc, map_zero, sub_zero] at h
  rw [mu, current_state_field, neutralField_ncoeff]
  by_cases hn1 : n = 1
  · subst n
    simpa using h
  · simpa [hn1, show n + -1 ≠ 0 by omega] using h

private theorem current_product (D : LatticeData) (u v : Fin D.rank → ℂ)
    (n : ℤ) (hn : 0 ≤ n) :
    mu D (currentAlong D u) n (currentAlong D v) =
      if n = 1 then ((D.G.map (Int.castRingHom ℂ)).toBilin' u v) • vacuum D else 0 := by
  have hcurrent : ((Y D (currentAlong D u))[[n]]) =
      ∑ i, u i • ((Y D (currentState D i))[[n]]) := by
    simp only [currentAlong, map_sum, map_smul, Finset.sum_apply, Pi.smul_apply]
  rw [mu, hcurrent]
  simp only [currentAlong, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul]
  have hb (i j : Fin D.rank) : ((Y D (currentState D i))[[n]]) (currentState D j) =
      if n = 1 then (D.G i j : ℂ) • vacuum D else 0 :=
    basis_current_product D i j n hn
  simp_rw [hb]
  by_cases h : n = 1
  · simp only [h, ite_true, Matrix.toBilin'_apply, Matrix.map_apply]
    simp_rw [Finset.smul_sum, Finset.sum_smul, smul_smul]
    conv_lhs => rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
      exact congrArg (fun c : ℂ => c • vacuum D)
        (show v j * (u i * (D.G i j : ℂ)) = u i * (D.G i j : ℂ) * v j
          from mul_comm _ _)
  · simp [h]

/-- The generalized binomial coefficient for the one-third grid in (3.13). -/
def oneThirdBinomial (j : ℕ) : ℂ :=
  (∏ r ∈ Finset.range j, ((1 / 3 : ℂ) - (r : ℂ))) / (j.factorial : ℂ)

private theorem oneThirdBinomial_two : oneThirdBinomial 2 = -1 / 9 := by
  norm_num [oneThirdBinomial, Finset.prod_range_succ, Nat.factorial]

/-- The explicit n = -1 instance of (3.13), coefficient by coefficient.
A native index k denotes exponent -k/3 - 1 in the state field. -/
def nativePairIterate (D : LatticeData) (a b : Carrier D)
    (Ytw : Carrier D →ₗ[ℂ] ℤ → Module.End ℂ ComplementFock) : Prop :=
  ∀ (m : ℤ) (Q : ComplementFock),
    (∑ᶠ k ∈ residue 1,
      (if k < 0 then Ytw a k * Ytw b (3 * m - k)
       else Ytw b (3 * m - k) * Ytw a k) Q) =
      ∑ᶠ j : ℕ, oneThirdBinomial j •
        Ytw (mu D a ((j : ℤ) - 1) b) (3 * (m + 1 - (j : ℤ))) Q

/-- The pair state is the actual untwisted (-1)-product. The twisted inputs
are the two current restrictions, the vacuum field, and (3.13) on this pair. -/
theorem fractionalVirasoro_of_nativeTwistedIterate (D : LatticeData) (u v : Fin D.rank → ℂ)
    (hpair : (D.G.map (Int.castRingHom ℂ)).toBilin' u v = 1)
    (Ytw : Carrier D →ₗ[ℂ] ℤ → Module.End ℂ ComplementFock)
    (hU : ∀ k, Ytw (currentAlong D u) k = if k % 3 = 1 then fractionalCurrent k else 0)
    (hV : ∀ k, Ytw (currentAlong D v) k = if k % 3 = 2 then fractionalCurrent k else 0)
    (hVac : ∀ k, Ytw (vacuum D) k = if k = -3 then 1 else 0)
    (hIterate : nativePairIterate D (currentAlong D u) (currentAlong D v) Ytw)
    (m : ℤ) :
    Ytw (mu D (currentAlong D u) (-1) (currentAlong D v)) (3 * (m + 1)) =
      fractionalVirasoro m := by
  let a := currentAlong D u
  let b := currentAlong D v
  apply LinearMap.ext
  intro Q
  have lhs : orderedCoefficient m Q =
      ∑ᶠ k ∈ residue 1, (if k < 0 then Ytw a k * Ytw b (3 * m - k)
        else Ytw b (3 * m - k) * Ytw a k) Q := by
    refine finsum_mem_congr rfl fun k hk => ?_
    have hl : 3 * m - k ∈ residue 2 := by
      change k % 3 = 1 at hk
      change (3 * m - k) % 3 = 2
      omega
    change k % 3 = 1 at hk
    change (3 * m - k) % 3 = 2 at hl
    simp only [a, b, orderedPair, hU k, hV (3 * m - k), hk, hl, ite_true]
  let term (j : ℕ) := oneThirdBinomial j •
    Ytw (mu D a ((j : ℤ) - 1) b) (3 * (m + 1 - (j : ℤ))) Q
  have hterm : Function.support term ⊆ (↑({0, 2} : Finset ℕ) : Set ℕ) := by
    intro j hj
    by_contra h
    have hj0 : j ≠ 0 := fun hz => h (by simp [hz])
    have hj2 : j ≠ 2 := fun hz => h (by simp [hz])
    apply hj
    dsimp [term, a, b]
    rw [current_product D u v _ (by omega)]
    simp [show (j : ℤ) - 1 ≠ 1 by omega]
  have h := lhs.trans (hIterate m Q)
  change orderedCoefficient m Q = ∑ᶠ j : ℕ, term j at h
  rw [finsum_eq_sum_of_support_subset term hterm, Finset.sum_pair (by decide : (0 : ℕ) ≠ 2)] at h
  have h0 : term 0 = Ytw (mu D a (-1) b) (3 * (m + 1)) Q := by
    simp [term, oneThirdBinomial]
  have h2 : term 2 = -((if m = 0 then (1 / 9 : ℂ) else 0) • Q) := by
    have hproduct : mu D a 1 b = vacuum D := by
      simpa only [a, b, ite_true, hpair, one_smul] using current_product D u v 1 (by decide)
    change oneThirdBinomial 2 • Ytw (mu D a 1 b) (3 * (m + 1 - 2)) Q = _
    rw [oneThirdBinomial_two, hproduct, hVac]
    simp only [show 3 * (m + 1 - 2) = -3 ↔ m = 0 by omega]
    split <;> simp [neg_div, neg_smul]
  rw [fractionalVirasoro_apply_ordered, h, h0, h2]
  abel

open ThirdEigenspacePairing P48qGramCertificateDraft

/-- The comparison for each pair in Nebe's actual normalized moving bases. -/
theorem p48q_fractionalVirasoro_of_twistedIterate {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 3)
    (i : Fin 16) (hSym : ∀ i j, nebeGram i j = nebeGram j i)
    (hEven : ∀ i, Even (nebeGram i i)) :
    let D : LatticeData := ⟨48, nebeGram, hSym, hEven⟩
    let u : Fin D.rank → ℂ := (p48qBasis hζ i : Fin 48 → ℂ)
    let v : Fin D.rank → ℂ := (p48qOppositeBasis hζ i : Fin 48 → ℂ)
    ∀ (Ytw : Carrier D →ₗ[ℂ] ℤ → Module.End ℂ ComplementFock),
      (∀ k, Ytw (currentAlong D u) k = if k % 3 = 1 then fractionalCurrent k else 0) →
      (∀ k, Ytw (currentAlong D v) k = if k % 3 = 2 then fractionalCurrent k else 0) →
      (∀ k, Ytw (vacuum D) k = if k = -3 then 1 else 0) →
      nativePairIterate D (currentAlong D u) (currentAlong D v) Ytw →
      ∀ m : ℤ, Ytw (mu D (currentAlong D u) (-1) (currentAlong D v)) (3 * (m + 1)) =
        fractionalVirasoro m := by
  intro D u v Ytw hU hV hVac hIterate m
  apply fractionalVirasoro_of_nativeTwistedIterate D u v _ Ytw hU hV hVac hIterate
  change p48qForm (p48qBasis hζ i) (p48qOppositeBasis hζ i) = 1
  simpa using p48q_pair_bases hζ i i

#print axioms oneThirdBinomial_two
#print axioms fractionalVirasoro_of_nativeTwistedIterate
#print axioms p48q_fractionalVirasoro_of_twistedIterate

end D5.S3.VertexAlgebra.Lattice.Orbifold.ThirdTwistedIterate
