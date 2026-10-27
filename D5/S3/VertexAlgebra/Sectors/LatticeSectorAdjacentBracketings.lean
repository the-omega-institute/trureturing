/- GID: D5/S3/VertexAlgebra/Sectors/LatticeSectorAdjacentBracketings
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Sectors/LatticeSectorAdjacentBracketings
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual adjacent bracketings share the original numerator in their distinct charts. -/
import D5.S3.VertexAlgebra.Sectors.LatticeSectorFinalLaurentCoefficients
import D5.S3.VertexAlgebra.FormalSeries.ThreeFieldOriginalMiddleInverse
import Batteries.Tactic.OpenPrivate

/-! The middle chamber is b << s << z; the final chamber is x << y << z.
Both expansions retain the original locality order, bounds and infinite
numerator. Supported finite inversions recover the actual middle channel.
The frozen normalization, Jacobi transport and final action are reused,
retaining Bakalov--Kac, Matsuo--Nagatomo and Carnahan attribution. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace D5.S3.VertexAlgebra.LatticeSectorAdjacentBracketings
open LatticeGeneratingFieldLocality LatticeSugawaraCurrents LatticeAllStateField
open LatticeSectorIntertwiner LatticeSectorChannelTransport
open LatticeSectorThreeFieldCommonSeries LatticeSectorThreeFieldInnerIterate
open LatticeSectorSecondCollisionSlice LatticeSectorMiddleCommonNumerator
open LatticeSectorFinalLaurentFiber LatticeSectorSameRLeftCovariance
open SupportedChannelSeries SupportedCollisionSlice SupportedFinalRInjectivity
open ThreeFieldOriginalMiddleInverse ThreeFieldFinalLaurentFiber ThreeFieldFinalLaurentAction
open SupportedMiddleCollision SupportedThreeFieldCollision
open UniformGradedLocalCorrelator UngradedLocalWordSeries
open StateFieldResidueReconstruction (integerBinomial)
open FieldNormalProductLocality (deltaEnd commutator)
open scoped BigOperators VertexOperator
noncomputable section

open private middle_action_is_actual sameR_from_actual_middle from
  D5.S3.VertexAlgebra.Sectors.LatticeSectorSameRLeftCovariance
open private actual_nested_support old_expression_support from
  D5.S3.VertexAlgebra.Sectors.LatticeSectorFinalLaurentCoefficients

/-- Uniform b support and fixed-b s support, both uniform in z. -/
private theorem actual_middle_support (D : LatticeData) (α β γ δ : Charge D)
    (u : Sector D α) (v : Sector D β) (t : Sector D γ) (w : Sector D δ) :
    NestedSupport (fun e => middleIterate D α β γ δ u v t w (e 1) (e 0) (e 2)) := by
  obtain ⟨B, hb⟩ := canonical_truncation D β γ v t
  constructor
  · refine ⟨B.toNat, ?_⟩
    intro b s z h
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]
    unfold middleIterate iterate
    rw [hb (-b - 1) (by omega)]
    simp only [map_zero, Pi.zero_apply, LinearMap.zero_apply]
  · intro b
    obtain ⟨S, hs⟩ := canonical_truncation D α (β + γ) u
      (canonical D β γ v (-b - 1) t)
    refine ⟨S.toNat, ?_⟩
    intro s z h
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]
    unfold middleIterate iterate
    rw [hs (-s - 1) (by omega)]
    simp only [map_zero, Pi.zero_apply, LinearMap.zero_apply]

private theorem cleared_positive (D : LatticeData) (α β γ δ : Charge D)
    (u : Sector D α) (v : Sector D β) (t : Sector D γ) (w : Sector D δ)
    (k : ℕ) (a : Fin 3 → ℕ) (b s z : ℤ) :
    clearedMiddleSlice D α β γ δ u v t w k a b s z =
      positiveClear (a 0)
        (qSlice k (a 1) (a 2) b (middleIterate D α β γ δ u v t w)) s (z - a 0) := by
  classical
  rw [positiveClear_qSlice]
  unfold clearedMiddleSlice
  apply Finset.sum_congr rfl
  intro p hp
  have hpk : p ≤ k := by simpa using Finset.mem_range.mp hp
  apply Finset.sum_congr rfl
  intro h hh
  have hhA : h ≤ a 1 := by simpa using Finset.mem_range.mp hh
  apply congrArg (fun x : Oscillator D =>
    (((-1 : ℂ) ^ p) * (k.choose p : ℂ)) • (((a 1).choose h : ℂ) • x))
  unfold clearIterate positiveClear
  apply Finset.sum_congr rfl
  intro j hj
  apply congrArg (fun x : Oscillator D => ((a 0).choose j : ℂ) • x)
  congr 1 <;> omega

/-- Finite actual descendant support licenses the inverse; native numerator
support removes every artificial tail, including the negative s branch. -/
private theorem actual_middle_short_inverse (D : LatticeData) (α β γ δ : Charge D)
    (u : Sector D α) (v : Sector D β) (t : Sector D γ) (w : Sector D δ)
    (k : ℕ) (a : Fin 3 → ℕ) (P : MvPowerSeries (Fin 3) (Oscillator D))
    (common : ∀ b s z : ℤ, clearedMiddleSlice D α β γ δ u v t w k a b s z =
      signedExtend P ![s, b, z]) (b s z : ℤ) :
    qSlice k (a 1) (a 2) b (middleIterate D α β γ δ u v t w) s z =
      ∑ q ∈ Finset.range (s.toNat + 1), integerBinomial (-(a 0 : ℤ)) q •
        clearedMiddleSlice D α β γ δ u v t w k a b (s - q) (z + q + a 0) := by
  classical
  let F := middleIterate D α β γ δ u v t w
  let H := qSlice k (a 1) (a 2) b F
  have support := actual_middle_support D α β γ δ u v t w
  let nz : ℤ → ℕ := fun r => Classical.choose (support.2 (-r - 1))
  let N : ℕ := (modeFiber k (a 1) b).sup nz
  have lower : ∀ x y : ℤ, x < -(N : ℤ) → H x y = 0 := by
    apply qSlice_lower k (a 1) (a 2) N b F
    intro r hr x y hx
    have bound : nz r ≤ N := Finset.le_sup hr
    dsimp only [nz] at bound
    exact Classical.choose_spec (support.2 (-r - 1)) x y (by omega)
  have native (x y : ℤ) (hx : x < 0) :
      clearedMiddleSlice D α β γ δ u v t w k a b x y = 0 := by
    rw [common]
    apply ite_eq_right
    intro hn
    exact (not_le_of_gt hx) (hn 0)
  have hc (x y : ℤ) : positiveClear (a 0) H x y =
      clearedMiddleSlice D α β γ δ u v t w k a b x (y + a 0) := by
    rw [cleared_positive]
    dsimp only [H, F]
    congr 1
    omega
  have inverse (x y : ℤ) (hx : 0 ≤ x + N) : H x y =
      ∑ q ∈ Finset.range ((x + N).toNat + 1), integerBinomial (-(a 0 : ℤ)) q •
        clearedMiddleSlice D α β γ δ u v t w k a b (x - q) (y + q + a 0) := by
    rw [supported_positive_reconstruction H (a 0) N lower x y hx]
    simp_rw [hc]
  have tail (q : ℕ) (hq : s < q) :
      integerBinomial (-(a 0 : ℤ)) q •
        clearedMiddleSlice D α β γ δ u v t w k a b (s - q) (z + q + a 0) = 0 := by
    rw [native _ _ (by omega), smul_zero]
  change H s z = _
  by_cases hs : 0 ≤ s
  · rw [inverse s z (by omega)]
    symm
    apply Finset.sum_subset
      (Finset.range_mono (by have := Int.toNat_le_toNat (show s ≤ s + N by omega); omega))
    intro q hq hout
    apply tail
    simp only [Finset.mem_range, not_lt] at hout
    omega
  · have zero : H s z = 0 := by
      by_cases hn : 0 ≤ s + N
      · rw [inverse s z hn]
        exact Finset.sum_eq_zero (fun q hq => tail q (by omega))
      · exact lower s z (by omega)
    rw [zero]
    symm
    exact Finset.sum_eq_zero (fun q hq => tail q (by omega))

/-- Two actual chart expansions with one original locality order, statewise
bounds and common numerator, together with their literal polynomial actions. -/
theorem actual_three_field_adjacent_bracketings
    (D : LatticeData) (α β γ : Charge D)
    (u : Sector D α) (v : Sector D β) (t : Sector D γ) :
    let c : Fin 3 → Charge D := ![α, β, γ]
    let states : Fin 3 → Oscillator D := ![u, v, t]
    ∃ k : ℕ,
      (∀ i j : Fin 3, i < j →
        (deltaEnd ^ k) (commutator (labelledFields D c states i)
          (labelledFields D c states j)) = 0) ∧
      ∀ (δ : Charge D) (w : Sector D δ), ∃ a : Fin 3 → ℕ,
        ∃ P : MvPowerSeries (Fin 3) (Oscillator D),
        (∀ (i : Fin 3) (n : ℤ), (a i : ℤ) ≤ n →
          canonical D (c i) δ (states i) n w = 0) ∧
        (∀ e : Exponent 3,
          polynomialAction (clearingPolynomial 3 k) (nestedCanonical D c states δ w 0 1 2)
            (fun i => e i - a i) = signedExtend P e ∧
          polynomialAction (clearingPolynomial 3 k) (nestedCanonical D c states δ w 0 2 1)
            (fun i => e i - a i) = signedExtend P e ∧
          polynomialAction (clearingPolynomial 3 k) (nestedCanonical D c states δ w 1 0 2)
            (fun i => e i - a i) = signedExtend P e ∧
          polynomialAction (clearingPolynomial 3 k) (nestedCanonical D c states δ w 1 2 0)
            (fun i => e i - a i) = signedExtend P e ∧
          polynomialAction (clearingPolynomial 3 k) (nestedCanonical D c states δ w 2 0 1)
            (fun i => e i - a i) = signedExtend P e ∧
          polynomialAction (clearingPolynomial 3 k) (nestedCanonical D c states δ w 2 1 0)
            (fun i => e i - a i) = signedExtend P e) ∧
        (∀ s b z : ℤ,
          middleIterate D α β γ δ u v t w s b z =
            ∑ i ∈ middleFiber k a s b z, middleWeight k a i •
              signedExtend (MvPowerSeries.subst (middleArguments (Oscillator D)) P)
                (middleInput k a s b z i)) ∧
        (∀ e : Exponent 3,
          polynomialAction (middlePolynomial k a)
            (fun e => middleIterate D α β γ δ u v t w (e 0) (e 1) (e 2)) e =
              signedExtend (MvPowerSeries.subst (middleArguments (Oscillator D)) P) e) ∧
        (∀ e : Exponent 3,
          polynomialAction (finalPolynomial k a)
            (fun e => leftNested D α β γ δ u v t w (e 0) (e 1) (e 2)) e =
              signedExtend (MvPowerSeries.subst (triangularArguments (Oscillator D)) P) e) ∧
        (∀ e : Exponent 3,
          leftNested D α β γ δ u v t w (e 0) (e 1) (e 2) =
            laurentCoefficient
              (MvPowerSeries.subst (triangularArguments (Oscillator D)) P) k a e) := by
  classical
  dsimp only
  obtain ⟨k, locality, rest⟩ := actual_three_field_middle_common_numerator D α β γ u v t
  refine ⟨k, locality, ?_⟩
  intro δ w
  obtain ⟨a, P, truncation, six, common⟩ := rest δ w
  let Pm := MvPowerSeries.subst (middleArguments (Oscillator D)) P
  let Pt := MvPowerSeries.subst (triangularArguments (Oscillator D)) P
  have native (b s z : ℤ) (h : s < 0 ∨ b < 0 ∨ z < 0) :
      clearedMiddleSlice D α β γ δ u v t w k a b s z = 0 := by
    rw [common]
    apply ite_eq_right
    intro hn
    rcases h with h | h | h
    · exact (not_le_of_gt h) (hn 0)
    · exact (not_le_of_gt h) (hn 1)
    · exact (not_le_of_gt h) (hn 2)
  have support := actual_middle_support D α β γ δ u v t w
  obtain ⟨T, lower⟩ := support.1
  have reconstruction := original_middle_reconstruction
    (middleIterate D α β γ δ u v t w)
    (clearedMiddleSlice D α β γ δ u v t w k a) k a (max T k) (Nat.le_max_right _ _)
    (fun s b z hb => lower b s z (by omega))
    (actual_middle_short_inverse D α β γ δ u v t w k a Pm common) native
  have middleAction (e : Exponent 3) :
      polynomialAction (middlePolynomial k a)
        (fun e => middleIterate D α β γ δ u v t w (e 0) (e 1) (e 2)) e =
        signedExtend Pm e := by
    have eq := (middle_action_is_actual D α β γ δ u v t w k a
      (e 0) (e 1) (e 2)).trans (common (e 1) (e 0) (e 2))
    have index : (![e 0, e 1, e 2] : Exponent 3) = e := by
      funext i
      fin_cases i <;> rfl
    simpa only [index] using eq
  obtain ⟨U, hU⟩ := canonical_truncation D α β u v
  obtain ⟨A, hA⟩ := canonical_truncation D α γ u t
  obtain ⟨B, hB⟩ := canonical_truncation D β γ v t
  have finalAction (e : Exponent 3) :
      polynomialAction (finalPolynomial k a)
        (fun e => leftNested D α β γ δ u v t w (e 0) (e 1) (e 2)) e =
        signedExtend Pt e := by
    have eq := sameR_from_actual_middle D α β γ δ u v t w k a P common
      U.toNat A.toNat B.toNat
      (fun n hn => hU n (by omega)) (fun n hn => hA n (by omega))
      (fun n hn => hB n (by omega)) (e 0) (e 1) (e 2)
    have index : (![e 0, e 1, e 2] : Exponent 3) = e := by
      funext i
      fin_cases i <;> rfl
    simpa only [index] using eq
  have finalEqual :
      (fun e => leftNested D α β γ δ u v t w (e 0) (e 1) (e 2)) =
        laurentCoefficient Pt k a := by
    apply finalR_injective k (a 0) (a 1) (a 2) _ _
      (actual_nested_support D α β γ δ u v t w) (old_expression_support Pt k a)
    funext e
    exact (finalAction e).trans (raw_R_action_transport Pt k a e).symm
  refine ⟨a, P, truncation, six, ?_, middleAction, finalAction, ?_⟩
  · intro s b z
    rw [reconstruction s b z]
    unfold middleSum middleTerm
    apply Finset.sum_congr rfl
    intro i hi
    rw [common]
    congr 2
  · intro e
    exact congrFun finalEqual e

#print actual_three_field_adjacent_bracketings
#print axioms actual_three_field_adjacent_bracketings
end
end D5.S3.VertexAlgebra.LatticeSectorAdjacentBracketings
