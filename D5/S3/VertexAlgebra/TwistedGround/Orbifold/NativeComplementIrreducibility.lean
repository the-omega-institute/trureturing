/- GID: D5/S3/VertexAlgebra/TwistedGround/Orbifold/NativeComplementIrreducibility
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/Orbifold/NativeComplementIrreducibility
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Irreducibility of the actual Leech complement under its native modes. -/

import D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeComplementOddDetection

/-! Irreducibility of the actual order-two Leech complement under its
integral diagonal modes and half-integer off-diagonal modes. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

noncomputable section

open scoped BigOperators VertexOperator

namespace D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeComplementIrreducibility

open ActualLeechHyperbolic (leechData leech_spec)
open HalfFock.LatticeHalfFockEvenFixedModeIrreducibility (fixedParitySlice_even_irreducible)
open HalfFock.LatticeHalfFockParityField (paritySpace)
open LatticeHalfFockGradedTrace (actualAmbientBasis actualTensorL0 actualTensorL0_repr oddWeight)
open LatticeInvolution (FixedCarrier)
open LatticePositiveEnergy (stateEnergies)
open NativeBBOCoefficientTransport (P Q fixedH mixedImageSpan_eq_top)
open NativeComplementOddDetection (exists_Q_ne_zero)
open NativeMixedPairBorcherds (mixedImageSpan)
open NativeOddTwistedIntertwiner (OddCarrier TwistedEven TwistedOdd leechUnit oddMode paritySign)

open private parity_repr from D5.S3.VertexAlgebra.TwistedGround.MixedTranslation
open private stress stress_action stress_odd_one from
  D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeOddTopDetection
open private oddGradeProjection oddGradeInclusion sum_oddGradeProjections from
  D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeMixedPairState

local notation "ℒ" => leechData
local notation "H" => TwistedEven
local notation "O" => OddCarrier ℒ
local notation "L₀H" => fixedH (stress ℒ) 1
local notation "L₀O" => oddMode ℒ (stress ℒ) 1

set_option maxHeartbeats 1000000 in
private theorem twisted_shift_ne_zero (d : ℤ) (h : H) (hh : h ≠ 0) :
    L₀H h - (d : ℂ) • h ≠ 0 := by
  intro hz
  have hz' : L₀H h = (d : ℂ) • h := sub_eq_zero.mp hz
  have hzval := congrArg (fun z : H => z.val) hz'
  change (L₀H h).val = (d : ℂ) • h.val at hzval
  have heigen : actualTensorL0 ℒ leechUnit h.val = (d : ℂ) • h.val :=
    (stress_action (D := ℒ) (hu := leechUnit) false h).symm.trans hzval
  apply hh
  apply Subtype.ext
  apply (actualAmbientBasis ℒ leechUnit).repr.injective
  apply Finsupp.ext
  intro i
  change (actualAmbientBasis ℒ leechUnit).repr h.val i =
    (actualAmbientBasis ℒ leechUnit).repr 0 i
  rw [map_zero, Finsupp.zero_apply]
  by_contra hcoord
  have heven : oddWeight ℒ i.1 % 2 = 0 := by
    have hp := h.property
    simp only [paritySign, Bool.false_eq_true, ite_false, paritySpace, LinearMap.mem_ker,
      LinearMap.sub_apply, LinearMap.id_apply, one_smul, sub_eq_zero] at hp
    have hc := congrArg (fun x => (actualAmbientBasis ℒ leechUnit).repr x i) hp
    rw [parity_repr] at hc
    by_contra hn
    have ho : oddWeight ℒ i.1 % 2 = 1 := by omega
    rw [neg_one_pow_eq_pow_mod_two, ho, pow_one] at hc
    exact hcoord (by linear_combination hc / (-2 : ℂ))
  have hc := congrArg (fun x => (actualAmbientBasis ℒ leechUnit).repr x i) heigen
  rw [actualTensorL0_repr] at hc
  simp only [map_smul, Finsupp.smul_apply, smul_eq_mul] at hc
  have hscalar := mul_right_cancel₀ hcoord hc
  rw [leech_spec.1] at hscalar
  have hw : (oddWeight ℒ i.1 : ℂ) + 3 = 2 * (d : ℂ) := by
    linear_combination 2 * hscalar
  have hwz : (oddWeight ℒ i.1 : ℤ) + 3 = 2 * d := by exact_mod_cast hw
  omega

set_option maxHeartbeats 1000000 in
private theorem exists_pure_even_of_sum (S : Submodule ℂ (H × O))
    (stable : ∀ (h : H) (o : O), (h, o) ∈ S → (L₀H h, L₀O o) ∈ S)
    (grades : Finset ℤ) :
    ∀ v : ℤ → O, (∀ d ∈ grades, L₀O (v d) = (d : ℂ) • v d) →
      ∀ h : H, h ≠ 0 → (h, ∑ d ∈ grades, v d) ∈ S →
        ∃ h' : H, h' ≠ 0 ∧ (h', (0 : O)) ∈ S := by
  classical
  let : AddCommGroup H := (paritySpace ℒ leechUnit (paritySign false)).addCommGroup
  let : AddCommGroup O := (LatticeInvolution.minusSpace ℒ).addCommGroup
  induction grades using Finset.induction_on with
  | empty =>
      intro v _ h hh hx
      exact ⟨h, hh, by simpa only [Finset.sum_empty] using hx⟩
  | insert d grades hd ih =>
      intro v hv h hh hx
      let shift : Module.End ℂ O :=
        L₀O - ((d : ℂ) • (LinearMap.id : Module.End ℂ O) : Module.End ℂ O)
      let w (e : ℤ) : O := ((e : ℂ) - (d : ℂ)) • v e
      have hshift (e : ℤ) (he : e ∈ insert d grades) : shift (v e) = w e := by
        change L₀O (v e) - (d : ℂ) • v e = ((e : ℂ) - (d : ℂ)) • v e
        rw [hv e he, sub_smul]
      have hw (e : ℤ) (he : e ∈ grades) : L₀O (w e) = (e : ℂ) • w e := by
        dsimp only [w]
        rw [map_smul, hv e (Finset.mem_insert_of_mem he)]
        exact smul_comm ((e : ℂ) - (d : ℂ)) (e : ℂ) (v e)
      have hsum : shift (∑ e ∈ insert d grades, v e) = ∑ e ∈ grades, w e := by
        rw [Finset.sum_insert hd, map_add, map_sum, hshift d (Finset.mem_insert_self _ _)]
        have hd0 : w d = 0 := by simp [w]
        rw [hd0, zero_add]
        exact Finset.sum_congr rfl fun e he => hshift e (Finset.mem_insert_of_mem he)
      have hy : (L₀H h - (d : ℂ) • h, shift (∑ e ∈ insert d grades, v e)) ∈ S := by
        change (L₀H h, L₀O (∑ e ∈ insert d grades, v e)) -
          (d : ℂ) • (h, ∑ e ∈ insert d grades, v e) ∈ S
        exact S.sub_mem (stable h _ hx) (S.smul_mem (d : ℂ) hx)
      rw [hsum] at hy
      exact ih w hw _ (twisted_shift_ne_zero d h hh) hy

/- proof_shape: complement_mode_irreducible: content
   admission_basis: escape-witness
   escape_witness: Actual stress-mode shifts remove every integral grade from the
   odd component while retaining a nonzero even twisted component. The native
   Q coefficients supply an even twisted vector for an initially pure odd input.
   The fixed modes and the span of the P coefficients then fill both summands. -/
set_option maxHeartbeats 1000000 in
/-- The actual fixed-source modes and the signed half-integer modes of the
order-two Leech complement have only the zero and full invariant submodules. -/
theorem complement_mode_irreducible (S : Submodule ℂ (H × O))
    (stableEven : ∀ (a : FixedCarrier ℒ) (n : ℤ) (h : H) (o : O), (h, o) ∈ S →
      (fixedH a n h, oddMode ℒ a n o) ∈ S)
    (stableOdd : ∀ (b : TwistedOdd) (n : ℤ) (h : H) (o : O), (h, o) ∈ S →
      (-Q b n o, P b n h) ∈ S) :
    S = ⊥ ∨ S = ⊤ := by
  by_cases hS : S = ⊥
  · exact Or.inl hS
  right
  obtain ⟨⟨h, o⟩, hx, hne⟩ := S.ne_bot_iff.mp hS
  have hseed : ∃ u : H, u ≠ 0 ∧ (u, (0 : O)) ∈ S := by
    by_cases hh : h = 0
    · subst h
      have ho : o ≠ 0 := by
        intro ho
        subst o
        exact hne rfl
      obtain ⟨b, n, hq⟩ := exists_Q_ne_zero o ho
      have hnq : -Q b n o ≠ 0 := by
        intro hn
        apply hq
        apply Subtype.ext
        have hv := congrArg (fun z : H => z.val) hn
        change -(Q b n o).val = 0 at hv
        exact neg_eq_zero.mp hv
      exact ⟨-Q b n o, hnq, by
        simpa only [map_zero] using stableOdd b n 0 o hx⟩
    · let v (d : ℤ) : O := oddGradeInclusion d (oddGradeProjection d o)
      have hsum : (∑ d ∈ stateEnergies ℒ o.val, v d) = o := sum_oddGradeProjections o
      refine exists_pure_even_of_sum S (stableEven (stress ℒ) 1) (stateEnergies ℒ o.val)
        v ?_ h hh ?_
      · intro d _
        exact stress_odd_one (D := ℒ) leechUnit d (v d) (oddGradeProjection d o).property.1
      · simpa only [hsum] using hx
  obtain ⟨u, hune, hu⟩ := hseed
  let SH := S.comap (LinearMap.inl ℂ H O)
  have hSHstable (a : FixedCarrier ℒ) (n : ℤ) (x : H) (hx : x ∈ SH) :
      fixedH a n x ∈ SH := by
    change (x, (0 : O)) ∈ S at hx
    change (fixedH a n x, (0 : O)) ∈ S
    simpa only [map_zero] using stableEven a n x 0 hx
  have hSHtop : SH = ⊤ :=
    (fixedParitySlice_even_irreducible ℒ leechUnit SH hSHstable).resolve_left
      (SH.ne_bot_iff.mpr ⟨u, hu, hune⟩)
  have hH (x : H) : (x, (0 : O)) ∈ S :=
    Submodule.eq_top_iff'.mp hSHtop x
  let SO := S.comap (LinearMap.inr ℂ H O)
  have hspan : mixedImageSpan ≤ SO := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨n, b, x⟩, rfl⟩
    change ((0 : H), P b n x) ∈ S
    have hn0 : -(0 : H) = 0 := by
      apply Subtype.ext
      change -((0 : H).val) = (0 : H).val
      rw [show (0 : H).val = 0 from rfl, neg_zero]
    simpa only [map_zero, hn0] using stableOdd b n x 0 (hH x)
  rw [mixedImageSpan_eq_top] at hspan
  refine Submodule.eq_top_iff'.mpr ?_
  rintro ⟨x, y⟩
  have hy : ((0 : H), y) ∈ S := hspan (Submodule.mem_top (x := y))
  simpa only [Prod.mk_add_mk, add_zero, zero_add] using S.add_mem (hH x) hy

/--
info: 'D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeComplementIrreducibility.complement_mode_irreducible' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms complement_mode_irreducible

end D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeComplementIrreducibility
