/- GID: D5/S3/VertexAlgebra/TwistedGround/BarnesWall/Rank32CommutingTrace
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/BarnesWall/Rank32CommutingTrace
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The rank-32 commuting Pauli lifts have a positive trace Gauss sum of 4096. -/

import D5.S3.VertexAlgebra.TwistedGround.BarnesWall.OddWeylTrace

/-!
The two commuting order-four Pauli words on slots zero and one have the
even rows as their common displacement space. Splitting at slot two and
reindexing the columns by a flip and complement pairs the two rows of
each tail with both columns of that tail.
-/

open scoped BigOperators Matrix
set_option autoImplicit false

namespace D5.S3.VertexAlgebra.TwistedGround.BarnesWall.Rank32CommutingTrace

open LatticeTwistedGroundRealization (sign_sum)
open LatticeTwistedGroundRealization.SignQuotient (F₂ complexSign)
open TailPauliPairing (Word parity parity_flip complement pairing)
open OddGaussSum (Half complementPermutation)
open OddWeylTrace (evenDisplacement spectatorDisplacementEquiv)

open private EvenIndex evenLabel evenLabel_parity displacementMap
  preimageIMap actionI actionI_odd actionI_eq actual_preimageI
  block_single block_flip block_add lift_phase_polar quadratic_eq_of_polar_of_single wordI
  from D5.S3.VertexAlgebra.TwistedGround.BarnesWall.OddGaussSum
open private displacement_of_action_eq range_le_evenDisplacement actions_fix_even_single
  even_single_mem_displacement generator_fixes_displacement word_phase_zero_on_evenDisplacement
  spectatorDisplacementEquiv_val
  from D5.S3.VertexAlgebra.TwistedGround.BarnesWall.OddWeylTrace

local notation "flip" => TailPauliPairing.flip

noncomputable section

private abbrev Bits := Word (Fin 5)
private abbrev Left := Half (2 : Fin 5) false
private abbrev Right := Half (2 : Fin 5) true
private abbrev Index := EvenIndex (2 : Fin 5)
private abbrev Rows := Bits → F₂

/-- The coordinate functions on the two spectator halves. -/
abbrev Coordinates := (Left → F₂) × (Right → F₂)

private abbrev Tail := Bool × Bool
private abbrev Label := Tail × Bool
private abbrev Block := (Bool → F₂) × (Bool → F₂)

private theorem odd_slots : (Fintype.card (Fin 5) : F₂) = 1 := by decide
private theorem five_slots : 5 ≤ Fintype.card (Fin 5) := by decide
private theorem three_slots : 3 ≤ Fintype.card (Fin 5) := by decide

private def leftWord (p : Label) : Bits :=
  ![p.2, xor p.2 (xor p.1.1 p.1.2), false, p.1.1, p.1.2]

/-- A tail and a slot-zero bit determine an even row of spectator bit zero. -/
def leftLabel : Label ≃ Left where
  toFun p := ⟨leftWord p, by
    rcases p with ⟨⟨a, b⟩, c⟩
    cases a <;> cases b <;> cases c <;> decide, rfl⟩
  invFun u := ((u.val 3, u.val 4), u.val 0)
  left_inv p := by rcases p with ⟨⟨a, b⟩, c⟩; rfl
  right_inv u := by
    have hu := u.property.1
    simp only [parity, Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one] at hu
    have h₁ : u.val 1 = xor (u.val 0) (xor (u.val 3) (u.val 4)) := by
      have h₂ := u.property.2
      change u.val 2 = false at h₂
      change ((if u.val 0 then 1 else 0) + ((if u.val 1 then 1 else 0) +
        ((if u.val 2 then 1 else 0) + ((if u.val 3 then 1 else 0) +
          ((if u.val 4 then 1 else 0) + 0))))) = (0 : F₂) at hu
      rw [h₂] at hu
      generalize u.val 0 = a at hu ⊢
      generalize u.val 1 = b at hu ⊢
      generalize u.val 3 = c at hu ⊢
      generalize u.val 4 = d at hu ⊢
      have hparity : ∀ a b c d : Bool,
          ((if a then 1 else 0) + ((if b then 1 else 0) + ((if false then 1 else 0) +
            ((if c then 1 else 0) + ((if d then 1 else 0) + 0))))) = (0 : F₂) →
          b = xor a (xor c d) := by decide
      exact hparity a b c d hu
    apply Subtype.ext
    funext i
    fin_cases i
    · rfl
    · exact h₁.symm
    · exact u.property.2.symm
    · rfl
    · rfl

/-- Reindex the other half by applying slot-zero flip followed by complement. -/
def rightLabel : Label ≃ Right :=
  leftLabel.trans (complementPermutation 0 2 (by decide) odd_slots)

/-- The two single-flip preimages paired with the second even row by Gram complement. -/
def preimagePairing (u v : Bits) : F₂ := pairing (flip u 0) v + pairing (flip u 1) v

private theorem same_spectator (u v : Bits) (h : v 2 = u 2) :
    preimagePairing u v = 0 := by
  have hz (r : Fin 5) (hr : (2 : Fin 5) ≠ r) : pairing (flip u r) v = 0 := by
    unfold pairing
    apply ite_eq_right
    intro he
    have hb := congrFun he 2
    rw [h] at hb
    cases hu : u 2 <;> simp [complement, TailPauliPairing.flip, hr, hu] at hb
  rw [preimagePairing, hz 0 (by decide), hz 1 (by decide), add_zero]

private theorem flip_leftWord (p : Label) :
    flip (leftWord (p.1, !p.2)) 0 = flip (leftWord p) 1 := by
  rcases p with ⟨⟨a, b⟩, c⟩
  cases a <;> cases b <;> cases c <;> decide

/-- The cross matrix is four all-ones blocks of size two. The right labels
are obtained by applying Gram complement after flipping slot zero. -/
theorem complement_cross_entry (p q : Label) :
    preimagePairing (leftLabel p).val (rightLabel q).val =
      if q.1 = p.1 then 1 else 0 := by
  classical
  have hmain : (rightLabel q).val = complement (flip (leftLabel p).val 0) ↔ q = p := by
    change (rightLabel q).val = (rightLabel p).val ↔ q = p
    exact ⟨fun h => rightLabel.injective (Subtype.ext h),
      fun h => congrArg (fun r => (rightLabel r).val) h⟩
  have hextra : (rightLabel q).val = complement (flip (leftLabel p).val 1) ↔
      q = (p.1, !p.2) := by
    have he : (rightLabel (p.1, !p.2)).val = complement (flip (leftLabel p).val 1) := by
      change complement (flip (leftWord (p.1, !p.2)) 0) = complement (flip (leftWord p) 1)
      rw [flip_leftWord]
    rw [← he]
    exact ⟨fun h => rightLabel.injective (Subtype.ext h),
      fun h => congrArg (fun r => (rightLabel r).val) h⟩
  simp only [preimagePairing, pairing, hmain, hextra]
  rcases p with ⟨s, b⟩
  rcases q with ⟨t, c⟩
  by_cases h : t = s
  · subst t
    cases b <;> cases c <;> simp
  · simp [h]

/-- The cross exponent in spectator coordinates. -/
def crossExponent (p : Coordinates) : F₂ :=
  ∑ u : Left, p.1 u * ∑ v : Right, preimagePairing u.val v.val * p.2 v

private def blockCoordinates : Coordinates ≃ (Tail → Block) :=
  (Equiv.prodCongr
    ((LinearEquiv.funCongrLeft F₂ F₂ leftLabel).toEquiv.trans (Equiv.curry _ _ _))
    ((LinearEquiv.funCongrLeft F₂ F₂ rightLabel).toEquiv.trans (Equiv.curry _ _ _))).trans
    (Equiv.arrowProdEquivProdArrow Tail (fun _ => Bool → F₂) (fun _ => Bool → F₂)).symm

private def bitSum (f : Bool → F₂) : F₂ := f false + f true

private def blockExponent (p : Block) : F₂ := bitSum p.1 * bitSum p.2

private theorem cross_eq_blocks (p : Coordinates) :
    crossExponent p = ∑ t : Tail, blockExponent (blockCoordinates p t) := by
  classical
  have hinner (u : Label) :
      (∑ v : Right, preimagePairing (leftLabel u).val v.val * p.2 v) =
        p.2 (rightLabel (u.1, false)) + p.2 (rightLabel (u.1, true)) := by
    rw [← rightLabel.sum_comp]
    simp_rw [complement_cross_entry, ite_mul, one_mul, zero_mul]
    rw [Fintype.sum_prod_type]
    calc
      _ = ∑ t : Tail, if t = u.1 then
          p.2 (rightLabel (t, false)) + p.2 (rightLabel (t, true)) else 0 := by
        apply Finset.sum_congr rfl
        intro t _
        by_cases ht : t = u.1 <;> simp [ht, add_comm]
      _ = _ := by simp
  unfold crossExponent
  rw [← leftLabel.sum_comp]
  simp_rw [hinner]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro t _
  simp only [Fintype.sum_bool]
  rw [← add_mul, add_comm (p.1 (leftLabel (t, true)))]
  rfl

private def bitSumEquiv : (Bool → F₂) ≃ F₂ × F₂ where
  toFun f := (f false, bitSum f)
  invFun p b := if b then p.1 + p.2 else p.1
  left_inv f := by
    funext b
    cases b <;> simp [bitSum, ← add_assoc, CharTwo.add_self_eq_zero]
  right_inv p := by simp [bitSum, ← add_assoc, CharTwo.add_self_eq_zero]

private theorem block_sum : (∑ p : Block, complexSign (blockExponent p)) = (8 : ℂ) := by
  have h := BinaryGauss.block_sum 0 1 0 (by decide)
  have hc : ZMod.χ₈ (BinaryGauss.gram 0 1 0).det = 1 := by decide
  have hbinary : (∑ p : F₂ × F₂, complexSign (p.1 * p.2)) = (2 : ℂ) := by
    simpa [BinaryGauss.quadratic, show BinaryGauss.residue 0 = 0 by decide,
      show BinaryGauss.residue 1 = 1 by decide, hc] using h
  let e := (Equiv.prodProdProdComm F₂ F₂ F₂ F₂).trans
    (Equiv.prodCongr bitSumEquiv.symm bitSumEquiv.symm)
  rw [← e.sum_comp (fun p : Block => complexSign (blockExponent p))]
  have he (p : (F₂ × F₂) × (F₂ × F₂)) : blockExponent (e p) = p.2.1 * p.2.2 := by
    change (p.1.1 + (p.1.1 + p.2.1)) * (p.1.2 + (p.1.2 + p.2.2)) = _
    rw [← add_assoc, ← add_assoc, CharTwo.add_self_eq_zero, CharTwo.add_self_eq_zero,
      zero_add, zero_add]
  simp_rw [he]
  rw [Fintype.sum_prod_type]
  norm_num [hbinary, Fintype.card_prod, ZMod.card]

private theorem cross_gauss_sum :
    (∑ p : Coordinates, complexSign (crossExponent p)) = (4096 : ℂ) := by
  classical
  simp_rw [cross_eq_blocks]
  rw [blockCoordinates.sum_comp (fun p => complexSign (∑ t, blockExponent (p t)))]
  simp_rw [sign_sum Finset.univ]
  rw [← Fintype.prod_sum (fun (_ : Tail) (p : Block) => complexSign (blockExponent p))]
  norm_num [block_sum, Fintype.card_prod]

private abbrev sectionI := preimageIMap (0 : Fin 5) 2
private abbrev sectionJ := preimageIMap (1 : Fin 5) 2
private abbrev displacement := displacementMap (2 : Fin 5)
private abbrev wordJ := wordI (1 : Fin 5)
private abbrev H [LinearOrder Bits] : LinearMap.BilinForm F₂ Rows := TensorGram.halfGram.toBilin'

/-- The coupled exponent of the literal words `[(0,false),(0,true)]` and
`[(1,false),(1,true)]` with their single-flip displacement sections. -/
def traceExponent [LinearOrder Bits] (p : Coordinates) : F₂ :=
  let x : Index → F₂ := Sum.elim p.1 p.2
  let w := displacement x
  let a := sectionI x
  let b := sectionJ x
  TensorLift.wordLiftExponent (wordI (0 : Fin 5)) a +
    TensorLift.wordLiftExponent wordJ b + H w (a + b + w)

private theorem basis_phase_zero [LinearOrder Bits] (u : Index) :
    let x := Pi.single u 1
    TensorLift.wordLiftExponent (wordI (0 : Fin 5)) (sectionI x) +
      TensorLift.wordLiftExponent wordJ (sectionJ x) +
      H (displacement x) (sectionI x + sectionJ x + displacement x) = 0 := by
  dsimp only
  simp only [preimageIMap, displacementMap, ← Pi.basisFun_apply, Module.Basis.constr_basis]
  simp only [Pi.basisFun_apply]
  let v := evenLabel (2 : Fin 5) u
  have hv : ∀ q : Fin 5, q ≠ 0 → q ≠ 1 → v q = v q := fun _ _ _ => rfl
  have ha := block_flip (r₁ := (0 : Fin 5)) (r₂ := 1) (r := 0) (Or.inl rfl) hv
  have hb := block_flip (r₁ := (0 : Fin 5)) (r₂ := 1) (r := 1) (Or.inr rfl) hv
  have hw := block_single 0 1 v v hv
  have hI := TensorLift.wordLiftExponent_eq_zero_on_block odd_slots five_slots 0 1 v
    (wordI 0) (by simp [wordI]) _ ha
  have hJ := TensorLift.wordLiftExponent_eq_zero_on_block odd_slots five_slots 0 1 v
    wordJ (by simp [wordJ, wordI]) _ hb
  have hH := TensorGram.halfGram_bilin_eq_zero_on_block odd_slots five_slots 0 1 v _ _ hw
    (block_add (block_add ha hb) hw)
  rw [hI, hJ, hH, add_zero, add_zero]

private def crossMatrix : Matrix Index Index F₂ := fun u v =>
  match u, v with
  | .inl u, .inr v => preimagePairing u.val v.val
  | _, _ => 0

/-- Polarization identifies the literal lift exponent with the complement pairing
between the spectator halves. -/
theorem trace_exponent_eq_cross [LinearOrder Bits] (p : Coordinates) :
    traceExponent p = crossExponent p := by
  classical
  let Q (x : Index → F₂) := TensorLift.wordLiftExponent (wordI (0 : Fin 5)) (sectionI x) +
    TensorLift.wordLiftExponent wordJ (sectionJ x) +
    H (displacement x) (sectionI x + sectionJ x + displacement x)
  let P : LinearMap.BilinForm F₂ Rows := H + H.flip
  let G := P.comp (sectionI + sectionJ + displacement) displacement
  let B := crossMatrix.toBilin'
  have hI := lift_phase_polar odd_slots three_slots (wordI (0 : Fin 5))
  have hJ := lift_phase_polar odd_slots three_slots wordJ
  simp only [← actionI_eq odd_slots] at hI hJ
  have hpol x y : Q (x + y) = Q x + Q y + G x y :=
    trace_exponent_polarization H (actionI 0) (actionI 1) sectionI sectionJ displacement
      _ _ (actual_preimageI 0 2) (actual_preimageI 1 2) hI hJ x y
  have hsym x y : G x y = G y x := by
    have h := hpol x y
    rw [add_comm x y, hpol y x, add_comm (Q y) (Q x)] at h
    exact (add_left_cancel h).symm
  have hentry (u v : Index) :
      G (Pi.single u 1) (Pi.single v 1) = preimagePairing (evenLabel 2 u) (evenLabel 2 v) := by
    have hp (s t : Bits) (ht : parity t = 0) :
        P (Pi.single s 1) (Pi.single t 1) = pairing s t := by
      simp only [P, H, LinearMap.BilinForm.add_apply, LinearMap.BilinForm.flip_apply,
        Matrix.toBilin'_single]
      rw [TensorGram.halfGram_symmetrize odd_slots three_slots,
        TensorGram.gram_mod_two_of_even_right odd_slots s t ht]
    have hu := evenLabel_parity (2 : Fin 5) u
    have hv := evenLabel_parity (2 : Fin 5) v
    have he : pairing (evenLabel 2 u) (evenLabel 2 v) = 0 := by
      rw [← TensorGram.gram_mod_two_of_even_right odd_slots _ _ hv,
        TensorGram.gram_mod_two_of_even_even odd_slots _ _ hu hv]
    simp only [G, LinearMap.BilinForm.comp_apply, LinearMap.add_apply,
      displacementMap, preimageIMap, ← Pi.basisFun_apply, Module.Basis.constr_basis]
    simp only [Pi.basisFun_apply, LinearMap.BilinForm.add_left, hp _ _ hv, he, add_zero,
      preimagePairing]
  have hbilin : G = B + B.flip := by
    apply LinearMap.BilinForm.ext_basis (Pi.basisFun F₂ Index)
    intro u v
    simp only [Pi.basisFun_apply, LinearMap.BilinForm.add_apply, LinearMap.BilinForm.flip_apply,
      B, Matrix.toBilin'_single]
    cases u with
    | inl u =>
      cases v with
      | inl v =>
        simpa only [hentry, evenLabel, Sum.elim_inl, crossMatrix, add_zero] using
          same_spectator u.val v.val (v.property.2.trans u.property.2.symm)
      | inr v => rw [hentry]; simp [crossMatrix, evenLabel]
    | inr u =>
      cases v with
      | inl v => rw [hsym, hentry]; simp [crossMatrix, evenLabel]
      | inr v =>
        simpa only [hentry, evenLabel, Sum.elim_inr, crossMatrix, add_zero] using
          same_spectator u.val v.val (v.property.2.trans u.property.2.symm)
  have hQ (x y) : Q (x + y) = Q x + Q y + (B x y + B y x) := by
    simpa only [hbilin, LinearMap.BilinForm.add_apply, LinearMap.BilinForm.flip_apply]
      using hpol x y
  have hB (u : Index) : Q (Pi.single u 1) = B (Pi.single u 1) (Pi.single u 1) := by
    dsimp only [Q, B]
    rw [basis_phase_zero u, Matrix.toBilin'_single]
    cases u <;> rfl
  let x : Index → F₂ := Sum.elim p.1 p.2
  change Q x = crossExponent p
  rw [quadratic_eq_of_polar_of_single Q B hQ hB]
  simp only [B, Matrix.toBilin'_apply, crossExponent, Fintype.sum_sum_type, crossMatrix, x,
    Sum.elim_inl, Sum.elim_inr, mul_zero, zero_mul, Finset.sum_const_zero, add_zero, zero_add]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun v _ => mul_assoc _ _ _

/-- The Gauss sum for the actual rank-32 commuting lift exponent. -/
theorem tensor_trace_gauss_sum [LinearOrder Bits] :
    (∑ p : Coordinates, complexSign (traceExponent p)) = (4096 : ℂ) := by
  simp_rw [trace_exponent_eq_cross]
  exact cross_gauss_sum

private theorem cross_polar (p q : Coordinates) :
    crossExponent (p + q) + crossExponent p + crossExponent q =
      ∑ t : Tail,
        (bitSum (blockCoordinates p t).1 * bitSum (blockCoordinates q t).2 +
         bitSum (blockCoordinates q t).1 * bitSum (blockCoordinates p t).2) := by
  simp only [cross_eq_blocks, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro t _
  have hleft : bitSum (blockCoordinates (p + q) t).1 =
      bitSum (blockCoordinates p t).1 + bitSum (blockCoordinates q t).1 := by
    change (p.1 (leftLabel (t, false)) + q.1 (leftLabel (t, false))) +
        (p.1 (leftLabel (t, true)) + q.1 (leftLabel (t, true))) =
      (p.1 (leftLabel (t, false)) + p.1 (leftLabel (t, true))) +
        (q.1 (leftLabel (t, false)) + q.1 (leftLabel (t, true)))
    abel
  have hright : bitSum (blockCoordinates (p + q) t).2 =
      bitSum (blockCoordinates p t).2 + bitSum (blockCoordinates q t).2 := by
    change (p.2 (rightLabel (t, false)) + q.2 (rightLabel (t, false))) +
        (p.2 (rightLabel (t, true)) + q.2 (rightLabel (t, true))) =
      (p.2 (rightLabel (t, false)) + p.2 (rightLabel (t, true))) +
        (q.2 (rightLabel (t, false)) + q.2 (rightLabel (t, true)))
    abel
  simp only [blockExponent, hleft, hright, add_mul, mul_add]
  have hxx := CharTwo.add_self_eq_zero
    (bitSum (blockCoordinates p t).1 * bitSum (blockCoordinates p t).2)
  have hyy := CharTwo.add_self_eq_zero
    (bitSum (blockCoordinates q t).1 * bitSum (blockCoordinates q t).2)
  linear_combination (norm := abel) hxx + hyy

/-- The radical of the lift polarization consists of the vectors whose two
coefficients in each tail agree, separately in both spectator halves. -/
theorem trace_polar_radical_iff [LinearOrder Bits] (p : Coordinates) :
    (∀ q : Coordinates, traceExponent (p + q) + traceExponent p + traceExponent q = 0) ↔
      ∀ t : Tail,
        p.1 (leftLabel (t, false)) = p.1 (leftLabel (t, true)) ∧
        p.2 (rightLabel (t, false)) = p.2 (rightLabel (t, true)) := by
  classical
  simp only [trace_exponent_eq_cross, cross_polar]
  constructor
  · intro h t
    let f (s : Tail) (b : Bool) : F₂ := if s = t ∧ b = false then 1 else 0
    have hf (s : Tail) : bitSum (f s) = if s = t then 1 else 0 := by simp [bitSum, f]
    have hz : bitSum (0 : Bool → F₂) = 0 := by simp [bitSum]
    have hl : bitSum (blockCoordinates p t).1 = 0 := by
      simpa [hf, hz, mul_ite] using h (blockCoordinates.symm (fun s => (0, f s)))
    have hr : bitSum (blockCoordinates p t).2 = 0 := by
      simpa [hf, hz, ite_mul] using h (blockCoordinates.symm (fun s => (f s, 0)))
    exact ⟨CharTwo.add_eq_zero.mp hl, CharTwo.add_eq_zero.mp hr⟩
  · intro h q
    apply Finset.sum_eq_zero
    intro t _
    have hl : bitSum (blockCoordinates p t).1 = 0 := CharTwo.add_eq_zero.mpr (h t).1
    have hr : bitSum (blockCoordinates p t).2 = 0 := CharTwo.add_eq_zero.mpr (h t).2
    rw [hl, hr, zero_mul, mul_zero, add_zero]

private theorem action_displacement_range (r : Fin 5) :
    LinearMap.range (actionI r + LinearMap.id) = evenDisplacement (2 : Fin 5) := by
  apply le_antisymm
  · apply range_le_evenDisplacement
    intro u
    rcases (show ∀ a : F₂, a = 0 ∨ a = 1 by decide) (parity u) with hu | hu
    · rw [displacement_of_action_eq
        (show actionI r (Pi.single u 1) = Pi.single u 1 + 0 by
          rw [add_zero, (actions_fix_even_single r r u hu).1])]
      exact Submodule.zero_mem _
    · rw [displacement_of_action_eq (actionI_odd r u hu)]
      exact even_single_mem_displacement 2 _ (by
        rw [parity_flip, hu, CharTwo.add_self_eq_zero])
  · rintro _ ⟨x, rfl⟩
    exact ⟨preimageIMap r 2 x, displacement_of_action_eq (actual_preimageI r 2 x)⟩

/-- Both literal words have the even tensor-row space as their displacement image. -/
theorem tensor_displacement_ranges :
    (∀ r : Fin 5, r = 0 ∨ r = 1 →
      LinearMap.range ((TensorLift.modTwo (TensorLift.wordMatrix (wordI r))).vecMulLinear +
        LinearMap.id) = evenDisplacement (2 : Fin 5)) := by
  intro r _
  have h : (TensorLift.modTwo (TensorLift.wordMatrix (wordI r))).vecMulLinear = actionI r :=
    LinearMap.ext fun x => (actionI_eq odd_slots r x).symm
  rw [h, action_displacement_range]

/-- The rank-32 Weyl trace ratio, and the product trace in the common
normalization where both order-four ground traces are 256. -/
theorem normalized_tensor_trace_mul [LinearOrder Bits]
    {V : Type*} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V] [Nontrivial V]
    (P : Rows → Module.End ℂ V) (hzero : P 0 = 1)
    (hmul : ∀ x y, P x * P y = complexSign (H x y) • P (x + y))
    (hdim : Module.finrank ℂ V = 65536)
    {Ui Uj : Module.End ℂ V} (hneI : Ui ≠ 0) (hneJ : Uj ≠ 0)
    (hcovI : ∀ x, Ui * P x =
      complexSign (TensorLift.wordLiftExponent (wordI (0 : Fin 5)) x) •
        (P (x ᵥ* TensorLift.modTwo (TensorLift.wordMatrix (wordI (0 : Fin 5)))) * Ui))
    (hcovJ : ∀ x, Uj * P x =
      complexSign (TensorLift.wordLiftExponent wordJ x) •
        (P (x ᵥ* TensorLift.modTwo (TensorLift.wordMatrix wordJ)) * Uj)) :
    ((Module.finrank ℂ V : ℂ) * LinearMap.trace ℂ V (Ui * Uj)) /
      (LinearMap.trace ℂ V Ui * LinearMap.trace ℂ V Uj) = 4096 ∧
    (LinearMap.trace ℂ V Ui = 256 → LinearMap.trace ℂ V Uj = 256 →
      LinearMap.trace ℂ V (Ui * Uj) = 4096) := by
  classical
  let W := evenDisplacement (2 : Fin 5)
  let e := (spectatorDisplacementEquiv (2 : Fin 5)).toEquiv
  let _ : Fintype W := Fintype.ofEquiv Coordinates e
  let coords (w : W) : Index → F₂ := Sum.elim (e.symm w).1 (e.symm w).2
  let a (w : W) := sectionI (coords w)
  let b (w : W) := sectionJ (coords w)
  have hw (w : W) : displacement (coords w) = w.val :=
    (spectatorDisplacementEquiv_val 2 (e.symm w)).symm.trans
      (congrArg Subtype.val (e.apply_symm_apply w))
  have ha (w : W) : actionI 0 (a w) + a w = w.val :=
    (displacement_of_action_eq (actual_preimageI 0 2 (coords w))).trans (hw w)
  have hb (w : W) : actionI 1 (b w) + b w = w.val :=
    (displacement_of_action_eq (actual_preimageI 1 2 (coords w))).trans (hw w)
  have hcard : Fintype.card Rows = (Module.finrank ℂ V) ^ 2 := by
    change Fintype.card ((Fin 5 → Bool) → ZMod 2) = _
    norm_num [Fintype.card_fun, ZMod.card, hdim]
  have hfixed (r : Fin 5) (hr : r = 0 ∨ r = 1) (w : Rows) (hw' : w ∈ W) :
      actionI r w = w ∧ TensorLift.wordLiftExponent (wordI r) w = 0 := by
    have hfix (x : Rows) (hx : x ∈ W) : actionI r x = x := by
      rcases hx with ⟨y, rfl⟩
      simp only [actionI, LinearMap.comp_apply, generator_fixes_displacement]
    exact ⟨hfix w hw', word_phase_zero_on_evenDisplacement 0 1 2 odd_slots five_slots
      (wordI r) (by simpa [wordI] using hr)
      (fun x hx => (actionI_eq odd_slots r x).symm.trans (hfix x hx)) w hw'⟩
  simp only [← actionI_eq odd_slots] at hcovI hcovJ
  have htrace := WeylIntertwinerTraceProduct.normalized_trace_mul_eq_gauss_sum
    (H := H) (W := W) hzero hmul
    (OddWeylTrace.tensorPairing_perfect 2 odd_slots three_slots) hcard
    hcovI hcovJ a b ha hb (hfixed 0 (Or.inl rfl)) (hfixed 1 (Or.inr rfl))
    (OddWeylTrace.separates_outside_evenDisplacement 2 odd_slots three_slots) hneI hneJ
  let f (w : W) := complexSign
    (TensorLift.wordLiftExponent (wordI (0 : Fin 5)) (a w) +
      TensorLift.wordLiftExponent wordJ (b w) + H w.val (a w + b w + w.val))
  have hsum : (∑ w : W, f w) = 4096 := by
    rw [← e.sum_comp f]
    have hf (p : Coordinates) : f (e p) = complexSign (traceExponent p) := by
      have hval : (e p).val = displacement (Sum.elim p.1 p.2) :=
        spectatorDisplacementEquiv_val 2 p
      simp only [f, a, b, coords, Equiv.symm_apply_apply, hval, traceExponent]
    simp_rw [hf]
    exact tensor_trace_gauss_sum
  have hnormalized := htrace.trans hsum
  refine ⟨hnormalized, ?_⟩
  intro hi hj
  rw [hdim, hi, hj, div_eq_iff (by norm_num : (256 : ℂ) * 256 ≠ 0)] at hnormalized
  norm_num at hnormalized
  linear_combination hnormalized / 65536

#print axioms tensor_trace_gauss_sum
#print axioms trace_polar_radical_iff
#print axioms tensor_displacement_ranges
#print axioms normalized_tensor_trace_mul

end
end D5.S3.VertexAlgebra.TwistedGround.BarnesWall.Rank32CommutingTrace
