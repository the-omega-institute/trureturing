/- GID: D5/S3/Combinatorics/Matroids/PuncturedCircuitSplit
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Matroids/PuncturedCircuitSplit
   mirror-E: none(waiver:algebraic-inference)
   anchors: []
   utility: none
   digest: Product coordinates for the punctured alternating residue equations. -/

module

public import D5.S3.Combinatorics.Matroids.PuncturedCircuitCoordinateCount
public import D5.S3.Combinatorics.Matroids.PuncturedCircuitResiduePairs

/-! The coefficient decomposition after the weight vector is supported on two directions. -/

@[expose] public section

namespace D5.S3.Combinatorics.Matroids.PuncturedCircuitSplit

open Finset
open PuncturedCircuitCoordinateCount
open PuncturedCircuitResiduePairs
open UniformCircuitResidueForms
open RankTwoCircuitInvariantFactors (ResidueTorsion gcd_torsion_iff)
open RationalJointCircuitImage (RationalResidue)
open D5.S3.HomologicalAlgebra.OrderedFaceSign (insertionSign)
open OrderedCycleFactorization (sign_sq)

set_option autoImplicit false

variable {I M N : Type*} [LinearOrder I] [AddCommGroup M] [AddCommGroup N]
variable {d : ℕ}

/-- Read the coefficient of an alternating form on one face. -/
noncomputable def coefficient (b : Module.Basis I ℤ M) (F : Finset I) :
    (M [⋀^Fin d]→ₗ[ℤ] N) →ₗ[ℤ] N where
  toFun f := formCoordinates b f F
  map_add' f g := by
    by_cases hf : F.card = d <;> simp [formCoordinates, hf]
  map_smul' t f := by
    by_cases hf : F.card = d <;> simp [formCoordinates, hf]

/-- The pivot, two-weight insertion, total-size torsion and missing coefficient equations. -/
noncomputable def puncturedForms (b : Module.Basis I ℤ M) (x z w : I) (n u v : ℕ)
    (J : PairIndex x z w d) : Submodule ℤ (M [⋀^Fin (d + 1)]→ₗ[ℤ] RationalResidue) :=
  (((insertVector (b x)).ker ⊓ (insertVector (u • b z + v • b w)).ker) ⊓
    Submodule.torsionBy ℤ _ (n : ℤ)) ⊓ (coefficient b (insert z J.val.val)).ker

private lemma sign_twice (F : Finset I) (i : I) (v : N) :
    insertionSign F i • (insertionSign F i • v) = v := by
  rw [smul_smul, insertionSign, sign_sq, one_smul]

/-- A pair of distinct weight directions leaves independent coordinates on the
subsets using both or neither direction and one weighted pair on every common deletion. -/
theorem punctured_forms_equiv [Finite I] (b : Module.Basis I ℤ M) (x z w : I)
    (hxz : x ≠ z) (hxw : x ≠ w) (hzw : z ≠ w) (n u v : ℕ) (J₀ : PairIndex x z w d) :
    Nonempty (puncturedForms b x z w n u v J₀ ≃ₗ[ℤ]
      ((BothIndex x z w (d + 1) → ResidueTorsion (n.gcd (u.gcd v))) ×
       (NeitherIndex x z w (d + 1) → ResidueTorsion n) × puncturedPairs J₀ n u v)) := by
  let F := Set.powersetCard I (d + 1)
  let A := BothIndex x z w (d + 1)
  let B := NeitherIndex x z w (d + 1)
  let J := PairIndex x z w d
  let P := puncturedForms b x z w n u v J₀
  let R := ResidueTorsion n
  let G := ResidueTorsion (n.gcd (u.gcd v))
  let T := (A → G) × (B → R) × puncturedPairs J₀ n u v
  let first := insertFirstEquiv x z w hxz hzw d
  let second := insertSecondEquiv x z w hxw hzw d
  let C := basisFormEquiv (N := RationalResidue) (n := d + 1) b
  have eval (f : M [⋀^Fin (d + 1)]→ₗ[ℤ] RationalResidue) (S : F) :
      formCoordinates b f S.val = C.symm f S := by
    rw [formCoordinates, dite_eq_left (show S.val.card = d + 1 from S.prop)]
  have torsion (f : P) (S : F) : (n : ℤ) • C.symm f.val S = 0 := by
    have h : (n : ℤ) • f.val = 0 := f.prop.1.2
    have h' := congrArg (fun p => C.symm p S) h
    simpa only [map_smul, Pi.smul_apply, map_zero, Pi.zero_apply] using h'
  have absent (f : P) (S : F) (hx : x ∈ S.val) : formCoordinates b f.val S.val = 0 := by
    have h : f.val.curryLeft (b x) = 0 := f.prop.1.1.1
    rw [eval]
    have hz := (curryLeft_smul_basis_eq_zero_iff b f.val 1 x).mp
      (by simpa only [one_smul] using h) S hx
    simpa only [one_smul] using hz
  have rows (f : P) := (weighted_pair_rows_iff b f.val hxz hxw hzw u v (absent f)).mp
    (show f.val.curryLeft (u • b z + v • b w) = 0 from f.prop.1.1.2)
  let signed (f : P) (S : F) (D : J) (i : I) : R :=
    ⟨insertionSign D.val.val i • C.symm f.val S, by
      change (n : ℤ) • (insertionSign D.val.val i • C.symm f.val S) = 0
      rw [smul_comm, torsion, smul_zero]⟩
  let paired (f : P) (D : J) : R × R :=
    (signed f (first D).val D z, signed f (second D).val D w)
  have first_face (D : J) : (first D).val.val = insert z D.val.val := rfl
  have second_face (D : J) : (second D).val.val = insert w D.val.val := rfl
  have pair_condition (f : P) (D : J) : paired f D ∈ (weightedPair n u v).ker := by
    apply Subtype.ext
    change (u : ℤ) • (insertionSign D.val.val z • C.symm f.val (first D).val) +
      (v : ℤ) • (insertionSign D.val.val w • C.symm f.val (second D).val) = 0
    simpa only [natCast_zsmul, ← eval, first_face, second_face] using
      (rows f).2 D.val D.prop.1 D.prop.2.1 D.prop.2.2
  have exceptional (f : P) : (paired f J₀).1 = 0 := by
    apply Subtype.ext
    change insertionSign J₀.val.val z • C.symm f.val (first J₀).val = 0
    have h : formCoordinates b f.val (insert z J₀.val.val) = 0 := f.prop.2
    rw [← eval, first_face, h, smul_zero]
  let read (f : P) : T :=
    (fun S => ⟨C.symm f.val S.val, by
      have hh := (rows f).1 S.val S.prop.1 S.prop.2.1 S.prop.2.2
      rw [eval] at hh
      apply (gcd_torsion_iff n (u.gcd v) _).mpr
      exact ⟨torsion f S.val, (gcd_torsion_iff u v _).mpr (by
        simpa only [natCast_zsmul] using hh)⟩⟩,
      fun S => ⟨C.symm f.val S.val, torsion f S.val⟩,
      ⟨paired f, by
        intro D _
        by_cases h : D = J₀
        · subst D
          have hm : paired f J₀ ∈ omitFirst n u v := ⟨pair_condition f J₀, exceptional f⟩
          simpa using hm
        · simpa [h] using pair_condition f D⟩)
  let get (p : T) (S : F) : RationalResidue :=
    if hx : x ∈ S.val then 0
    else if hz : z ∈ S.val then
      if hw : w ∈ S.val then p.1 ⟨S, hx, hz, hw⟩
      else
        let D := first.symm ⟨S, hx, hz, hw⟩
        insertionSign D.val.val z • (p.2.2.val D).1.val
    else if hw : w ∈ S.val then
      let D := second.symm ⟨S, hx, hz, hw⟩
      insertionSign D.val.val w • (p.2.2.val D).2.val
    else p.2.1 ⟨S, hx, hz, hw⟩
  have get_first (p : T) (D : J) :
      get p (first D).val = insertionSign D.val.val z • (p.2.2.val D).1.val := by
    have h := (first D).prop
    simp [get, show x ∉ (first D).val.val from h.1,
      show z ∈ (first D).val.val from h.2.1, show w ∉ (first D).val.val from h.2.2]
  have get_second (p : T) (D : J) :
      get p (second D).val = insertionSign D.val.val w • (p.2.2.val D).2.val := by
    have h := (second D).prop
    simp [get, show x ∉ (second D).val.val from h.1,
      show z ∉ (second D).val.val from h.2.1, show w ∈ (second D).val.val from h.2.2]
  have decode (p : T) (S : F) : formCoordinates b (C (get p)) S.val = get p S :=
    (eval _ S).trans (congrFun (C.symm_apply_apply (get p)) S)
  have decode_first (p : T) (D : J) :
      formCoordinates b (C (get p)) (insert z D.val.val) =
        insertionSign D.val.val z • (p.2.2.val D).1.val := by
    rw [← first_face, decode, get_first]
  have decode_second (p : T) (D : J) :
      formCoordinates b (C (get p)) (insert w D.val.val) =
        insertionSign D.val.val w • (p.2.2.val D).2.val := by
    rw [← second_face, decode, get_second]
  have data_pair (p : T) (D : J) : p.2.2.val D ∈ (weightedPair n u v).ker := by
    have h := p.2.2.prop D (Set.mem_univ _)
    by_cases hD : D = J₀
    · subst D
      have he : p.2.2.val J₀ ∈ omitFirst n u v := by simpa using h
      exact he.1
    · simpa [hD] using h
  have data_exception (p : T) : (p.2.2.val J₀).1 = 0 := by
    have h : p.2.2.val J₀ ∈ omitFirst n u v := by
      simpa using p.2.2.prop J₀ (Set.mem_univ _)
    exact h.2
  let write (p : T) : P := ⟨C (get p), by
    have hzero (S : F) (hx : x ∈ S.val) : formCoordinates b (C (get p)) S.val = 0 := by
      rw [decode]
      simp [get, hx]
    refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
    · change (C (get p)).curryLeft (b x) = 0
      simpa only [one_smul] using (curryLeft_smul_basis_eq_zero_iff b (C (get p)) 1 x).mpr
        (fun S hx => by
          have h := hzero S hx
          rw [eval] at h
          simpa only [one_smul] using h)
    · exact (weighted_pair_rows_iff b (C (get p)) hxz hxw hzw u v hzero).mpr
        ⟨fun S hx hz hw => by
          rw [decode]
          have hg := (gcd_torsion_iff n (u.gcd v) _).mp (p.1 ⟨S, hx, hz, hw⟩).prop
          simpa only [get, dite_eq_right hx, dite_eq_left hz, dite_eq_left hw, natCast_zsmul] using
            (gcd_torsion_iff u v _).mp hg.2,
          fun S hx hz hw => by
            let D : J := ⟨S, hx, hz, hw⟩
            have h : weightedPair n u v (p.2.2.val D) = 0 := data_pair p D
            have hc := congrArg Subtype.val h
            change (u : ℤ) • (p.2.2.val D).1.val + (v : ℤ) • (p.2.2.val D).2.val = 0 at hc
            change u • (insertionSign D.val.val z •
              formCoordinates b (C (get p)) (insert z D.val.val)) +
              v • (insertionSign D.val.val w •
              formCoordinates b (C (get p)) (insert w D.val.val)) = 0
            rwa [decode_first, decode_second, sign_twice, sign_twice, ← natCast_zsmul,
              ← natCast_zsmul]⟩
    · change (n : ℤ) • C (get p) = 0
      rw [← map_zsmul]
      apply (map_eq_zero_iff C C.injective).mpr
      funext S
      change (n : ℤ) • get p S = 0
      unfold get
      split_ifs with hx hz hw hw
      · exact smul_zero _
      · exact ((gcd_torsion_iff n (u.gcd v) _).mp (p.1 ⟨S, hx, hz, hw⟩).prop).1
      · let D := first.symm ⟨S, hx, hz, hw⟩
        have h : (n : ℤ) • (p.2.2.val D).1.val = 0 := (p.2.2.val D).1.prop
        change (n : ℤ) • (insertionSign D.val.val z • (p.2.2.val D).1.val) = 0
        rw [smul_comm, h, smul_zero]
      · let D := second.symm ⟨S, hx, hz, hw⟩
        have h : (n : ℤ) • (p.2.2.val D).2.val = 0 := (p.2.2.val D).2.prop
        change (n : ℤ) • (insertionSign D.val.val w • (p.2.2.val D).2.val) = 0
        rw [smul_comm, h, smul_zero]
      · exact (p.2.1 ⟨S, hx, hz, hw⟩).prop
    · change formCoordinates b (C (get p)) (insert z J₀.val.val) = 0
      rw [decode_first, data_exception, Submodule.coe_zero, smul_zero]⟩
  have left (f : P) : write (read f) = f := by
    apply Subtype.ext
    change C (get (read f)) = f.val
    apply C.symm.injective
    rw [C.symm_apply_apply]
    funext S
    unfold get
    split_ifs with hx hz hw hw
    · rw [← eval, absent f S hx]
    · rfl
    · let D := first.symm ⟨S, hx, hz, hw⟩
      change insertionSign D.val.val z •
        (insertionSign D.val.val z • C.symm f.val (first D).val) = C.symm f.val S
      rw [sign_twice, first.apply_symm_apply]
    · let D := second.symm ⟨S, hx, hz, hw⟩
      change insertionSign D.val.val w •
        (insertionSign D.val.val w • C.symm f.val (second D).val) = C.symm f.val S
      rw [sign_twice, second.apply_symm_apply]
    · rfl
  have right (p : T) : read (write p) = p := by
    apply Prod.ext
    · funext S
      apply Subtype.ext
      change C.symm (C (get p)) S.val = (p.1 S).val
      rw [C.symm_apply_apply]
      exact by simp [get, show x ∉ S.val.val from S.prop.1,
        show z ∈ S.val.val from S.prop.2.1, show w ∈ S.val.val from S.prop.2.2]
    · apply Prod.ext
      · funext S
        apply Subtype.ext
        change C.symm (C (get p)) S.val = (p.2.1 S).val
        rw [C.symm_apply_apply]
        exact by simp [get, show x ∉ S.val.val from S.prop.1,
          show z ∉ S.val.val from S.prop.2.1, show w ∉ S.val.val from S.prop.2.2]
      · apply Subtype.ext
        funext D
        apply Prod.ext
        · apply Subtype.ext
          change insertionSign D.val.val z • C.symm (C (get p)) (first D).val = _
          rw [C.symm_apply_apply, get_first, sign_twice]
        · apply Subtype.ext
          change insertionSign D.val.val w • C.symm (C (get p)) (second D).val = _
          rw [C.symm_apply_apply, get_second, sign_twice]
  refine ⟨{ toFun := read, invFun := write, left_inv := left, right_inv := right
            map_add' := ?_, map_smul' := ?_ }⟩
  · intro f g
    apply Prod.ext
    · funext S
      apply Subtype.ext
      exact congrFun (C.symm.map_add f.val g.val) S.val
    · apply Prod.ext
      · funext S
        apply Subtype.ext
        exact congrFun (C.symm.map_add f.val g.val) S.val
      · apply Subtype.ext
        funext D
        apply Prod.ext
        · apply Subtype.ext
          change insertionSign D.val.val z • C.symm (f.val + g.val) (first D).val = _
          rw [map_add, Pi.add_apply, smul_add]
          rfl
        · apply Subtype.ext
          change insertionSign D.val.val w • C.symm (f.val + g.val) (second D).val = _
          rw [map_add, Pi.add_apply, smul_add]
          rfl
  · intro t f
    apply Prod.ext
    · funext S
      apply Subtype.ext
      exact congrFun (C.symm.map_smul t f.val) S.val
    · apply Prod.ext
      · funext S
        apply Subtype.ext
        exact congrFun (C.symm.map_smul t f.val) S.val
      · apply Subtype.ext
        funext D
        apply Prod.ext
        · apply Subtype.ext
          change insertionSign D.val.val z • C.symm (t • f.val) (first D).val = _
          rw [map_smul, Pi.smul_apply, smul_comm]
          rfl
        · apply Subtype.ext
          change insertionSign D.val.val w • C.symm (t • f.val) (second D).val = _
          rw [map_smul, Pi.smul_apply, smul_comm]
          rfl

end D5.S3.Combinatorics.Matroids.PuncturedCircuitSplit
