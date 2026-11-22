/- GID: D5/S3/Combinatorics/Matroids/RankTwoCircuitInvariantFactors
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Matroids/RankTwoCircuitInvariantFactors
   mirror-E: none(waiver:algebraic-inference)
   anchors: []
   utility: none
   digest: Invariant factors of the rank-two joint circuit lifting obstruction. -/

module

public import D5.S3.Combinatorics.Matroids.RankTwoCircuitTorsion
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Tactic.Module

/-! # Invariant factors of the rank-two lifting obstruction -/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Finset

namespace D5.S3.Combinatorics.Matroids.RankTwoCircuitInvariantFactors

open RationalJointCircuitImage (RationalResidue rationalResidue rationalResidue_eq_zero)
open RankTwoCircuitTorsion (HasClassBases normalizedClassPotentials
  rank_two_lifting_obstruction_potentials)
open JointCircuitLiftingObstruction (JointSaturatedImage JointImageInSaturation)

variable {A : Type*} [AddCommGroup A]

/-- A unimodular change of two coordinates, with the weighted sum as its first row
after multiplication by the gcd. -/
private theorem exists_gcd_coordinates (a b : ℕ) (ha : 0 < a) :
    ∃ coordinates : (A × A) ≃ₗ[ℤ] (A × A),
      ∀ x y, (a.gcd b) • (coordinates (x, y)).1 = a • x + b • y := by
  obtain ⟨u, hu⟩ := Nat.gcd_dvd_left a b
  obtain ⟨v, hv⟩ := Nat.gcd_dvd_right a b
  let s := Nat.gcdA a b
  let t := Nat.gcdB a b
  have hg : ((a.gcd b : ℕ) : ℤ) ≠ 0 := by
    exact_mod_cast (Nat.gcd_pos_of_pos_left b ha).ne'
  have hu' : (a : ℤ) = (a.gcd b : ℤ) * (u : ℤ) := by exact_mod_cast hu
  have hv' : (b : ℤ) = (a.gcd b : ℤ) * (v : ℤ) := by exact_mod_cast hv
  have hdet : (u : ℤ) * s + (v : ℤ) * t = 1 := by
    apply mul_left_cancel₀ hg
    rw [mul_add, ← mul_assoc, ← mul_assoc, ← hu', ← hv', mul_one]
    exact (Nat.gcd_eq_gcd_ab a b).symm
  let forward : A × A → A × A := fun p =>
    ((u : ℤ) • p.1 + (v : ℤ) • p.2, -t • p.1 + s • p.2)
  let backward : A × A → A × A := fun p =>
    (s • p.1 - (v : ℤ) • p.2, t • p.1 + (u : ℤ) • p.2)
  have hleft (p : A × A) : backward (forward p) = p := by
    apply Prod.ext
    · change s • ((u : ℤ) • p.1 + (v : ℤ) • p.2) -
        (v : ℤ) • (-t • p.1 + s • p.2) = p.1
      calc
        _ = ((u : ℤ) * s + (v : ℤ) * t) • p.1 := by module
        _ = _ := by rw [hdet, one_smul]
    · change t • ((u : ℤ) • p.1 + (v : ℤ) • p.2) +
        (u : ℤ) • (-t • p.1 + s • p.2) = p.2
      calc
        _ = ((u : ℤ) * s + (v : ℤ) * t) • p.2 := by module
        _ = _ := by rw [hdet, one_smul]
  have hright (p : A × A) : forward (backward p) = p := by
    apply Prod.ext
    · change (u : ℤ) • (s • p.1 - (v : ℤ) • p.2) +
        (v : ℤ) • (t • p.1 + (u : ℤ) • p.2) = p.1
      calc
        _ = ((u : ℤ) * s + (v : ℤ) * t) • p.1 := by module
        _ = _ := by rw [hdet, one_smul]
    · change -t • (s • p.1 - (v : ℤ) • p.2) +
        s • (t • p.1 + (u : ℤ) • p.2) = p.2
      calc
        _ = ((u : ℤ) * s + (v : ℤ) * t) • p.2 := by module
        _ = _ := by rw [hdet, one_smul]
  let coordinates : (A × A) ≃ₗ[ℤ] (A × A) :=
    { toFun := forward
      invFun := backward
      left_inv := hleft
      right_inv := hright
      map_add' := fun p q => Prod.ext (by dsimp [forward]; module) (by dsimp [forward]; module)
      map_smul' := fun n p => Prod.ext (by dsimp [forward]; module) (by dsimp [forward]; module) }
  refine ⟨coordinates, fun x y => ?_⟩
  change (a.gcd b : ℕ) • ((u : ℤ) • x + (v : ℤ) • y) = a • x + b • y
  rw [← natCast_zsmul, smul_add, smul_smul, smul_smul, ← hu', ← hv', natCast_zsmul,
    natCast_zsmul]

private theorem gcd_univ_fin_succ {k : ℕ} (weight : Fin (k + 1) → ℕ) :
    univ.gcd weight = (weight 0).gcd (univ.gcd fun i : Fin k => weight i.succ) := by
  apply Nat.dvd_antisymm
  · exact Nat.dvd_gcd (gcd_dvd (mem_univ _)) (dvd_gcd fun i _ => gcd_dvd (mem_univ i.succ))
  · apply Finset.dvd_gcd
    intro i _
    refine Fin.cases ?_ (fun j => ?_) i
    · exact Nat.gcd_dvd_left _ _
    · exact (Nat.gcd_dvd_right _ _).trans (gcd_dvd (mem_univ j))

/-- Reduce a finite weighted sum to multiplication by the gcd in one coordinate. -/
theorem exists_sum_coordinates (k : ℕ) (weight : Fin (k + 1) → ℕ)
    (hpos : ∀ i, 0 < weight i) :
    ∃ coordinates : (Fin (k + 1) → A) ≃ₗ[ℤ] (A × (Fin k → A)),
      ∀ f, (univ.gcd weight) • (coordinates f).1 = ∑ i, weight i • f i := by
  induction k with
  | zero =>
      exact ⟨(Fin.consLinearEquiv ℤ (fun _ : Fin 1 => A)).symm, fun f => by simp⟩
  | succ k ih =>
      let tailWeight : Fin (k + 1) → ℕ := fun i => weight i.succ
      obtain ⟨tail, htail⟩ := ih tailWeight (fun i => hpos i.succ)
      obtain ⟨head, hhead⟩ := exists_gcd_coordinates (A := A) (weight 0) (univ.gcd tailWeight)
        (hpos 0)
      let assoc := LinearEquiv.prodAssoc ℤ A A (Fin k → A)
      let coordinates := (Fin.consLinearEquiv ℤ (fun _ : Fin (k + 2) => A)).symm.trans
        (((LinearEquiv.refl ℤ A).prodCongr tail).trans
          (assoc.symm.trans ((head.prodCongr (LinearEquiv.refl ℤ (Fin k → A))).trans
            (assoc.trans ((LinearEquiv.refl ℤ A).prodCongr
              (Fin.consLinearEquiv ℤ (fun _ : Fin (k + 1) => A)))))))
      refine ⟨coordinates, fun f => ?_⟩
      rw [gcd_univ_fin_succ]
      change (weight 0).gcd (univ.gcd tailWeight) •
        (head (f 0, (tail (fun i => f i.succ)).1)).1 = _
      rw [hhead, htail]
      exact (Fin.sum_univ_succ (fun i => weight i • f i)).symm

abbrev ResidueTorsion (n : ℕ) := Submodule.torsionBy ℤ RationalResidue (n : ℤ)

private def integerFraction (n : ℕ) : ℤ →+ RationalResidue where
  toFun a := rationalResidue ((a : ℚ) / n)
  map_zero' := by simp
  map_add' a b := by simp [add_div]

theorem residueTorsion_equiv_zmod (n : ℕ) (hn : n ≠ 0) :
    Nonempty (ResidueTorsion n ≃ₗ[ℤ] ZMod n) := by
  have hnq : (n : ℚ) ≠ 0 := by exact_mod_cast hn
  have hzero (a : ℤ) : integerFraction n a = 0 ↔ (n : ℤ) ∣ a := by
    change rationalResidue ((a : ℚ) / n) = 0 ↔ _
    rw [rationalResidue_eq_zero]
    constructor
    · rintro ⟨b, hb⟩
      refine ⟨b, ?_⟩
      have h := (eq_div_iff hnq).mp hb
      exact_mod_cast ((mul_comm (n : ℚ) (b : ℚ)).trans h).symm
    · rintro ⟨b, rfl⟩
      exact ⟨b, (eq_div_iff hnq).mpr (by push_cast; ring)⟩
  let lift := ZMod.lift n ⟨integerFraction n, (hzero _).mpr dvd_rfl⟩
  have hlift (a : ℤ) : lift (a : ZMod n) = integerFraction n a :=
    ZMod.lift_coe _ _ _
  let into := lift.toIntLinearMap.codRestrict (ResidueTorsion n) (fun x => by
    change (n : ℤ) • lift x = 0
    rw [← map_zsmul, natCast_zsmul, ← Nat.cast_smul_eq_nsmul (ZMod n), ZMod.natCast_self,
      zero_smul, map_zero])
  have hinj : Function.Injective into := by
    apply (injective_iff_map_eq_zero into).mpr
    intro x hx
    obtain ⟨a, rfl⟩ := (show Function.Surjective (Int.castAddHom (ZMod n)) from
      fun y => ⟨_, ZMod.intCast_zmod_cast y⟩) x
    have ha : integerFraction n a = 0 := by
      have h := congrArg Subtype.val hx
      exact (hlift a).symm.trans h
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr ((hzero a).mp ha)
  have hsurj : Function.Surjective into := by
    intro x
    obtain ⟨q, hq⟩ := (show Function.Surjective rationalResidue from
      QuotientAddGroup.mk'_surjective _) x.val
    have ht : rationalResidue ((n : ℚ) * q) = 0 := by
      rw [← Int.cast_natCast, ← zsmul_eq_mul, map_zsmul, hq]
      exact x.prop
    obtain ⟨a, ha⟩ := rationalResidue_eq_zero.mp ht
    refine ⟨(a : ZMod n), Subtype.ext ?_⟩
    change lift (a : ZMod n) = x.val
    rw [hlift]
    exact (congrArg rationalResidue ((div_eq_iff hnq).mpr (ha.trans (mul_comm _ _)))).trans hq
  exact ⟨(LinearEquiv.ofBijective into ⟨hinj, hsurj⟩).symm⟩

theorem gcd_torsion_iff (n d : ℕ) (x : A) :
    (n.gcd d : ℤ) • x = 0 ↔ (n : ℤ) • x = 0 ∧ (d : ℤ) • x = 0 := by
  constructor
  · intro h
    have hdvd (a : ℕ) (ha : n.gcd d ∣ a) : (a : ℤ) • x = 0 := by
      obtain ⟨b, hb⟩ := ha
      have hcast : (a : ℤ) = (b : ℤ) * (n.gcd d : ℤ) := by
        exact_mod_cast hb.trans (mul_comm _ _)
      rw [hcast, mul_smul, h, smul_zero]
    exact ⟨hdvd n (Nat.gcd_dvd_left _ _), hdvd d (Nat.gcd_dvd_right _ _)⟩
  · rintro ⟨hn, hd⟩
    rw [Nat.gcd_eq_gcd_ab, add_smul, mul_comm (n : ℤ), mul_comm (d : ℤ),
      mul_smul, mul_smul, hn, hd, smul_zero, smul_zero, add_zero]

private def weightedSum (A : Type*) [AddCommGroup A] {k : ℕ}
    (weight : Fin k → ℕ) : (Fin k → A) →ₗ[ℤ] A :=
  ∑ i, weight i • LinearMap.proj i

private lemma weightedSum_apply {k : ℕ} (weight : Fin k → ℕ) (f : Fin k → A) :
    weightedSum A weight f = ∑ i, weight i • f i := by
  simp [weightedSum, LinearMap.sum_apply]

private theorem weightedTorsion_equiv (n k : ℕ) (weight : Fin (k + 1) → ℕ)
    (hpos : ∀ i, 0 < weight i) :
    Nonempty ((weightedSum (ResidueTorsion n) weight).ker ≃ₗ[ℤ]
      ((ResidueTorsion (n.gcd (univ.gcd weight))) × (Fin k → ResidueTorsion n))) := by
  let d := univ.gcd weight
  obtain ⟨coordinate, hcoordinate⟩ := exists_sum_coordinates (A := ResidueTorsion n) k weight hpos
  have hm (x : Fin (k + 1) → ResidueTorsion n) :
      x ∈ (weightedSum (ResidueTorsion n) weight).ker ↔
        (coordinate x).1.val ∈ ResidueTorsion (n.gcd d) := by
    rw [LinearMap.mem_ker, weightedSum_apply, ← hcoordinate]
    rw [← natCast_zsmul]
    constructor
    · intro hx
      exact (gcd_torsion_iff n d _).mpr ⟨(coordinate x).1.prop, congrArg Subtype.val hx⟩
    · intro hx
      exact Subtype.ext ((gcd_torsion_iff n d _).mp hx).2
  have hfirst (x : ResidueTorsion (n.gcd d)) : x.val ∈ ResidueTorsion n :=
    ((gcd_torsion_iff n d _).mp x.prop).1
  let transform (x : (weightedSum (ResidueTorsion n) weight).ker) :
      ResidueTorsion (n.gcd d) × (Fin k → ResidueTorsion n) :=
    (⟨(coordinate x.val).1.val, (hm x.val).mp x.prop⟩, (coordinate x.val).2)
  let inverse (x : ResidueTorsion (n.gcd d) × (Fin k → ResidueTorsion n)) :
      (weightedSum (ResidueTorsion n) weight).ker :=
    ⟨coordinate.symm (⟨x.1.val, hfirst x.1⟩, x.2), (hm _).mpr (by simp [x.1.prop])⟩
  refine ⟨{ toFun := transform
            invFun := inverse
            left_inv := ?_
            right_inv := ?_
            map_add' := ?_
            map_smul' := ?_ }⟩
  · intro x y
    apply Prod.ext
    · apply Subtype.ext
      exact congrArg (fun p : ResidueTorsion n × (Fin k → ResidueTorsion n) => p.1.val)
        (map_add coordinate x.val y.val)
    · exact congrArg (fun p : ResidueTorsion n × (Fin k → ResidueTorsion n) => p.2)
        (map_add coordinate x.val y.val)
  · intro m x
    apply Prod.ext
    · apply Subtype.ext
      exact congrArg (fun p : ResidueTorsion n × (Fin k → ResidueTorsion n) => p.1.val)
        (map_smul coordinate m x.val)
    · exact congrArg (fun p : ResidueTorsion n × (Fin k → ResidueTorsion n) => p.2)
        (map_smul coordinate m x.val)
  · intro x
    apply Subtype.ext
    exact coordinate.symm_apply_apply x.val
  · intro x
    apply Prod.ext
    · apply Subtype.ext
      exact congrArg (fun p : ResidueTorsion n × (Fin k → ResidueTorsion n) => p.1.val)
        (coordinate.apply_symm_apply (⟨x.1.val, hfirst x.1⟩, x.2))
    · exact congrArg (fun p : ResidueTorsion n × (Fin k → ResidueTorsion n) => p.2)
        (coordinate.apply_symm_apply (⟨x.1.val, hfirst x.1⟩, x.2))

/-- The number of vertices in a parallel class. -/
def classSize {V : Type*} [Fintype V] {k : ℕ}
    (part : V → Fin k) (i : Fin k) : ℕ :=
  (univ.filter (fun v => part v = i)).card

private theorem normalizedPotentials_equiv_weighted {V : Type*} [Fintype V]
    {k : ℕ} (part : V → Fin (k + 2)) :
    Nonempty (normalizedClassPotentials part 0 ≃ₗ[ℤ]
      (weightedSum (ResidueTorsion (Fintype.card V)) (fun i : Fin (k + 1) =>
        classSize part i.succ)).ker) := by
  let A := ResidueTorsion (Fintype.card V)
  let weight (i : Fin (k + 1)) := classSize part i.succ
  let forward (f : normalizedClassPotentials part 0) : (weightedSum A weight).ker := by
    let tail : Fin (k + 1) → A := fun i =>
      ⟨f.val i.succ, by rw [Submodule.mem_torsionBy_iff, natCast_zsmul]; exact f.prop.2.1 i.succ⟩
    refine ⟨tail, ?_⟩
    rw [LinearMap.mem_ker, weightedSum_apply]
    apply Subtype.ext
    have hm : ∑ i, classSize part i • f.val i = 0 := f.prop.2.2
    rw [Fin.sum_univ_succ, f.prop.1, smul_zero, zero_add] at hm
    simpa only [Submodule.coe_sum, Submodule.coe_smul_of_tower, tail, weight,
      Submodule.coe_zero] using hm
  let inverse (f : (weightedSum A weight).ker) : normalizedClassPotentials part 0 := by
    let head : Fin (k + 2) → RationalResidue := Fin.cons 0 (fun i => (f.val i).val)
    refine ⟨head, Fin.cons_zero _ _, ?_, ?_⟩
    · intro i
      refine Fin.cases (by simp [head]) (fun j => ?_) i
      simp only [head, Fin.cons_succ]
      have hj : (Fintype.card V : ℤ) • (f.val j).val = 0 := (f.val j).prop
      simpa only [natCast_zsmul] using hj
    · have hf : ∑ i, weight i • f.val i = 0 := (weightedSum_apply weight f.val) ▸ f.prop
      have h := congrArg (fun a : A => a.val) hf
      change ∑ i, classSize part i • head i = 0
      rw [Fin.sum_univ_succ]
      simpa only [head, Fin.cons_zero, smul_zero, zero_add, Fin.cons_succ,
        Submodule.coe_sum, Submodule.coe_smul_of_tower, weight, Submodule.coe_zero] using h
  refine ⟨{ toFun := forward
            invFun := inverse
            map_add' := fun f g => by
              apply Subtype.ext
              funext i
              apply Subtype.ext
              simp only [forward, Submodule.coe_add, Pi.add_apply]
            map_smul' := fun n f => by
              apply Subtype.ext
              funext i
              apply Subtype.ext
              simp only [forward, Submodule.coe_smul, Pi.smul_apply, RingHom.id_apply]
            left_inv := ?_
            right_inv := ?_ }⟩
  · intro f
    apply Subtype.ext
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa only [inverse, Fin.cons_zero] using f.prop.1.symm
    · simp [inverse, forward]
  · intro f
    apply Subtype.ext
    funext i
    apply Subtype.ext
    simp [inverse, forward]

theorem gcd_card_tail_eq {V : Type*} [Fintype V] {k : ℕ}
    (part : V → Fin (k + 2)) :
    (Fintype.card V).gcd (univ.gcd fun i : Fin (k + 1) => classSize part i.succ) =
      univ.gcd (classSize part) := by
  let weight := classSize part
  let tailWeight (i : Fin (k + 1)) := weight i.succ
  let d := univ.gcd tailWeight
  have hcard : Fintype.card V = ∑ i, weight i := by
    classical
    simpa only [weight, classSize, card_univ] using
      (card_eq_sum_card_fiberwise (s := (univ : Finset V))
        (t := (univ : Finset (Fin (k + 2)))) (f := part) (fun _ _ => mem_univ _))
  have htail : d ∣ ∑ i, tailWeight i :=
    Finset.dvd_sum fun i _ => gcd_dvd (mem_univ i)
  have hhead : Fintype.card V = weight 0 + ∑ i, tailWeight i :=
    hcard.trans (Fin.sum_univ_succ weight)
  change (Fintype.card V).gcd d = univ.gcd weight
  rw [gcd_univ_fin_succ]
  apply Nat.dvd_antisymm
  · apply Nat.dvd_gcd
    · have h := Nat.dvd_sub (Nat.gcd_dvd_left (Fintype.card V) d)
        ((Nat.gcd_dvd_right (Fintype.card V) d).trans htail)
      simpa [hhead] using h
    · exact Nat.gcd_dvd_right _ _
  · apply Nat.dvd_gcd
    · rw [hhead]
      exact Nat.dvd_add (Nat.gcd_dvd_left _ _) ((Nat.gcd_dvd_right _ _).trans htail)
    · exact Nat.gcd_dvd_right _ _

/-- A loopless rank-two matroid with `k + 2` parallel classes has `k` ground-size
cyclic factors and one cyclic factor given by the gcd of the class sizes. -/
theorem rank_two_lifting_obstruction_invariant_factors {V : Type*}
    [Fintype V] [LinearOrder V] {k : ℕ} {M : Matroid V} {part : V → Fin (k + 2)}
    (hbases : HasClassBases M part) (hsurj : Function.Surjective part) :
    Nonempty ((JointSaturatedImage M ⧸ JointImageInSaturation M) ≃ₗ[ℤ]
      (ZMod (univ.gcd (classSize part)) × (Fin k → ZMod (Fintype.card V)))) := by
  let n := Fintype.card V
  let weight (i : Fin (k + 1)) := classSize part i.succ
  have hpositive (i : Fin (k + 2)) : 0 < classSize part i := by
    obtain ⟨v, hv⟩ := hsurj i
    exact card_pos.mpr ⟨v, mem_filter.mpr ⟨mem_univ _, hv⟩⟩
  have hn : n ≠ 0 := by
    obtain ⟨v, _⟩ := hsurj 0
    exact (Fintype.card_pos_iff.mpr ⟨v⟩).ne'
  have hg : univ.gcd (classSize part) ≠ 0 := by
    intro hz
    have h := Finset.gcd_dvd (f := classSize part) (mem_univ (0 : Fin (k + 2)))
    rw [hz, zero_dvd_iff] at h
    exact (hpositive 0).ne' h
  obtain ⟨potentials⟩ := rank_two_lifting_obstruction_potentials hbases hsurj 0
  obtain ⟨weighted⟩ := normalizedPotentials_equiv_weighted part
  obtain ⟨diagonal⟩ := weightedTorsion_equiv n k weight (fun i => hpositive i.succ)
  have hgcd : n.gcd (univ.gcd weight) = univ.gcd (classSize part) := gcd_card_tail_eq part
  rw [hgcd] at diagonal
  obtain ⟨first⟩ := residueTorsion_equiv_zmod _ hg
  obtain ⟨rest⟩ := residueTorsion_equiv_zmod n hn
  exact ⟨potentials.trans (weighted.trans (diagonal.trans
    (first.prodCongr (LinearEquiv.piCongrRight fun _ => rest))))⟩

end D5.S3.Combinatorics.Matroids.RankTwoCircuitInvariantFactors
