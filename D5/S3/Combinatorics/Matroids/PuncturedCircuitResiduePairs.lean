/- GID: D5/S3/Combinatorics/Matroids/PuncturedCircuitResiduePairs
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Matroids/PuncturedCircuitResiduePairs
   mirror-E: none(waiver:algebraic-inference)
   anchors: []
   utility: none
   digest: Two-weight residue equations with one distinguished coefficient omitted. -/

module

public import D5.S3.Combinatorics.Matroids.RankTwoCircuitInvariantFactors
public import D5.S3.Combinatorics.Matroids.UniformCircuitResidueForms
public import Mathlib.Algebra.Module.Submodule.Equiv

/-! Weighted pairs and the loss of a cyclic factor when the first coefficient vanishes. -/

@[expose] public section

namespace D5.S3.Combinatorics.Matroids.PuncturedCircuitResiduePairs

open Finset
open RankTwoCircuitInvariantFactors (ResidueTorsion weightedSum weightedTorsion_equiv gcd_torsion_iff)
open RationalJointCircuitImage (RationalResidue)

set_option autoImplicit false

/-- The scalar equation for a pair of residue coordinates. -/
def weightedPair (n a b : ℕ) :
    (ResidueTorsion n × ResidueTorsion n) →ₗ[ℤ] ResidueTorsion n :=
  (a : ℤ) • LinearMap.fst ℤ _ _ + (b : ℤ) • LinearMap.snd ℤ _ _

private lemma pair_gcd (a b : ℕ) : (univ : Finset (Fin 2)).gcd (Fin.cons a (fun _ => b)) =
    a.gcd b := by
  rw [show (univ : Finset (Fin 2)) = {0, 1} by decide, gcd_insert]
  rw [gcd_singleton]
  let weight : Fin 2 → ℕ := Fin.cons a (fun _ => b)
  change GCDMonoid.gcd (weight 0) (normalize (weight 1)) = a.gcd b
  have h₀ : weight 0 = a := rfl
  have h₁ : weight 1 = b := rfl
  rw [h₀, h₁, normalize_eq]
  rfl

/-- A weighted pair contributes one common-gcd coordinate and one total-order
coordinate. -/
theorem weighted_pair_equiv (n a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    Nonempty ((weightedPair n a b).ker ≃ₗ[ℤ]
      (ResidueTorsion (n.gcd (a.gcd b)) × ResidueTorsion n)) := by
  let A := ResidueTorsion n
  let tail := LinearEquiv.piUnique ℤ (fun _ : Fin 1 => A)
  let expand := ((LinearEquiv.refl ℤ A).prodCongr tail.symm).trans
    (Fin.consLinearEquiv ℤ (fun _ : Fin 2 => A))
  let weight : Fin 2 → ℕ := Fin.cons a (fun _ => b)
  have heq (p : A × A) :
      weightedSum A weight (expand p) = weightedPair n a b p := by
    have ht : tail.symm p.2 0 = p.2 := rfl
    simp [weightedSum, LinearMap.sum_apply, Fin.sum_univ_two, weight,
      expand, ht, weightedPair, natCast_zsmul]
  have hmap : (weightedPair n a b).ker.map expand.toLinearMap = (weightedSum A weight).ker := by
    rw [Submodule.map_equiv_eq_comap_symm]
    apply Submodule.ext
    intro p
    change weightedPair n a b (expand.symm p) = 0 ↔ weightedSum A weight p = 0
    rw [← heq, expand.apply_symm_apply]
  obtain ⟨diagonal⟩ := weightedTorsion_equiv n 1 weight (by
    intro i
    exact Fin.cases (by simpa [weight] using ha) (fun j => by simpa [weight] using hb) i)
  have hgcd : univ.gcd weight = a.gcd b := pair_gcd a b
  rw [hgcd] at diagonal
  exact ⟨(expand.ofSubmodules _ _ hmap).trans
    (diagonal.trans ((LinearEquiv.refl ℤ _).prodCongr tail))⟩

/-- The weighted pairs whose first coordinate vanishes. -/
def omitFirst (n a b : ℕ) : Submodule ℤ (ResidueTorsion n × ResidueTorsion n) :=
  (weightedPair n a b).ker ⊓ (LinearMap.fst ℤ (ResidueTorsion n) (ResidueTorsion n)).ker

/-- When the first coefficient vanishes, the remaining coordinate has order
dividing the gcd of the total size and the second weight. -/
noncomputable def omitFirstEquiv (n a b : ℕ) :
    omitFirst n a b ≃ₗ[ℤ] ResidueTorsion (n.gcd b) := by
  have hright (p : omitFirst n a b) : (b : ℤ) • p.val.2.val = 0 := by
    have hz : weightedPair n a b p.val = 0 := p.prop.1
    have hx : p.val.1 = 0 := p.prop.2
    have hz' : (b : ℤ) • p.val.2 = 0 := by
      simpa only [weightedPair, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.fst_apply,
        LinearMap.snd_apply, hx, smul_zero, zero_add] using hz
    exact congrArg Subtype.val hz'
  let into (p : omitFirst n a b) : ResidueTorsion (n.gcd b) :=
    ⟨p.val.2.val, (gcd_torsion_iff n b _).mpr ⟨p.val.2.prop, hright p⟩⟩
  let out (p : ResidueTorsion (n.gcd b)) : omitFirst n a b := by
    obtain ⟨hn, hb⟩ := (gcd_torsion_iff n b _).mp p.prop
    refine ⟨(0, ⟨p.val, hn⟩), ?_, rfl⟩
    change weightedPair n a b _ = 0
    apply Subtype.ext
    simpa [weightedPair] using hb
  refine {
    toFun := into
    invFun := out
    left_inv := fun p => Subtype.ext (Prod.ext p.prop.2.symm rfl)
    right_inv := fun p => Subtype.ext rfl
    map_add' := fun _ _ => Subtype.ext rfl
    map_smul' := fun _ _ => Subtype.ext rfl }

variable {J : Type*}

/-- The exceptional pair obeys the same weighted equation and also has first
coordinate zero. -/
def puncturedPairs [DecidableEq J] (star : J) (n a b : ℕ) :
    Submodule ℤ (J → ResidueTorsion n × ResidueTorsion n) :=
  Submodule.pi Set.univ (fun j => if j = star then omitFirst n a b else (weightedPair n a b).ker)

/-- A family of weighted pairs contributes one factor of each usual order for
each ordinary pair, and a single outside-gcd factor for the distinguished pair. -/
theorem punctured_pairs_equiv [DecidableEq J] (star : J) (n a b : ℕ)
    (ha : 0 < a) (hb : 0 < b) :
    Nonempty (puncturedPairs star n a b ≃ₗ[ℤ]
      (({j : J // j ≠ star} → ResidueTorsion (n.gcd (a.gcd b)) × ResidueTorsion n) ×
        ResidueTorsion (n.gcd b))) := by
  let P := puncturedPairs star n a b
  let K := (weightedPair n a b).ker
  let X := {j : J // j ≠ star}
  let T := (X → K) × omitFirst n a b
  let read : P → T := fun f =>
    ⟨fun j => ⟨f.val j.val, by
        have hm := f.prop j.val (Set.mem_univ _)
        simpa [K, j.prop] using hm⟩,
      ⟨f.val star, by simpa using f.prop star (Set.mem_univ _)⟩⟩
  let assemble (g : T) : J → ResidueTorsion n × ResidueTorsion n :=
    fun j => if h : j = star then g.2.val else (g.1 ⟨j, h⟩).val
  let write (g : T) : P := ⟨assemble g, by
    intro j _
    by_cases h : j = star
    · simp [assemble, h]
    · simp [assemble, h]⟩
  let eqv : P ≃ₗ[ℤ] T :=
    { toFun := read
      invFun := write
      left_inv := by
        intro f
        apply Subtype.ext
        funext j
        by_cases h : j = star <;> simp [write, read, assemble, h]
      right_inv := by
        intro g
        apply Prod.ext
        · funext j
          apply Subtype.ext
          simp [read, write, assemble, j.prop]
        · apply Subtype.ext
          simp [read, write, assemble]
      map_add' := fun f g => rfl
      map_smul' := fun d f => rfl }
  obtain ⟨pair⟩ := weighted_pair_equiv n a b ha hb
  exact ⟨eqv.trans ((LinearEquiv.piCongrRight (fun _ : X => pair)).prodCongr
    (omitFirstEquiv n a b))⟩

open UniformCircuitResidueForms (formCoordinates curryLeft_weighted_basis
  basisFormEquiv basisFormEquiv_symm_apply)
open Set.powersetCard (ofFinEmbEquiv)
open D5.S3.HomologicalAlgebra.OrderedFaceSign (insertionSign)

variable {I M N : Type*} [Finite I] [LinearOrder I] [AddCommGroup M] [AddCommGroup N]
variable {d : ℕ}

/-- Inserting a vector supported on two basis elements gives the two signed
coordinate terms, with a term omitted when that index is already present. -/
theorem curry_weighted_pair_apply (basis : Module.Basis I ℤ M)
    (f : M [⋀^Fin (d + 1)]→ₗ[ℤ] N) (u v : ℕ) {z w : I} (hzw : z ≠ w)
    (J : Set.powersetCard I d) :
    f.curryLeft (u • basis z + v • basis w) (basis ∘ ofFinEmbEquiv.symm J) =
      (if z ∈ J.val then 0 else
        insertionSign J.val z • (u • formCoordinates basis f (insert z J.val))) +
      (if w ∈ J.val then 0 else
        insertionSign J.val w • (v • formCoordinates basis f (insert w J.val))) := by
  let _ := Fintype.ofFinite I
  let weight : I → ℕ := fun i => if i = z then u else if i = w then v else 0
  have hweight (i : I) (hi : i ∉ ({z, w} : Finset I)) : weight i = 0 := by
    by_cases hz : i = z
    · exact (hi (by simp [hz])).elim
    · have hw : i ≠ w := fun h => hi (by simp [h])
      simp [weight, hz, hw]
  have hvec : (∑ i, weight i • basis i) = u • basis z + v • basis w := by
    rw [← sum_subset (show ({z, w} : Finset I) ⊆ univ from subset_univ _)]
    · rw [sum_pair hzw]
      simp [weight, hzw.symm]
    · intro i _ hi
      rw [hweight i hi, zero_nsmul]
  let e := ofFinEmbEquiv.symm J
  have hJ := congrArg Subtype.val (ofFinEmbEquiv.apply_symm_apply J)
  rw [← hvec, curryLeft_weighted_basis basis f weight e, hJ]
  have hsum : (∑ i ∈ univ \ J.val,
      insertionSign J.val i • (weight i • formCoordinates basis f (insert i J.val))) =
      ∑ i ∈ ({z, w} : Finset I),
        if i ∈ J.val then 0 else
          insertionSign J.val i • (weight i • formCoordinates basis f (insert i J.val)) := by
    rw [show (∑ i ∈ ({z, w} : Finset I),
      if i ∈ J.val then 0 else
        insertionSign J.val i • (weight i • formCoordinates basis f (insert i J.val))) =
        ∑ i ∈ ({z, w} : Finset I) \ J.val,
          insertionSign J.val i • (weight i • formCoordinates basis f (insert i J.val)) by
      rw [Finset.sdiff_eq_filter, sum_filter]
      apply sum_congr rfl
      intro i _
      by_cases h : i ∈ J.val <;> simp [h]]
    rw [← sum_subset (show (({z, w} : Finset I) \ J.val) ⊆ univ \ J.val from
      fun i hi => mem_sdiff.mpr ⟨mem_univ _, (mem_sdiff.mp hi).2⟩)]
    intro i hi hNot
    have hi' : i ∉ J.val := (mem_sdiff.mp hi).2
    have hout : i ∉ ({z, w} : Finset I) := fun h => hNot (mem_sdiff.mpr ⟨h, hi'⟩)
    rw [hweight i hout, zero_nsmul, smul_zero]
  rw [hsum, sum_pair hzw]
  simp [weight, hzw.symm]

open OrderedCycleFactorization (sign_sq)

omit [Finite I] in
private lemma insertion_smul_eq_zero_iff (J : Finset I) (i : I) (v : N) :
    insertionSign J i • v = 0 ↔ v = 0 := by
  constructor
  · intro h
    have hc := congrArg (insertionSign J i • ·) h
    simpa only [smul_smul, insertionSign, sign_sq, one_smul, smul_zero] using hc
  · rintro rfl
    exact smul_zero _

/-- The two-weight insertion equations separate into two torsion constraints
on each coefficient using both indices and one relation for each pair using
exactly one of them. -/
theorem weighted_pair_rows_iff (basis : Module.Basis I ℤ M)
    (f : M [⋀^Fin (d + 1)]→ₗ[ℤ] N) {x z w : I} (hxz : x ≠ z)
    (hxw : x ≠ w) (hzw : z ≠ w) (u v : ℕ)
    (hp : ∀ F : Set.powersetCard I (d + 1), x ∈ F.val → formCoordinates basis f F.val = 0) :
    f.curryLeft (u • basis z + v • basis w) = 0 ↔
      (∀ F : Set.powersetCard I (d + 1), x ∉ F.val → z ∈ F.val → w ∈ F.val →
        u • formCoordinates basis f F.val = 0 ∧ v • formCoordinates basis f F.val = 0) ∧
      (∀ J : Set.powersetCard I d, x ∉ J.val → z ∉ J.val → w ∉ J.val →
        u • (insertionSign J.val z • formCoordinates basis f (insert z J.val)) +
        v • (insertionSign J.val w • formCoordinates basis f (insert w J.val)) = 0) := by
  have hread (J : Set.powersetCard I d) :=
    curry_weighted_pair_apply basis f u v hzw J
  constructor
  · intro h
    have row (J : Set.powersetCard I d) :
        (if z ∈ J.val then 0 else
          insertionSign J.val z • (u • formCoordinates basis f (insert z J.val))) +
        (if w ∈ J.val then 0 else
          insertionSign J.val w • (v • formCoordinates basis f (insert w J.val))) = 0 := by
      rw [← hread, h]
      rfl
    refine ⟨fun F _ hz hw => ?_, fun J _ hz hw => ?_⟩
    · let Jz : Set.powersetCard I d := ⟨F.val.erase z, by
        change (F.val.erase z).card = d
        rw [card_erase_of_mem hz, F.prop, Nat.add_sub_cancel]⟩
      let Jw : Set.powersetCard I d := ⟨F.val.erase w, by
        change (F.val.erase w).card = d
        rw [card_erase_of_mem hw, F.prop, Nat.add_sub_cancel]⟩
      have hJz : w ∈ Jz.val := mem_erase.mpr ⟨hzw.symm, hw⟩
      have hJw : z ∈ Jw.val := mem_erase.mpr ⟨hzw, hz⟩
      have hz' : z ∉ Jz.val := notMem_erase _ _
      have hw' : w ∉ Jw.val := notMem_erase _ _
      have hinz : insert z Jz.val = F.val := insert_erase hz
      have hinw : insert w Jw.val = F.val := insert_erase hw
      exact ⟨(insertion_smul_eq_zero_iff _ _ _).mp (by
        simpa only [ite_eq_right hz', ite_eq_left hJz, hinz, add_zero] using row Jz),
        (insertion_smul_eq_zero_iff _ _ _).mp (by
          simpa only [ite_eq_right hw', ite_eq_left hJw, hinw, zero_add] using row Jw)⟩
    · rw [smul_comm u, smul_comm v]
      simpa only [ite_eq_right hz, ite_eq_right hw] using row J
  · rintro ⟨hboth, hpairs⟩
    apply (basisFormEquiv basis).symm.injective
    rw [map_zero]
    funext J
    rw [basisFormEquiv_symm_apply, Pi.zero_apply, hread]
    have mkF (i : I) (hi : i ∉ J.val) :
        (insert i J.val).card = d + 1 := (card_insert_of_notMem hi).trans
          (congrArg (· + 1) J.prop)
    by_cases hx : x ∈ J.val
    · have hv (i : I) (hi : i ∉ J.val) :
          formCoordinates basis f (insert i J.val) = 0 :=
        hp ⟨insert i J.val, mkF i hi⟩ (mem_insert_of_mem hx)
      by_cases hz : z ∈ J.val <;> by_cases hw : w ∈ J.val <;> simp [hz, hw, hv]
    · by_cases hz : z ∈ J.val
      · by_cases hw : w ∈ J.val
        · simp [hz, hw]
        · have hFx : x ∉ insert w J.val := by simp [hxw, hx]
          have hFz : z ∈ insert w J.val := mem_insert_of_mem hz
          have hv := (hboth ⟨insert w J.val, mkF w hw⟩ hFx hFz (mem_insert_self _ _)).2
          simp [hz, hw, hv]
      · by_cases hw : w ∈ J.val
        · have hFx : x ∉ insert z J.val := by simp [hxz, hx]
          have hFw : w ∈ insert z J.val := mem_insert_of_mem hw
          have hu := (hboth ⟨insert z J.val, mkF z hz⟩ hFx (mem_insert_self _ _) hFw).1
          simp [hz, hw, hu]
        · rw [ite_eq_right hz, ite_eq_right hw, smul_comm _ u, smul_comm _ v]
          exact hpairs J hx hz hw

end D5.S3.Combinatorics.Matroids.PuncturedCircuitResiduePairs
