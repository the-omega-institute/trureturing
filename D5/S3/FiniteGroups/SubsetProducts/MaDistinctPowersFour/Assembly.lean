/- GID: D5/S3/FiniteGroups/SubsetProducts/MaDistinctPowersFour/Assembly
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/SubsetProducts/MaDistinctPowersFour/Assembly
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Assemble subgroup-local permutations into one distinct-power enumeration. -/

/- Escape audit unfinished for 1 supporting theorem. See https://github.com/the-omega-institute/trureturing/issues/32494. -/

import D5.S3.FiniteGroups.SubsetProducts.MaDistinctPowersFour.LocalPowers
import D5.S3.FiniteGroups.SubsetProducts.MaDistinctPowersFour.Allocation

namespace D5.S3.FiniteGroups.SubsetProducts.MaDistinctPowersFour

private theorem arrange_class {G : Type} [Group G] [Finite G] (classify : OrderFourObstruction)
    {n : ℕ} (h : noSmallOrders n G) {count : Fin 4 → ℕ}
    (hn : n = 2 * count 1 + 3 * count 2 + 4 * count 3 + count 0)
    (k : Fin 4) (i : Fin (count k)) (x : Fin (k.val + 1) → G) (hx : Function.Injective x)
    (hz : ∀ j j', Subgroup.zpowers (x j) = Subgroup.zpowers (x j')) :
    ∃ π : Equiv.Perm (Fin (k.val + 1)), Function.Injective
      (fun j : Fin (k.val + 1) => x (π j) ^ (slot n count k i j + 1)) := by
  fin_cases k
  · refine ⟨Equiv.refl _, fun j j' _ => Fin.ext ?_⟩
    have hj := j.isLt
    have hj' := j'.isLt
    simp only [Fin.val_mk] at hj hj'
    omega
  · obtain ⟨h₀, h₁, hlt, hsum⟩ := pair_slots hn i
    exact arrange_pair h (Nat.succ_pos _) hlt hsum _ h₀ h₁ x hx hz
  · have hbound : (count 1 + 3 * i.val + 1) + 2 ≤ n := by
      have hh := slot_lt hn 2 i (2 : Fin 3)
      have he := triple_slots n count i (2 : Fin 3)
      change slot n count 2 i 2 + 1 = (count 1 + 3 * i.val + 1) + 2 at he
      omega
    obtain ⟨π, hπ⟩ := arrange_triple h (Nat.succ_pos _) hbound x hx hz
    refine ⟨π, fun j j' he => hπ ?_⟩
    change x (π j) ^ (slot n count 2 i j + 1) = x (π j') ^ (slot n count 2 i j' + 1) at he
    rwa [triple_slots, triple_slots] at he
  · have hbound : (count 1 + 3 * count 2 + 4 * i.val + 1) + 3 ≤ n := by
      have hh := slot_lt hn 3 i (3 : Fin 4)
      have he := four_slots n count i (3 : Fin 4)
      change slot n count 3 i 3 + 1 = (count 1 + 3 * count 2 + 4 * i.val + 1) + 3 at he
      omega
    obtain ⟨π, hπ⟩ := arrange_four classify h (Nat.succ_pos _) hbound x hx hz
    refine ⟨π, fun j j' he => hπ ?_⟩
    change x (π j) ^ (slot n count 3 i j + 1) = x (π j') ^ (slot n count 3 i j' + 1) at he
    rwa [four_slots, four_slots] at he

/-- Ma's registered size-four claim follows from the order-four Latin-array obstruction. -/
theorem claim_of_orderFour (classify : OrderFourObstruction) : claim := by
  classical
  intro n G _ _ A _ hcard horders hclasses
  let generator (a : ↥A) := Subgroup.zpowers (a : G)
  let C := ↥(Set.range generator)
  let key (a : ↥A) : C := ⟨generator a, ⟨a, rfl⟩⟩
  let Fiber (c : C) := {a : ↥A // key a = c}
  let (c : C) : Fintype (Fiber c) := Fintype.ofFinite _
  let : Finite C := Finite.Set.finite_range generator
  have hfiber (c : C) : 0 < Fintype.card (Fiber c) ∧ Fintype.card (Fiber c) ≤ 4 := by
    obtain ⟨a, ha⟩ := c.property
    have hk : key a = c := Subtype.ext ha
    let e : Fiber c ≃ generatorClass A (a : G) :=
      { toFun := fun b => ⟨b.val.val, b.val.property, by
          exact (congrArg Subtype.val b.property).trans ha.symm⟩
        invFun := fun b => ⟨⟨b.val, b.property.1⟩, Subtype.ext (b.property.2.trans ha)⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    have hupper := hclasses (a : G) a.property
    rw [← Nat.card_congr e, Nat.card_eq_fintype_card] at hupper
    exact ⟨Fintype.card_pos_iff.mpr ⟨⟨a, hk⟩⟩, hupper⟩
  let sizeIndex (c : C) : Fin 4 :=
    ⟨Fintype.card (Fiber c) - 1, by have := (hfiber c).2; omega⟩
  let Bucket (k : Fin 4) := {c : C // sizeIndex c = k}
  let (k : Fin 4) : Fintype (Bucket k) := Fintype.ofFinite _
  let count (k : Fin 4) := Fintype.card (Bucket k)
  let bucket (k : Fin 4) : Fin (count k) ≃ Bucket k := (Fintype.equivFin _).symm
  let cls (k : Fin 4) (i : Fin (count k)) : C := (bucket k i).val
  let elems (k : Fin 4) (i : Fin (count k)) : Fin (k.val + 1) ≃ Fiber (cls k i) :=
    (Fintype.equivFinOfCardEq (by
      have hk := congrArg Fin.val (bucket k i).property
      change Fintype.card (Fiber (cls k i)) - 1 = k.val at hk
      have := (hfiber (cls k i)).1
      omega)).symm
  let x (k : Fin 4) (i : Fin (count k)) (j : Fin (k.val + 1)) : G := (elems k i j).val.val
  have hx (k : Fin 4) (i : Fin (count k)) : Function.Injective (x k i) :=
    Subtype.val_injective.comp (Subtype.val_injective.comp (elems k i).injective)
  have hxkey (k : Fin 4) (i : Fin (count k)) (j : Fin (k.val + 1)) :
      Subgroup.zpowers (x k i j) = (cls k i : Subgroup G) :=
    congrArg Subtype.val (elems k i j).property
  -- First enumerate all positions by size, then identify them with the subgroup fibers.
  let grouped : ClassPositions count ≃ (Σ k : Fin 4, Σ b : Bucket k, Fiber b.val) :=
    Equiv.sigmaCongrRight fun k =>
      (Equiv.sigmaEquivProd _ _).symm.trans (Equiv.sigmaCongr (bucket k) (elems k))
  let ungrouped : (Σ k : Fin 4, Σ b : Bucket k, Fiber b.val) ≃ (Σ c : C, Fiber c) :=
    (Equiv.sigmaAssoc (fun _ (b : Bucket _) => Fiber b.val)).symm.trans
      (Equiv.sigmaCongr (Equiv.sigmaFiberEquiv sizeIndex) (fun _ => Equiv.refl _))
  let eA : ClassPositions count ≃ ↥A :=
    grouped.trans (ungrouped.trans (Equiv.sigmaFiberEquiv key))
  have htotal : n = 2 * count 1 + 3 * count 2 + 4 * count 3 + count 0 :=
    hcard.symm.trans ((Fintype.card_coe A).symm.trans
      ((Fintype.card_congr eA).symm.trans (card_classPositions count)))
  have harrange (k : Fin 4) (i : Fin (count k)) :
      ∃ π : Equiv.Perm (Fin (k.val + 1)), Function.Injective
        (fun j : Fin (k.val + 1) => x k i (π j) ^ (slot n count k i j + 1)) :=
    arrange_class classify horders htotal k i (x k i) (hx k i)
      (fun j j' => (hxkey k i j).trans (hxkey k i j').symm)
  choose perm hperm using harrange
  let place (p : ClassPositions count) : Fin n :=
    ⟨slot n count p.1 p.2.1 p.2.2, slot_lt htotal p.1 p.2.1 p.2.2⟩
  let ePlace := Equiv.ofBijective place ((Fintype.bijective_iff_injective_and_card place).mpr
    ⟨fun _ _ he => slot_injective htotal (congrArg Fin.val he),
      (card_classPositions count).trans (htotal.symm.trans (Fintype.card_fin n).symm)⟩)
  let ePerm : Equiv.Perm (ClassPositions count) :=
    Equiv.sigmaCongrRight fun k =>
      { toFun := fun p => (p.1, perm k p.1 p.2)
        invFun := fun p => (p.1, (perm k p.1).symm p.2)
        left_inv := fun p => Prod.ext rfl ((perm k p.1).symm_apply_apply p.2)
        right_inv := fun p => Prod.ext rfl ((perm k p.1).apply_symm_apply p.2) }
  let a := ePlace.symm.trans (ePerm.trans eA)
  have ha (p : ClassPositions count) :
      (a (ePlace p) : G) = x p.1 p.2.1 (perm p.1 p.2.1 p.2.2) := by
    simp only [a, Equiv.trans_apply, Equiv.symm_apply_apply]
    rfl
  have hpower : Function.Injective
      (fun p : ClassPositions count => (a (ePlace p) : G) ^ ((ePlace p).val + 1)) := by
    rintro ⟨k, i, j⟩ ⟨k', i', j'⟩ hp
    dsimp only at hp
    rw [ha, ha] at hp
    change x k i (perm k i j) ^ (slot n count k i j + 1) =
      x k' i' (perm k' i' j') ^ (slot n count k' i' j' + 1) at hp
    have h₀ := zpowers_pow_of_bound horders (x k i (perm k i j)) (Nat.succ_pos _)
      (slot_lt htotal k i j)
    have h₁ := zpowers_pow_of_bound horders (x k' i' (perm k' i' j')) (Nat.succ_pos _)
      (slot_lt htotal k' i' j')
    have hz := h₀.symm.trans ((congrArg Subgroup.zpowers hp).trans h₁)
    rw [hxkey, hxkey] at hz
    have hc : cls k i = cls k' i' := Subtype.ext hz
    have hk : k = k' :=
      (bucket k i).property.symm.trans ((congrArg sizeIndex hc).trans (bucket k' i').property)
    subst k'
    have hi : i = i' := (bucket k).injective (Subtype.ext hc)
    subst i'
    exact congrArg (fun t => (⟨k, (i, t)⟩ : ClassPositions count)) (hperm k i hp)
  refine ⟨a, ?_⟩
  intro i j h
  apply ePlace.symm.injective
  apply hpower
  simpa only [Equiv.apply_symm_apply] using h

end D5.S3.FiniteGroups.SubsetProducts.MaDistinctPowersFour
