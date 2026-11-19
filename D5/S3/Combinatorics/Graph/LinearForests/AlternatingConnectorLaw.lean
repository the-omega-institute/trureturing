/- GID: D5/S3/Combinatorics/Graph/LinearForests/AlternatingConnectorLaw
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/LinearForests/AlternatingConnectorLaw
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.GroupTheory.Perm.Option]
   utility: none
   digest: Exact prescribed-successor mass by contracting one labelled connector. -/

import D5.S3.Combinatorics.Graph.LinearForests.CompatibleCycleInventory

/-! A prescribed successor removes one label from the cycle and transfers the
removed label's source color to that successor. The reduced carrier counts all
compatible cycles with the prescribed connection. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Combinatorics.Graph.LinearForests.AlternatingConnectorLaw

open Equiv CompatibleCycleInventory
open D5.S0.Diagonal.Probability.EquivariantEscape (uniformPmf uniformPmf_toOuterMeasure_apply)
open scoped ENNReal

variable {A C : Type*}

section Insertion
variable [DecidableEq A]

private theorem insert_compatibility (s d : A → Bool) (a b : Bool) (ρ : Perm A) (y : A) :
    (∀ x, Option.elim' b d x = Option.elim' a s
      (insertLabel ρ y x)) ↔
      s y = b ∧ ∀ x, d x = Function.update s y a (ρ x) := by
  constructor
  · intro h
    have hy : s y = b := by
      simpa only [insert_none,
        Option.elim'_none, Option.elim'_some] using (h none).symm
    refine ⟨hy, fun x => ?_⟩
    by_cases he : ρ x = y
    · simpa [insert_some, he] using h (some x)
    · simpa [insert_some, he] using h (some x)
  · rintro ⟨hy, h⟩ (_ | x)
    · simpa [insert_none]
        using hy.symm
    · by_cases he : ρ x = y
      · simpa [insert_some, he]
          using h x
      · simpa [insert_some, he]
          using h x


/-- Contract an inserted predecessor into its prescribed successor. -/
private noncomputable def connectorContraction [Finite A]
    (s d : A → Bool) (a b : Bool) (y : A) (hy : s y = b) :
    Compatible (Function.update s y a) d ≃
      {σ : Compatible (Option.elim' a s) (Option.elim' b d) // σ.1 none = some y} := by
  let : Nonempty A := ⟨y⟩
  let ins : Perm A → A → Perm (Option A) :=
    insertLabel
  have hslot (ρ : Perm A) : ins ρ y none = some y :=
    insert_none ρ y
  have hcycle (ρ : Perm A) :
      (ins ρ y).IsCycleOn Set.univ ↔ ρ.IsCycleOn Set.univ :=
    insert_cycle_iff ρ y
  let f (ρ : Compatible (Function.update s y a) d) :
      {σ : Compatible (Option.elim' a s) (Option.elim' b d) // σ.1 none = some y} :=
    ⟨⟨ins ρ.1 y, inferInstance, (hcycle ρ.1).mpr ρ.2.2.1,
      (insert_compatibility s d a b ρ.1 y).mpr ⟨hy, ρ.2.2.2⟩⟩, hslot ρ.1⟩
  apply Equiv.ofBijective f
  constructor
  · intro p q h
    have hperm := congrArg (fun σ => Equiv.removeNone σ.1.1) h
    have he (ρ : Perm A) : Equiv.removeNone (ins ρ y) = ρ := by
      have hdec := Perm.decomposeOption.apply_symm_apply (some y, ρ)
      simpa [Perm.decomposeOption, Equiv.symm, ins,
        insertLabel]
        using congrArg Prod.snd hdec
    change Equiv.removeNone (ins p.1 y) = Equiv.removeNone (ins q.1 y) at hperm
    exact Subtype.ext (by simpa only [he] using hperm)
  · intro σ
    let ρ : Perm A := Equiv.removeNone σ.1.1
    have hperm : ins ρ y = σ.1.1 := by
      simp [Perm.decomposeOption, Equiv.symm, ρ, ins, σ.2, insertLabel]
    have hC : ρ.IsCycleOn Set.univ := (hcycle ρ).mp (hperm ▸ σ.1.2.2.1)
    have hcompat (x : Option A) :
        Option.elim' b d x = Option.elim' a s (ins ρ y x) := by
      rw [hperm]
      exact σ.1.2.2.2 x
    have hD := (insert_compatibility s d a b ρ y).mp hcompat
    exact ⟨⟨ρ, inferInstance, hC, hD.2⟩, Subtype.ext (Subtype.ext hperm)⟩

end Insertion

attribute [local instance] Classical.propDecidable

private theorem inventory_update [Finite A] [DecidableEq A] (s d : A → Bool) (a : Bool) (y : A) (i j : Bool) :
    inventory (Function.update s y a) d i j +
      (if s y = i ∧ d y = j then 1 else 0) =
    inventory s d i j + (if a = i ∧ d y = j then 1 else 0) := by
  classical
  let := Fintype.ofFinite A
  have decompose (p : A → Prop) [DecidablePred p] :
      Nat.card {x // p x} =
        ((Finset.univ.erase y).filter p).card + (if p y then 1 else 0) := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    conv_lhs => rw [← Finset.insert_erase (Finset.mem_univ y), Finset.filter_insert]
    by_cases h : p y
    · rw [ite_eq_left h, ite_eq_left h, Finset.card_insert_of_notMem]
      intro hy
      have hm : y ∈ (Finset.univ : Finset A).erase y := (Finset.mem_filter.mp hy).1
      exact (Finset.mem_erase.mp hm).1 rfl
    · simp [h]
  have hfilter :
      (Finset.univ.erase y).filter (fun x => Function.update s y a x = i ∧ d x = j) =
        (Finset.univ.erase y).filter (fun x => s x = i ∧ d x = j) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true]
    by_cases h : x = y
    · simp [h]
    · simp [h]
  unfold inventory
  rw [decompose (fun x => Function.update s y a x = i ∧ d x = j),
    decompose (fun x => s x = i ∧ d x = j), hfilter, Function.update_self]
  ac_rfl


private theorem option_inventory_colors [Finite A] (s d : A → Bool) (a b i j : Bool) :
    inventory (Option.elim' a s) (Option.elim' b d) i j =
      inventory s d i j + if a = i ∧ b = j then 1 else 0 := by
  let := Fintype.ofFinite A
  classical
  simp only [inventory, Nat.card_eq_fintype_card, Fintype.card_subtype,
    Finset.card_filter, Fintype.sum_option, Option.elim'_none, Option.elim'_some]
  ac_rfl

private theorem balance_of_compatible [Finite A] (s d : A → Bool)
    (ρ : Compatible s d) : inventory s d false true = inventory s d true false := by
  apply inventory_balanced
  exact (Nat.card_congr (Equiv.subtypeEquiv ρ.1 (fun x => by rw [ρ.2.2.2 x]) :
    Side d true ≃ Side s true)).symm

private theorem contracted_balance [Finite A] [DecidableEq A] (s d : A → Bool) (a b : Bool) (y : A)
    (hy : s y = b) (ρ : Compatible (Option.elim' a s) (Option.elim' b d)) :
    inventory (Function.update s y a) d false true =
      inventory (Function.update s y a) d true false := by
  have hb := balance_of_compatible _ _ ρ
  rw [option_inventory_colors, option_inventory_colors] at hb
  have hl := inventory_update s d a y false true
  have hr := inventory_update s d a y true false
  rw [hy] at hl hr
  cases a <;> cases b <;> cases hd : d y <;> simp [hd] at hb hl hr <;> omega

/-- Delete x and change the source color at its prescribed successor y. -/
def contractedSource (s : C → Bool) (x y : C) : {z : C // z ≠ x} → Bool :=
  fun z => if z.1 = y then s x else s z

private theorem contractedSource_eq_update (s : C → Bool) (x y : C) (hxy : y ≠ x) :
    contractedSource s x y = Function.update (fun z => s z.1) ⟨y, hxy⟩ (s x) := by
  classical
  funext z
  by_cases hz : z = ⟨y, hxy⟩
  · subst z
    simp [contractedSource]
  · have he : z.1 ≠ y := fun h => hz (Subtype.ext h)
    simp [contractedSource, Function.update_of_ne hz, he]

/-- Name the removed label as none and keep all other labels as themselves. -/
private def pointedCompatibility (s d : C → Bool) (x : C) [DecidableEq C] :
    Compatible (Option.elim' (s x) (fun z : {z : C // z ≠ x} => s z.1))
      (Option.elim' (d x) (fun z : {z : C // z ≠ x} => d z.1)) ≃ Compatible s d := by
  let B := {z : C // z ≠ x}
  let e : Option B ≃ C := Equiv.optionSubtypeNe x
  let ss : B → Bool := fun z => s z.1
  let dd : B → Bool := fun z => d z.1
  have hs : Option.elim' (s x) ss = s ∘ e := by
    funext z
    cases z <;> rfl
  have hd : Option.elim' (d x) dd = d ∘ e := by
    funext z
    cases z <;> rfl
  let transport : Compatible (Option.elim' (s x) ss) (Option.elim' (d x) dd) ≃
      Compatible (s ∘ e) (d ∘ e) :=
    Equiv.subtypeEquiv (Equiv.refl _) (fun _ => by simp only [Equiv.refl_apply, hs, hd])
  exact transport.trans (compatibleTransport e.symm s d).symm

private def contractAt [Finite C] (s d : C → Bool) (x y : C)
    (hxy : y ≠ x) (hy : s y = d x) :
    Compatible (contractedSource s x y) (fun z => d z.1) ≃
      {ρ : Compatible s d // ρ.1 x = y} := by
  classical
  let B := {z : C // z ≠ x}
  let e : Option B ≃ C := Equiv.optionSubtypeNe x
  let f := pointedCompatibility s d x
  rw [contractedSource_eq_update s x y hxy]
  refine (connectorContraction (fun z : B => s z.1) (fun z : B => d z.1)
    (s x) (d x) ⟨y, hxy⟩ hy).trans (Equiv.subtypeEquiv f ?_)
  intro ρ
  have he : (f ρ).1 x = e (ρ.1 none) := by
    change (e.symm.permCongr.symm ρ.1) x = _
    rw [Equiv.permCongr_symm, Equiv.permCongr_apply]
    have hx : e.symm x = none := e.symm_apply_apply none
    simp only [Equiv.symm_symm, hx]
  rw [he]
  exact e.apply_eq_iff_eq.symm

private theorem contracted_balance_at [Finite C] (s d : C → Bool) (x y : C)
    (hxy : y ≠ x) (hy : s y = d x) (ρ : Compatible s d) :
    inventory (contractedSource s x y) (fun z => d z.1) false true =
      inventory (contractedSource s x y) (fun z => d z.1) true false := by
  classical
  rw [contractedSource_eq_update s x y hxy]
  exact contracted_balance (fun z : {z : C // z ≠ x} => s z.1) (fun z => d z.1)
    (s x) (d x) ⟨y, hxy⟩ hy ((pointedCompatibility s d x).symm ρ)

/-- The inventory count on the nonempty carrier remaining after contraction. -/
def contractedInventoryCount (u v : A → Bool) : ℕ :=
  if 0 < inventory u v false true then
    inventory u v false true * (Nat.card (Side u false) - 1).factorial *
      (Nat.card (Side u true) - 1).factorial
  else if inventory u v false false = 0 ∨ inventory u v true true = 0 then
    (Nat.card A - 1).factorial else 0

/-- Uniform mass of one prescribed successor between distinct labels. -/
theorem connector_mass [Finite C] (s d : C → Bool) (x y : C) (hxy : y ≠ x)
    (μ : PMF (Compatible s d))
    (hμ : ∀ σ, μ σ = (Nat.card (Compatible s d) : ℝ≥0∞)⁻¹) :
    let R := {z : C // z ≠ x}
    let u := contractedSource s x y
    let v : R → Bool := fun z => d z.1
    let M := contractedInventoryCount u v
    μ.toOuterMeasure {σ | σ.1 x = y} =
      if s y = d x then (M : ℝ≥0∞) / Nat.card (Compatible s d) else 0 := by
  classical
  dsimp only [contractedInventoryCount]
  obtain ⟨σ₀, _⟩ := μ.support_nonempty
  let K := Compatible s d
  let S : Set K := {σ | σ.1 x = y}
  let : Fintype K := Fintype.ofFinite K
  let : Nonempty K := ⟨σ₀⟩
  let : Fintype S := Fintype.ofFinite S
  have heq : μ = uniformPmf K := by
    apply PMF.ext
    intro σ
    rw [hμ]
    change (Nat.card K : ℝ≥0∞)⁻¹ = (Fintype.card K : ℝ≥0∞)⁻¹
    rw [Nat.card_eq_fintype_card]
  rw [heq, uniformPmf_toOuterMeasure_apply]
  by_cases hy : s y = d x
  · have hcount := Nat.card_congr (contractAt s d x y hxy hy).symm
    have hR : Nat.card {z : C // z ≠ x} ≠ 0 :=
      Nat.ne_of_gt (Finite.card_pos_iff.mpr ⟨⟨y, hxy⟩⟩)
    have hb := contracted_balance_at s d x y hxy hy σ₀
    rw [compatible_cycle_card _ _ hb, ite_eq_right hR] at hcount
    change Nat.card S = _ at hcount
    change (Fintype.card S : ℝ≥0∞) / Fintype.card K = _
    rw [ite_eq_left hy, ← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hcount]
  · have hS : IsEmpty S := ⟨fun σ => by
      have hc := σ.1.2.2.2 x
      have hs : σ.1.1 x = y := σ.2
      rw [hs] at hc
      exact hy hc.symm⟩
    let : IsEmpty S := hS
    change (Fintype.card S : ℝ≥0∞) / Fintype.card K = _
    simp [hy]

end D5.S3.Combinatorics.Graph.LinearForests.AlternatingConnectorLaw
