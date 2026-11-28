/- GID: D5/S3/Algebra/Refinement/RegularMayerVietoris
   generality: G
   mirror-B: none(waiver:covered-by-regular-mayer-vietoris-blueprint)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Both directions of Goodearl--Pardo--Wehrung, Theorem 3.2. -/

module

public import D5.S3.Algebra.Refinement.RegularComponents
public import D5.S3.Algebra.Refinement.FiniteTransport

/-! Omega original.
Both directions of Goodearl--Pardo--Wehrung, Theorem 3.2.
Refinement entries, component inverses, and all sums remain in the original monoid.
-/

@[expose] public section

namespace Omega.Refinement.Regular

universe u
variable {K : Type u} [AddCommMonoid K]

/-- Riesz refinement of the idempotent semilattice, with no meet operation. -/
def IdempotentRefinement (K : Type u) [AddCommMonoid K] : Prop :=
  ∀ e₀ e₁ f₀ f₁ : K, Idempotent e₀ → Idempotent e₁ → Idempotent f₀ →
    Idempotent f₁ → e₀ + e₁ = f₀ + f₁ →
    ∃ g₀₀ g₀₁ g₁₀ g₁₁ : K,
      Idempotent g₀₀ ∧ Idempotent g₀₁ ∧ Idempotent g₁₀ ∧ Idempotent g₁₁ ∧
      g₀₀ + g₀₁ = e₀ ∧ g₁₀ + g₁₁ = e₁ ∧
      g₀₀ + g₁₀ = f₀ ∧ g₀₁ + g₁₁ = f₁

/-- The first Mayer--Vietoris property: addition is surjective on components. -/
def ComponentSum (K : Type u) [AddCommMonoid K] : Prop :=
  ∀ e f : K, Idempotent e → Idempotent f → ∀ x : K,
    InComponent (e + f) x ↔
      ∃ a b : K, InComponent e a ∧ InComponent f b ∧ a + b = x

/-- The second Mayer--Vietoris property: compatible elements have a common lift. -/
def CommonLift (K : Type u) [AddCommMonoid K] : Prop :=
  ∀ e f a b : K, Idempotent e → Idempotent f →
    InComponent e a → InComponent f b → a + f = b + e →
    ∃ w : K, w + e = a ∧ w + f = b

/-- Applying the component identity to the four entries gives an idempotent
refinement. This is the first step of the source's forward construction. -/
theorem idempotent_refinement_of_refinement (hreg : AddRegular K)
    (hr : BinaryRefinement K) : IdempotentRefinement K := by
  intro e₀ e₁ f₀ f₁ he₀ he₁ hf₀ hf₁ h
  obtain ⟨a, b, c, d, hab, hcd, hac, hbd⟩ := hr _ _ _ _ h
  obtain ⟨ga, hga, ha⟩ := regular_component_idempotent hreg a
  obtain ⟨gb, hgb, hb⟩ := regular_component_idempotent hreg b
  obtain ⟨gc, hgc, hc⟩ := regular_component_idempotent hreg c
  obtain ⟨gd, hgd, hd⟩ := regular_component_idempotent hreg d
  have ident {e g x : K} (he : Idempotent e) (hg : Idempotent g)
      (hx : InComponent g x) (hxe : x = e) : g = e := by
    subst x
    exact component_idempotent_unique hg he hx
      ⟨⟨0, by simp⟩, ⟨0, by simp⟩⟩
  exact ⟨ga, gb, gc, gd, hga, hgb, hgc, hgd,
    ident he₀ (component_add hga hgb ha hb).1 (component_add hga hgb ha hb).2 hab,
    ident he₁ (component_add hgc hgd hc hd).1 (component_add hgc hgd hc hd).2 hcd,
    ident hf₀ (component_add hga hgc ha hc).1 (component_add hga hgc ha hc).2 hac,
    ident hf₁ (component_add hgb hgd hb hd).1 (component_add hgb hgd hb hd).2 hbd⟩

/-- The offsets of a refinement of `x + inverse(x) = e + f` supply the
component decomposition without cancellation. -/
theorem component_sum_of_refinement (hr : BinaryRefinement K) : ComponentSum K := by
  intro e f he hf x
  constructor
  · intro hx
    have hef : Idempotent (e + f) := IsIdempotentElem.mul
      (S := Multiplicative K) (a := Multiplicative.ofAdd e)
      (b := Multiplicative.ofAdd f) he hf
    obtain ⟨xi, _, hxi⟩ := component_inverse hef hx
    obtain ⟨a, b, c, d, hab, _, hac, hbd⟩ := hr x xi e f hxi
    refine ⟨a + e, b + f, component_offset he ⟨c, hac⟩,
      component_offset hf ⟨d, hbd⟩, ?_⟩
    calc
      (a + e) + (b + f) = (a + b) + (e + f) := by ac_rfl
      _ = x + (e + f) := by rw [hab]
      _ = x := by simpa [add_comm] using component_identity hef hx
  · rintro ⟨a, b, ha, hb, rfl⟩
    exact (component_add he hf ha hb).2

/-- The upper-left refinement entry plus the inverse of the lower-right entry
is the common lift. -/
theorem common_lift_of_refinement (hreg : AddRegular K)
    (hr : BinaryRefinement K) : CommonLift K := by
  intro e f u v he hf hu hv huv
  obtain ⟨a, b, c, d, hab, hcd, hac, hbd⟩ := hr u f v e huv
  obtain ⟨gd, hgd, hd⟩ := regular_component_idempotent hreg d
  obtain ⟨di, _, hdi⟩ := component_inverse hgd hd
  have gde : AlgebraicLE gd e :=
    algebraicLE_trans hd.1 ⟨b, by simpa [add_comm] using hbd⟩
  have gdf : AlgebraicLE gd f :=
    algebraicLE_trans hd.1 ⟨c, by simpa [add_comm] using hcd⟩
  have hdu : u + gd = u := idempotent_absorb hgd (algebraicLE_trans gde hu.1)
  have hdv : v + gd = v := idempotent_absorb hgd (algebraicLE_trans gdf hv.1)
  refine ⟨a + di, ?_, ?_⟩
  · calc
      (a + di) + e = (a + di) + (b + d) := by rw [hbd]
      _ = (a + b) + (d + di) := by ac_rfl
      _ = u + gd := by rw [hab, hdi]
      _ = u := hdu
  · calc
      (a + di) + f = (a + di) + (c + d) := by rw [hcd]
      _ = (a + c) + (d + di) := by ac_rfl
      _ = v + gd := by rw [hac, hdi]
      _ = v := hdv

/-- The four-entry correction construction of the reverse implication in
Theorem 3.2. Component inverses are internal to their idempotent identities. -/
theorem refinement_of_mayer_vietoris (hreg : AddRegular K)
    (hir : IdempotentRefinement K) (hs : ComponentSum K) (hl : CommonLift K) :
    BinaryRefinement K := by
  intro a₀ a₁ b₀ b₁ hab
  obtain ⟨e₀, ⟨he₀, ha₀⟩, _⟩ := exists_unique_component_idempotent hreg a₀
  obtain ⟨e₁, he₁, ha₁⟩ := regular_component_idempotent hreg a₁
  obtain ⟨f₀, hf₀, hb₀⟩ := regular_component_idempotent hreg b₀
  obtain ⟨f₁, hf₁, hb₁⟩ := regular_component_idempotent hreg b₁
  have totals := component_add he₀ he₁ ha₀ ha₁
  have totals' := component_add hf₀ hf₁ hb₀ hb₁
  have hid : e₀ + e₁ = f₀ + f₁ := component_idempotent_unique
    totals.1 totals'.1 totals.2 (by rw [hab]; exact totals'.2)
  obtain ⟨g₀₀, g₀₁, g₁₀, g₁₁, hg₀₀, hg₀₁, hg₁₀, hg₁₁,
    hrow₀, hrow₁, hcol₀, hcol₁⟩ := hir _ _ _ _ he₀ he₁ hf₀ hf₁ hid
  obtain ⟨c₀₀, c₀₁, hc₀₀, hc₀₁, hc₀⟩ :=
    (hs _ _ hg₀₀ hg₀₁ a₀).mp (by rw [hrow₀]; exact ha₀)
  obtain ⟨c₁₀, c₁₁, hc₁₀, hc₁₁, hc₁⟩ :=
    (hs _ _ hg₁₀ hg₁₁ a₁).mp (by rw [hrow₁]; exact ha₁)
  let s₀ := c₀₀ + c₁₀
  let s₁ := c₀₁ + c₁₁
  have hs₀ : InComponent f₀ s₀ := by
    rw [← hcol₀]; exact (component_add hg₀₀ hg₁₀ hc₀₀ hc₁₀).2
  have hs₁ : InComponent f₁ s₁ := by
    rw [← hcol₁]; exact (component_add hg₀₁ hg₁₁ hc₀₁ hc₁₁).2
  have hsum : s₀ + s₁ = b₀ + b₁ := by
    calc
      s₀ + s₁ = (c₀₀ + c₀₁) + (c₁₀ + c₁₁) := by dsimp [s₀, s₁]; ac_rfl
      _ = a₀ + a₁ := by rw [hc₀, hc₁]
      _ = b₀ + b₁ := hab
  obtain ⟨bi, hbi, hbbi⟩ := component_inverse hf₀ hb₀
  obtain ⟨si, hsi, hssi⟩ := component_inverse hf₁ hs₁
  have hu : InComponent f₀ (s₀ + bi) := by
    simpa only [show f₀ + f₀ = f₀ from hf₀] using (component_add hf₀ hf₀ hs₀ hbi).2
  have hv : InComponent f₁ (b₁ + si) := by
    simpa only [show f₁ + f₁ = f₁ from hf₁] using (component_add hf₁ hf₁ hb₁ hsi).2
  have huv : (s₀ + bi) + f₁ = (b₁ + si) + f₀ := by
    calc
      (s₀ + bi) + f₁ = (s₀ + bi) + (s₁ + si) := by rw [hssi]
      _ = (s₀ + s₁) + bi + si := by ac_rfl
      _ = (b₀ + b₁) + bi + si := by rw [hsum]
      _ = (b₁ + si) + (b₀ + bi) := by ac_rfl
      _ = (b₁ + si) + f₀ := by rw [hbbi]
  obtain ⟨w, hw₀, hw₁⟩ := hl _ _ _ _ hf₀ hf₁ hu hv huv
  obtain ⟨h, hh, hw⟩ := regular_component_idempotent hreg w
  have hwf₀ : h + f₀ = f₀ := by
    have hi := component_add hh hf₀ hw
      (show InComponent f₀ f₀ from ⟨⟨0, by simp⟩, ⟨0, by simp⟩⟩)
    exact component_idempotent_unique hi.1 hf₀ hi.2 (by rw [hw₀]; exact hu)
  have hle : AlgebraicLE h (e₀ + e₁) := by
    apply algebraicLE_trans (show AlgebraicLE h f₀ from ⟨f₀, hwf₀⟩)
    exact ⟨f₁, hid.symm⟩
  have hee : Idempotent (e₀ + e₁) := totals.1
  have heq : h + (e₀ + e₁) = e₀ + e₁ := by
    simpa [add_comm] using idempotent_absorb hh hle
  obtain ⟨h₀, h₁, k₀, k₁, hh₀, hh₁, _, _, hhs, _, hke₀, hke₁⟩ :=
    hir h (e₀ + e₁) e₀ e₁ hh hee he₀ he₁ heq
  have h₀e₀ : AlgebraicLE h₀ e₀ := ⟨k₀, hke₀⟩
  have h₁e₁ : AlgebraicLE h₁ e₁ := ⟨k₁, hke₁⟩
  obtain ⟨w₀, w₁, hw₀c, hw₁c, hws⟩ :=
    (hs h₀ h₁ hh₀ hh₁ w).mp (by rw [hhs]; exact hw)
  obtain ⟨wi₀, _, hwi₀⟩ := component_inverse hh₀ hw₀c
  obtain ⟨wi₁, _, hwi₁⟩ := component_inverse hh₁ hw₁c
  have hinv : w + (wi₀ + wi₁) = h := by
    calc
      w + (wi₀ + wi₁) = (w₀ + wi₀) + (w₁ + wi₁) := by rw [← hws]; ac_rfl
      _ = h₀ + h₁ := by rw [hwi₀, hwi₁]
      _ = h := hhs
  have hs₀id : s₀ + f₀ = s₀ := by simpa [add_comm] using component_identity hf₀ hs₀
  have hb₀id : b₀ + f₀ = b₀ := by simpa [add_comm] using component_identity hf₀ hb₀
  have hs₁id : s₁ + f₁ = s₁ := by simpa [add_comm] using component_identity hf₁ hs₁
  have hb₁id : b₁ + f₁ = b₁ := by simpa [add_comm] using component_identity hf₁ hb₁
  have ha₀h : a₀ + h₀ = a₀ :=
    idempotent_absorb hh₀ (algebraicLE_trans h₀e₀ ha₀.1)
  have ha₁h : a₁ + h₁ = a₁ :=
    idempotent_absorb hh₁ (algebraicLE_trans h₁e₁ ha₁.1)
  have hfirst : s₀ + (wi₀ + wi₁) = b₀ := by
    have huadd : (s₀ + bi) + b₀ = s₀ := by
      calc
        (s₀ + bi) + b₀ = s₀ + (b₀ + bi) := by ac_rfl
        _ = s₀ := by rw [hbbi, hs₀id]
    calc
      s₀ + (wi₀ + wi₁) = ((s₀ + bi) + b₀) + (wi₀ + wi₁) := by rw [huadd]
      _ = (w + f₀ + b₀) + (wi₀ + wi₁) := by rw [hw₀]
      _ = b₀ + (h + f₀) := by rw [← hinv]; ac_rfl
      _ = b₀ := by rw [hwf₀, hb₀id]
  have hsecond : s₁ + w = b₁ := by
    calc
      s₁ + w = (s₁ + f₁) + w := by rw [hs₁id]
      _ = s₁ + (w + f₁) := by ac_rfl
      _ = s₁ + (b₁ + si) := by rw [hw₁]
      _ = b₁ + (s₁ + si) := by ac_rfl
      _ = b₁ := by rw [hssi, hb₁id]
  refine ⟨c₀₀ + wi₀, c₀₁ + w₀, c₁₀ + wi₁, c₁₁ + w₁, ?_, ?_, ?_, ?_⟩
  · calc
      (c₀₀ + wi₀) + (c₀₁ + w₀) = (c₀₀ + c₀₁) + (w₀ + wi₀) := by ac_rfl
      _ = a₀ := by rw [hc₀, hwi₀, ha₀h]
  · calc
      (c₁₀ + wi₁) + (c₁₁ + w₁) = (c₁₀ + c₁₁) + (w₁ + wi₁) := by ac_rfl
      _ = a₁ := by rw [hc₁, hwi₁, ha₁h]
  · calc
      (c₀₀ + wi₀) + (c₁₀ + wi₁) = s₀ + (wi₀ + wi₁) := by dsimp [s₀]; ac_rfl
      _ = b₀ := hfirst
  · calc
      (c₀₁ + w₀) + (c₁₁ + w₁) = s₁ + (w₀ + w₁) := by dsimp [s₁]; ac_rfl
      _ = b₁ := by rw [hws]; exact hsecond

/-- Goodearl--Pardo--Wehrung, Theorem 3.2, in original additive coordinates. -/
theorem refinement_iff_mayer_vietoris (hreg : AddRegular K) :
    BinaryRefinement K ↔ IdempotentRefinement K ∧ ComponentSum K ∧ CommonLift K := by
  constructor
  · intro hr
    exact ⟨idempotent_refinement_of_refinement hreg hr,
      component_sum_of_refinement hr, common_lift_of_refinement hreg hr⟩
  · rintro ⟨hir, hs, hl⟩
    exact refinement_of_mayer_vietoris hreg hir hs hl

end Omega.Refinement.Regular
