/- GID: D5/S3/Combinatorics/Lattices/CyclotomicHNRestriction
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Lattices/CyclotomicHNRestriction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Monogenic algebraic scalar actions make Euclidean HN stages saturated modules. -/

import D5.S3.Combinatorics.Lattices.EuclideanHNEquivariance
import Mathlib.RingTheory.Algebraic.Basic
import Mathlib.RingTheory.Adjoin.Basic

/-! Restriction of scalars for a monogenic algebraic order acting by integral isometries.
Saturation is relative to the original lattice and includes every nonzero order scalar.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace D5.S3.Combinatorics.Lattices.CyclotomicHNRestriction

open EuclideanSublattices EuclideanHarderNarasimhan EuclideanHNEquivariance
open HarderNarasimhan

variable {A E : Type*} [CommRing A] [NoZeroDivisors A]
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [Module A E]
variable (z : A) (hz : Algebra.adjoin ℤ ({z} : Set A) = ⊤)

omit [NoZeroDivisors A] [InnerProductSpace ℝ E] in
include hz in
private theorem generated_stable (N : Submodule ℤ E)
    (hN : ∀ x ∈ N, z • x ∈ N) (a : A) : ∀ x ∈ N, a • x ∈ N := by
  have ha : a ∈ Algebra.adjoin ℤ ({z} : Set A) := by rw [hz]; trivial
  induction ha using Algebra.adjoin_induction with
  | mem a ha => simpa only [Set.mem_singleton_iff.mp ha] using hN
  | algebraMap r =>
    intro x hx
    simpa only [algebraMap_smul] using N.smul_mem r hx
  | add a b ha hb ia ib =>
    intro x hx
    simpa only [add_smul] using N.add_mem (ia x hx) (ib x hx)
  | mul a b ha hb ia ib =>
    intro x hx
    simpa only [mul_smul] using ia (b • x) (ib x hx)

private def orderModule (N : Submodule ℤ E) (hN : ∀ x ∈ N, z • x ∈ N) :
    Submodule A E where
  carrier := N
  zero_mem' := N.zero_mem
  add_mem' := N.add_mem
  smul_mem' := generated_stable z hz N hN

variable (L : Submodule ℤ E) (T : E ≃ₗᵢ[ℝ] E)
variable (hT : L.map (T.toLinearMap.restrictScalars ℤ) = L)
variable (hact : ∀ x : E, T x = z • x)

omit [NoZeroDivisors A] in
include hact in
private theorem fixed_stable (F : Sublattice L)
    (hF : sublatticeMap L T hT F = F) :
    ∀ x ∈ integral L F, z • x ∈ integral L F := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hx
  have hmem : latticeEquiv L T hT y ∈
      F.val.map (latticeEquiv L T hT).toLinearMap :=
    Submodule.mem_map_of_mem hy
  have heq : F.val.map (latticeEquiv L T hT).toLinearMap = F.val :=
    congrArg Subtype.val hF
  rw [heq] at hmem
  have hout : (T y : E) ∈ integral L F :=
    Submodule.mem_map.mpr ⟨latticeEquiv L T hT y, hmem, rfl⟩
  rwa [hact] at hout

private theorem int_saturated (F : Sublattice L) (m : ℤ) (hm : m ≠ 0)
    (x : E) (hx : x ∈ L) (hmx : m • x ∈ integral L F) : x ∈ integral L F := by
  apply integral_saturated L F x hx
  have hspan : m • x ∈ EuclideanHarderNarasimhan.realSpan (integral L F) :=
    Submodule.subset_span hmx
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm
  have h := (EuclideanHarderNarasimhan.realSpan (integral L F)).smul_mem
    (m : ℝ)⁻¹ hspan
  simpa only [← Int.cast_smul_eq_zsmul ℝ, smul_smul, inv_mul_cancel₀ hmR,
    one_smul] using h

variable [Algebra.IsAlgebraic ℤ A]

include hz hact in
private theorem fixed_saturated (F : Sublattice L)
    (hF : sublatticeMap L T hT F = F) :
    ∃ P : Submodule A E, P.restrictScalars ℤ = integral L F ∧
      ∀ (a : A), a ≠ 0 → ∀ x ∈ L, a • x ∈ P → x ∈ P := by
  let P := orderModule z hz (integral L F) (fixed_stable z L T hT hact F hF)
  refine ⟨P, rfl, ?_⟩
  intro a ha x hx hax
  obtain ⟨c, m, hm, hmc⟩ := Algebra.IsAlgebraic.exists_smul_eq_mul ℤ (1 : A) ha
  have hmx : m • x ∈ integral L F := by
    have h := P.smul_mem c hax
    have heq : m • x = c • (a • x) := by
      rw [← mul_smul, mul_comm c a, ← hmc, smul_assoc, one_smul]
    rwa [← heq] at h
  exact int_saturated L F m hm x hx hmx

variable [FiniteDimensional ℝ E] [DiscreteTopology L]

include hz hT hact in
/-- All HN stages and all strict slope truncations are saturated modules over the
monogenic algebraic order. No finite-order hypothesis on the generator is needed. -/
theorem hn_saturated (l : List (Sublattice L))
    (hl : (slopeData L).Filtration ⊥ ⊤ l) :
    let saturated := fun F : Sublattice L =>
      ∃ P : Submodule A E, P.restrictScalars ℤ = integral L F ∧
        ∀ (a : A), a ≠ 0 → ∀ x ∈ L, a • x ∈ P → x ∈ P
    (∀ F ∈ l, saturated F) ∧
      ∀ t : ℝ, saturated (above L (slopeData L) t ⊥ l) := by
  have hb : sublatticeMap L T hT ⊥ = ⊥ := (sublatticeEquiv L T hT).map_bot
  have ht : sublatticeMap L T hT ⊤ = ⊤ := (sublatticeEquiv L T hT).map_top
  have h := (isometry_hn L T hT).2.2 ⊥ ⊤ l hb ht hl
  exact ⟨fun F hF => fixed_saturated z hz L T hT hact F (h.2.1 F hF),
    fun t => fixed_saturated z hz L T hT hact _ (h.2.2 t)⟩

/-- Stability of the actual ambient sublattice under all order scalars. -/
def OrderStable (F : Sublattice L) : Prop :=
  ∀ (a : A) (x : E), x ∈ integral L F → a • x ∈ integral L F

/-- Semistability tested only on order-stable subobjects, with a common slope shift. -/
def OrderSemistable (c : ℝ) (F G : Sublattice L) : Prop :=
  F < G ∧ ∀ X : Sublattice L, OrderStable (A := A) L X → F < X → X ≤ G →
    (slopeData L).slope F X + c ≤ (slopeData L).slope F G + c

omit [FiniteDimensional ℝ E] [DiscreteTopology L] in
private theorem mem_integral (F : Sublattice L) (x : L) :
    (x : E) ∈ integral L F ↔ x ∈ F.val := by
  constructor
  · rintro ⟨y, hy, he⟩
    exact (Subtype.ext he : y = x) ▸ hy
  · intro hx
    exact Submodule.mem_map.mpr ⟨x, hx, rfl⟩

omit [NoZeroDivisors A] [Algebra.IsAlgebraic ℤ A] [FiniteDimensional ℝ E]
  [DiscreteTopology L] in
include hz hact in
private theorem stable_of_fixed (F : Sublattice L)
    (hF : sublatticeMap L T hT F = F) : OrderStable (A := A) L F :=
  generated_stable z hz (integral L F) (fixed_stable z L T hT hact F hF)

omit [NoZeroDivisors A] [Algebra.IsAlgebraic ℤ A] in
include hact in
private theorem fixed_of_stable (F : Sublattice L) (hF : OrderStable (A := A) L F) :
    sublatticeMap L T hT F = F := by
  have hle : sublatticeMap L T hT F ≤ F := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hx
    apply (mem_integral L F _).mp
    change T (y : E) ∈ integral L F
    rw [hact]
    exact hF z y ((mem_integral L F y).mpr hy)
  apply le_antisymm hle
  by_contra h
  have hlt : sublatticeMap L T hT F < F := lt_of_le_not_ge hle h
  have hr := (slopeData L).rank_strictMono hlt
  rw [((isometry_hn L T hT).1 F).1] at hr
  exact (lt_irrefl _ hr)

omit [NoZeroDivisors A] [Algebra.IsAlgebraic ℤ A] in
include hz hT hact in
private theorem semistable_iff (c : ℝ) (F G : Sublattice L)
    (hF : OrderStable (A := A) L F) (hG : OrderStable (A := A) L G) :
    (slopeData L).Semistable F G ↔ OrderSemistable (A := A) L c F G := by
  constructor
  · intro h
    refine ⟨h.1, fun X _ hFX hXG => ?_⟩
    have hb := h.2 X hFX hXG
    linarith
  · intro h
    obtain ⟨l, hl, _⟩ := ((euclidean_hn L F G).2.1).mpr h.1.le
    cases l with
    | nil => cases hl; exact (lt_irrefl _ h.1).elim
    | cons X l =>
      have hf := (isometry_hn L T hT).2.2 F G (X :: l)
        (fixed_of_stable z L T hT hact F hF)
        (fixed_of_stable z L T hT hact G hG) hl
      have hX := stable_of_fixed z hz L T hT hact X (hf.2.1 X (List.mem_cons_self ..))
      have hm := (filtration_extremes (slopeData L) F G X l hl).2.2.1
      have hFX : F < X := by cases hl with | cons hs _ _ _ => exact hs.1
      have hXG : X ≤ G := by cases hl with | cons _ hXG _ _ => exact hXG
      have hbound : (slopeData L).slope F X ≤ (slopeData L).slope F G := by
        have hb := h.2 X hX hFX hXG
        linarith
      refine ⟨h.1, fun Y hFY hYG => ?_⟩
      exact (hm.2 ⟨Y, hFY, hYG, rfl⟩).trans hbound

omit [NoZeroDivisors A] [Algebra.IsAlgebraic ℤ A] in
include hz hT hact in
/-- Testing only order submodules gives exactly the same semistability, on every
order-stable interval. The common additive shift is arbitrary. -/
theorem semistable_restriction (c : ℝ) (F G : Sublattice L)
    (hF : OrderStable (A := A) L F) (hG : OrderStable (A := A) L G) :
    (slopeData L).Semistable F G ↔ OrderSemistable (A := A) L c F G :=
  semistable_iff z hz L T hT hact c F G hF hG

/-- The first order slope of a tail lies strictly below the given bound. -/
def OrderStartsBelow (c : ℝ) (F : Sublattice L) (t : ℝ) :
    List (Sublattice L) → Prop
  | [] => True
  | G :: _ => (slopeData L).slope F G + c < t

/-- HN filtrations tested on order subobjects and using the shifted normalized slope. -/
inductive OrderFiltration (c : ℝ) :
    Sublattice L → Sublattice L → List (Sublattice L) → Prop
  | nil (F : Sublattice L) (hF : OrderStable (A := A) L F) : OrderFiltration c F F []
  | cons {F G H : Sublattice L} {l : List (Sublattice L)}
      (hs : OrderSemistable (A := A) L c F G) (hG : OrderStable (A := A) L G)
      (hGH : G ≤ H) (tail : OrderFiltration c G H l)
      (drop : OrderStartsBelow L c G ((slopeData L).slope F G + c) l) :
      OrderFiltration c F H (G :: l)

private theorem startsBelow_iff (c : ℝ) (F G : Sublattice L)
    (l : List (Sublattice L)) :
    OrderStartsBelow L c G ((slopeData L).slope F G + c) l ↔
      (slopeData L).StartsBelow G ((slopeData L).slope F G) l := by
  cases l with
  | nil => rfl
  | cons H l =>
    change _ + c < _ + c ↔ _ < _
    constructor <;> intro h <;> linarith

omit [NoZeroDivisors A] [Algebra.IsAlgebraic ℤ A] in
include hz hT hact in
/-- The entire HN chain agrees with the HN chain tested on order subobjects.
Every factor slope is translated by the same arbitrary real constant. -/
theorem filtration_restriction (c : ℝ) (F G : Sublattice L)
    (hF : OrderStable (A := A) L F) (hG : OrderStable (A := A) L G)
    (l : List (Sublattice L)) :
    (slopeData L).Filtration F G l ↔ OrderFiltration (A := A) L c F G l := by
  induction l generalizing F with
  | nil =>
    constructor
    · intro h
      cases h
      exact .nil _ hF
    · intro h
      cases h
      exact .nil _
  | cons H l ih =>
    constructor
    · intro h
      have hf := (isometry_hn L T hT).2.2 F G (H :: l)
        (fixed_of_stable z L T hT hact F hF)
        (fixed_of_stable z L T hT hact G hG) h
      have hH := stable_of_fixed z hz L T hT hact H (hf.2.1 H (List.mem_cons_self ..))
      cases h with
      | cons hs hHG tail drop =>
        exact .cons ((semistable_restriction z hz L T hT hact c F H hF hH).mp hs)
          hH hHG ((ih H hH).mp tail) ((startsBelow_iff L c F H l).mpr drop)
    · intro h
      cases h with
      | cons hs hH hHG tail drop =>
        exact .cons ((semistable_restriction z hz L T hT hact c F H hF hH).mpr hs)
          hHG ((ih H hH).mpr tail) ((startsBelow_iff L c F H l).mp drop)

end D5.S3.Combinatorics.Lattices.CyclotomicHNRestriction
