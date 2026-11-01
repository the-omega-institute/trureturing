/- GID: D5/S3/Geometry/FiniteCoordinateTruncation
   generality: G
   mirror-B: D5/B/S3/Geometry/FiniteCoordinateTruncation
   mirror-E: none(waiver:finite-coordinate-topology)
   anchors: [mathlib/module/Mathlib.AlgebraicTopology.SimplicialComplex.Basic]
   utility: none
   digest: Support tests, normalization, and straight homotopies in actual finite independence realizations. -/
import D5.S3.Geometry.FiniteGraphVertexSubstitution
import Mathlib.Topology.Homotopy.Contractible

/-!
Coordinate support for `FiniteGraphSubgraphSuspension`.  The carrier throughout
is `FiniteConeCollapse.realization`, not a replacement homology theory.

-/

noncomputable section
open Set Topology
open scoped BigOperators unitInterval ContinuousMap

namespace D5.S3.Geometry.FiniteCoordinateTruncation

open FiniteConeCollapse FiniteGraphVertexSubstitution

variable {V : Type*} [Fintype V] [DecidableEq V]

def Probability (x : V → ℝ) : Prop := (∀ a, 0 ≤ x a) ∧ ∑ a, x a = 1

def Avoid (G : SimpleGraph V) (x : V → ℝ) : Prop :=
  ∀ a b, G.Adj a b → x a = 0 ∨ x b = 0

def support (x : V → ℝ) : Finset V :=
  by classical exact Finset.univ.filter fun a => x a ≠ 0

@[simp] theorem mem_support (x : V → ℝ) (a : V) :
    a ∈ support x ↔ x a ≠ 0 := by
  classical
  simp [support]

theorem support_nonempty {x : V → ℝ} (hx : Probability x) :
    (support x).Nonempty := by
  obtain ⟨a, _, ha⟩ := Finset.exists_ne_zero_of_sum_ne_zero
    (show (∑ a, x a) ≠ 0 by rw [hx.2]; norm_num)
  exact ⟨a, (mem_support x a).mpr ha⟩

theorem independent_support_iff (G : SimpleGraph V) (x : V → ℝ) :
    G.IsIndepSet (support x : Set V) ↔ Avoid G x := by
  constructor
  · intro h a b hab
    by_cases ha : x a = 0
    · exact Or.inl ha
    · right
      by_contra hb
      exact h ((mem_support x a).mpr ha) ((mem_support x b).mpr hb)
        (G.ne_of_adj hab) hab
  · intro h a ha b hb _ hab
    rcases h a b hab with h | h
    · exact (mem_support x a).mp ha h
    · exact (mem_support x b).mp hb h

theorem realization_iff (G : SimpleGraph V) (x : V → ℝ) :
    x ∈ realization (independenceComplex G).toPreAbstractSimplicialComplex ↔
      Probability x ∧ Avoid G x := by
  constructor
  · rintro ⟨s, ⟨_, hs⟩, hx⟩
    rw [← faceSimplex_eq_convexHull] at hx
    refine ⟨⟨hx.1, hx.2.1⟩, ?_⟩
    intro a b hab
    by_cases ha : a ∈ s
    · by_cases hb : b ∈ s
      · exact (hs ha hb (G.ne_of_adj hab) hab).elim
      · exact Or.inr (hx.2.2 b hb)
    · exact Or.inl (hx.2.2 a ha)
  · rintro ⟨hp, hi⟩
    refine ⟨support x, ⟨support_nonempty hp,
      (independent_support_iff G x).mpr hi⟩, ?_⟩
    rw [← faceSimplex_eq_convexHull]
    exact ⟨hp.1, hp.2, fun a ha => by simpa using ha⟩

abbrev Ispace (G : SimpleGraph V) :=
  ↥(realization (independenceComplex G).toPreAbstractSimplicialComplex)

theorem probability (G : SimpleGraph V) (x : Ispace G) : Probability x.val :=
  ((realization_iff G x.val).mp x.property).1

theorem avoid (G : SimpleGraph V) (x : Ispace G) : Avoid G x.val :=
  ((realization_iff G x.val).mp x.property).2

def vertex (G : SimpleGraph V) (a : V) : Ispace G :=
  ⟨Pi.single a 1, ⟨{a}, (independenceComplex G).singleton_mem a,
    subset_convexHull ℝ _ ⟨a, Finset.mem_singleton_self a, rfl⟩⟩⟩

theorem avoid_of_support {G : SimpleGraph V} {x y : V → ℝ}
    (hx : Avoid G x) (hy : ∀ a, x a = 0 → y a = 0) : Avoid G y := by
  intro a b hab
  exact (hx a b hab).imp (hy a) (hy b)

def mix (t : ℝ) (x y : V → ℝ) (a : V) : ℝ := (1 - t) * x a + t * y a

@[simp] theorem mix_zero (x y : V → ℝ) : mix 0 x y = x := by ext a; simp [mix]
@[simp] theorem mix_one (x y : V → ℝ) : mix 1 x y = y := by ext a; simp [mix]

theorem probability_mix {x y : V → ℝ} (hx : Probability x) (hy : Probability y)
    (t : I) : Probability (mix t x y) := by
  refine ⟨fun a => add_nonneg (mul_nonneg (sub_nonneg.mpr t.2.2) (hx.1 a))
    (mul_nonneg t.2.1 (hy.1 a)), ?_⟩
  simp only [mix, Finset.sum_add_distrib, ← Finset.mul_sum, hx.2, hy.2]
  ring

theorem mix_support {x y : V → ℝ} (hy : ∀ a, x a = 0 → y a = 0)
    (t : ℝ) (a : V) (ha : x a = 0) : mix t x y a = 0 := by
  simp [mix, ha, hy a ha]

theorem avoid_mix_of_support {G : SimpleGraph V} {x y : V → ℝ}
    (hx : Avoid G x) (hy : ∀ a, x a = 0 → y a = 0) (t : ℝ) :
    Avoid G (mix t x y) :=
  avoid_of_support hx (mix_support hy t)

theorem avoid_mix {G : SimpleGraph V} {x y : V → ℝ}
    (h : ∀ a b, G.Adj a b →
      (x a = 0 ∧ y a = 0) ∨ (x b = 0 ∧ y b = 0)) (t : ℝ) :
    Avoid G (mix t x y) := by
  intro a b hab
  rcases h a b hab with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · left; simp [mix, ha, hb]
  · right; simp [mix, ha, hb]

def normalize (x : V → ℝ) (a : V) : ℝ := x a / ∑ b, x b

theorem probability_normalize {x : V → ℝ} (hx : ∀ a, 0 ≤ x a)
    (hs : 0 < ∑ a, x a) : Probability (normalize x) := by
  refine ⟨fun a => div_nonneg (hx a) hs.le, ?_⟩
  simp only [normalize, ← Finset.sum_div]
  exact div_self hs.ne'

theorem normalize_zero {x : V → ℝ} {a : V} (ha : x a = 0) :
    normalize x a = 0 := by simp [normalize, ha]

def cut (e : ℝ) (x : V → ℝ) (a : V) : ℝ := max (x a - e) 0

theorem cut_nonneg (e : ℝ) (x : V → ℝ) (a : V) : 0 ≤ cut e x a := le_max_right _ _

theorem cut_zero {e : ℝ} (he : 0 ≤ e) {x : V → ℝ} {a : V} (ha : x a = 0) :
    cut e x a = 0 := by simp [cut, ha, max_eq_right (neg_nonpos.mpr he)]

theorem cut_eq_zero {e : ℝ} {x : V → ℝ} {a : V} (ha : x a ≤ e) :
    cut e x a = 0 := max_eq_right (sub_nonpos.mpr ha)

theorem cut_sum_bound {x : V → ℝ} (hx : Probability x) (e : ℝ) :
    1 - (Fintype.card V : ℝ) * e ≤ ∑ a, cut e x a := by
  calc
    1 - (Fintype.card V : ℝ) * e = ∑ a, (x a - e) := by
      rw [Finset.sum_sub_distrib, hx.2]; simp
    _ ≤ ∑ a, cut e x a := Finset.sum_le_sum fun _ _ => le_max_left _ _

theorem continuous_normalize {X : Type*} [TopologicalSpace X] {f : X → V → ℝ}
    (hf : Continuous f) (hs : ∀ x, (∑ a, f x a) ≠ 0) :
    Continuous (fun x => normalize (f x)) := by
  apply continuous_pi
  intro a
  exact ((continuous_apply a).comp hf).div
    (continuous_finsetSum _ fun b _ => (continuous_apply b).comp hf) hs

theorem continuous_cut {X : Type*} [TopologicalSpace X] {f : X → V → ℝ}
    (hf : Continuous f) {e : X → ℝ} (he : Continuous e) :
    Continuous (fun x => cut (e x) (f x)) := by
  exact continuous_pi fun a => (((continuous_apply a).comp hf).sub he).max continuous_const

theorem continuous_mix {X : Type*} [TopologicalSpace X] {f g : X → V → ℝ}
    (hf : Continuous f) (hg : Continuous g) :
    Continuous (fun z : I × X => mix z.1 (f z.2) (g z.2)) := by
  apply continuous_pi
  intro a
  exact ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).mul
    ((continuous_apply a).comp (hf.comp continuous_snd))).add
    ((continuous_subtype_val.comp continuous_fst).mul
      ((continuous_apply a).comp (hg.comp continuous_snd)))

/-- Straight homotopy in a specified coordinate subspace, with membership proved
at the call site. This imposes no topological conclusion as an assumption. -/
def straight {X : Type*} [TopologicalSpace X] {D : Set (V → ℝ)}
    (f g : C(X, D)) (h : ∀ t : I, ∀ x, mix t (f x).val (g x).val ∈ D) :
    f.Homotopy g where
  toFun z := ⟨mix z.1 (f z.2).val (g z.2).val, h z.1 z.2⟩
  continuous_toFun := (continuous_mix
    (continuous_subtype_val.comp f.continuous)
    (continuous_subtype_val.comp g.continuous)).subtype_mk _
  map_zero_left x := Subtype.ext (mix_zero _ _)
  map_one_left x := Subtype.ext (mix_one _ _)

end D5.S3.Geometry.FiniteCoordinateTruncation
