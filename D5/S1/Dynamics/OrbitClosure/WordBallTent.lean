/- GID: D5/S1/Dynamics/OrbitClosure/WordBallTent
   generality: G
   mirror-B: D5/B/S1/Dynamics/OrbitClosure/WordBallTent
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Continuous word-ball tents for infinite finitely generated actions. -/

module

public import Mathlib.GroupTheory.Finiteness
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.GroupTheory.Generators
public import Mathlib.GroupTheory.GroupAction.Basic
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.GroupTheory.Index
public import Mathlib.Topology.Separation.Regular
public import Mathlib.Topology.UrysohnsLemma
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Topology.Order.Lattice
public import Mathlib.Tactic.Linarith
public import Mathlib.Geometry.Group.WordMetric
public import OmegaBuild.Commands

/-! Word-ball constructions for continuous actions on compact Hausdorff spaces. -/

@[expose] public section

compile_only_with_mathlib

open Set Function
open scoped Pointwise

namespace D5.S1.Dynamics.OrbitClosure.WordBallTent

noncomputable section

universe u v

variable {G : Type u} {X : Type v} [Group G]

local instance : DecidableEq G := Classical.decEq G

private theorem finite_hom_of_finite_generators (S : Finset G)
    (hS : Subgroup.closure (S : Set G) = ⊤)
    {H : Type*} [Group H] [Finite H] : Finite (G →* H) := by
  classical
  let P : Group.Generators G S := Group.Generators.ofSet hS
  let e : (G →* H) → (S → H) := fun f s => f s
  apply Finite.of_injective e
  intro f g hfg
  apply P.hom_ext f g
  intro s
  exact congrFun hfg s

private def transportPerm {A B : Type*} (e : A ≃ B) :
    Equiv.Perm A →* Equiv.Perm B where
  toFun p := e.symm.trans (p.trans e)
  map_one' := by ext x; simp
  map_mul' p q := by ext x; simp

/-- Uniformly bounded finite orbits force finite image for a finitely generated group. -/
private theorem finite_image_of_bounded_orbits [MulAction G X]
    (S : Finset G) (hS : Subgroup.closure (S : Set G) = ⊤)
    (N : ℕ) (hfinite : ∀ x : X, Finite (MulAction.orbit G x))
    (hcard : ∀ x : X, Nat.card (MulAction.orbit G x) ≤ N) :
    Finite (MulAction.toPermHom G X).range := by
  classical
  letI (n : Fin (N + 1)) : Finite (G →* Equiv.Perm (Fin n.val)) :=
    finite_hom_of_finite_generators S hS
  let K : Subgroup G := ⨅ (n : Fin (N + 1)) (f : G →* Equiv.Perm (Fin n.val)), f.ker
  have hK : K.FiniteIndex := Subgroup.finiteIndex_iInf fun n =>
    Subgroup.finiteIndex_iInf fun f => inferInstance
  have hle : K ≤ (MulAction.toPermHom G X).ker := by
    intro g hg
    rw [MonoidHom.mem_ker]
    apply Equiv.ext
    intro x
    letI : Finite (MulAction.orbit G x) := hfinite x
    letI : Fintype (MulAction.orbit G x) := Fintype.ofFinite _
    let n : Fin (N + 1) := ⟨Nat.card (MulAction.orbit G x), Nat.lt_succ_of_le (hcard x)⟩
    let e : MulAction.orbit G x ≃ Fin n.val :=
      Fintype.equivFinOfCardEq (Nat.card_eq_fintype_card.symm)
    let f : G →* Equiv.Perm (Fin n.val) :=
      (transportPerm e).comp (MulAction.toPermHom G (MulAction.orbit G x))
    have hfg : f g = 1 := MonoidHom.mem_ker.mp
      (Subgroup.mem_iInf.mp (Subgroup.mem_iInf.mp hg n) f)
    let q : MulAction.orbit G x := ⟨x, MulAction.mem_orbit_self x⟩
    have heq := congrArg (fun p : Equiv.Perm (Fin n.val) => p (e q)) hfg
    have hq : g • q = q := e.injective (by simpa [f, transportPerm] using heq)
    exact congrArg Subtype.val hq
  letI : (MulAction.toPermHom G X).ker.FiniteIndex := Subgroup.finiteIndex_of_le hle
  exact Finite.of_equiv _ (QuotientGroup.quotientKerEquivRange
    (MulAction.toPermHom G X)).toEquiv

/-- A single orbit escapes any prescribed finite collection of translates. -/
private theorem exists_orbit_outside_finset [MulAction G X]
    (S : Finset G) (hS : Subgroup.closure (S : Set G) = ⊤)
    (hinf : (Set.range (MulAction.toPermHom G X)).Infinite) (B : Finset G) :
    ∃ x : X, ∃ g : G, ∀ b ∈ B, b • x ≠ g • x := by
  classical
  by_contra! h
  have cover (x : X) : ∀ g : G, ∃ b ∈ B, b • x = g • x := h x
  let f (x : X) : B → MulAction.orbit G x :=
    fun b => ⟨b.1 • x, MulAction.mem_orbit x b.1⟩
  have hf (x : X) : Surjective (f x) := by
    rintro ⟨y, g, rfl⟩
    obtain ⟨b, hb, he⟩ := cover x g
    exact ⟨⟨b, hb⟩, Subtype.ext he⟩
  have hfinite (x : X) : Finite (MulAction.orbit G x) := Finite.of_surjective (f x) (hf x)
  have hcard (x : X) : Nat.card (MulAction.orbit G x) ≤ B.card := by
    simpa using Nat.card_le_card_of_surjective (f x) (hf x)
  letI : Finite (MulAction.toPermHom G X).range :=
    finite_image_of_bounded_orbits S hS B.card hfinite hcard
  apply hinf
  change Set.Finite ((MulAction.toPermHom G X).range : Set (Equiv.Perm X))
  exact Set.toFinite _

private def wordBall (S : Finset G) : ℕ → Finset G
  | 0 => {1}
  | n + 1 => wordBall S n ∪ S.biUnion (fun s => (wordBall S n).image (fun g => s * g))

private theorem one_mem_wordBall (S : Finset G) (n : ℕ) : (1 : G) ∈ wordBall S n := by
  induction n with
  | zero => simp [wordBall]
  | succ n ih => exact Finset.mem_union_left _ ih

private theorem finite_wordBall (S : Finset G) (n : ℕ) : Set.Finite (wordBall S n : Set G) := by
  exact (wordBall S n).finite_toSet

private theorem generator_wordLength_le (S : Finset G)
    (hS : Subgroup.closure (S : Set G) = ⊤) {s : G} (hs : s ∈ S) :
    (Group.Generators.ofSet hS).wordLength s ≤ 1 := by
  apply (Group.Generators.wordLength_le_iff _ _).mpr
  exact ⟨[(⟨s, hs⟩, true)], by simp, by simp⟩

private theorem wordProd_mem_wordBall (S : Finset G)
    (hsym : ∀ s ∈ S, s⁻¹ ∈ S) (hS : Subgroup.closure (S : Set G) = ⊤)
    {n : ℕ} (l : List (S × Bool)) (hlen : l.length ≤ n) :
    (Group.Generators.ofSet hS).wordProd l ∈ wordBall S n := by
  induction n generalizing l with
  | zero =>
      have hl : l = [] := List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero hlen)
      subst l
      simp [wordBall]
  | succ n ih =>
      cases l with
      | nil => simpa using one_mem_wordBall S (n + 1)
      | cons a t =>
          obtain ⟨i, b⟩ := a
          have ht := ih t (by simpa using hlen)
          have ha : (cond b (i : G) (i : G)⁻¹) ∈ S := by
            cases b
            · exact hsym i i.property
            · exact i.property
          rw [Group.Generators.wordProd_cons]
          exact Finset.mem_union_right _
            (Finset.mem_biUnion.mpr ⟨_, ha,
              Finset.mem_image.mpr ⟨_, ht, rfl⟩⟩)

private theorem mem_wordBall_wordLength_le (S : Finset G)
    (hS : Subgroup.closure (S : Set G) = ⊤) {n : ℕ} {g : G}
    (hg : g ∈ wordBall S n) : (Group.Generators.ofSet hS).wordLength g ≤ n := by
  induction n generalizing g with
  | zero =>
      have : g = 1 := by simpa [wordBall] using hg
      subst g
      simp
  | succ n ih =>
      rw [wordBall, Finset.mem_union] at hg
      rcases hg with hg | hg
      · exact (ih hg).trans (Nat.le_succ n)
      · obtain ⟨a, ha, hg⟩ := Finset.mem_biUnion.mp hg
        obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hg
        have hmul := (Group.Generators.ofSet hS).wordLength_mul_le a b
        have hleft := generator_wordLength_le S hS ha
        have hright := ih hb
        omega

private theorem wordBall_length_iff (S : Finset G)
    (hsym : ∀ s ∈ S, s⁻¹ ∈ S) (hS : Subgroup.closure (S : Set G) = ⊤)
    (n : ℕ) (g : G) :
    g ∈ wordBall S n ↔ (Group.Generators.ofSet hS).wordLength g ≤ n := by
  constructor
  · exact mem_wordBall_wordLength_le S hS
  · intro hg
    obtain ⟨l, hl, he⟩ := ((Group.Generators.ofSet hS).wordLength_le_iff g).mp hg
    rw [← he]
    exact wordProd_mem_wordBall S hsym hS l hl

private def weight (R : ℝ) (n : ℕ) : ℝ := max 0 (1 - (n : ℝ) / R)

private theorem weight_nonneg (R : ℝ) (n : ℕ) : 0 ≤ weight R n := le_max_left _ _

private theorem weight_le_one {R : ℝ} (hR : 0 < R) (n : ℕ) : weight R n ≤ 1 := by
  apply max_le zero_le_one
  have : 0 ≤ (n : ℝ) / R := div_nonneg (Nat.cast_nonneg _) hR.le
  linarith

private theorem weight_zero {R : ℝ} (hR : 0 < R) {n : ℕ}
    (hn : R ≤ (n : ℝ)) : weight R n = 0 := by
  apply max_eq_left
  have : 1 ≤ (n : ℝ) / R := (le_div_iff₀ hR).mpr (by simpa using hn)
  linarith

private theorem weight_step {R : ℝ} (hR : 0 < R) {m n : ℕ} (hm : m ≤ n + 1) :
    weight R n ≤ weight R m + 1 / R := by
  have hm' : (m : ℝ) ≤ (n : ℝ) + 1 := by exact_mod_cast hm
  have hd := (div_le_div_iff_of_pos_right hR).mpr hm'
  rw [add_div] at hd
  have hz := weight_nonneg R m
  have hq : 0 ≤ 1 / R := (one_div_pos.mpr hR).le
  apply max_le (by linarith)
  have hmle : 1 - (m : ℝ) / R ≤ weight R m := le_max_right _ _
  linarith

/-- Infinite-image actions admit continuous tents with prescribed slow variation.

proof_shape: content.
escape_witness: the finite transported maximum constructed from a separating
continuous function has simultaneous generator defect at most the reciprocal
radius and takes both endpoint values on one actual orbit.
admission_basis: escape-witness. The private finite-family and word-ball helpers
are consumed by this construction and receive no independent content credit. -/
theorem exists_continuous_wordBall_tent
    [TopologicalSpace X] [CompactSpace X] [T2Space X] [MulAction G X]
    (S : Finset G) (hsym : ∀ s ∈ S, s⁻¹ ∈ S)
    (hS : Subgroup.closure (S : Set G) = ⊤)
    (hcont : ∀ g : G, Continuous (fun x : X => g • x))
    (hinf : (Set.range (MulAction.toPermHom G X)).Infinite)
    (R : ℕ) (hR : 1 ≤ R) :
    ∃ u : C(X, ℝ), ∃ x₀ : X, ∃ g₀ : G,
      (∀ x, 0 ≤ u x ∧ u x ≤ 1) ∧ u x₀ = 1 ∧ u (g₀ • x₀) = 0 ∧
      (∀ s ∈ S, ∀ x, |u (s • x) - u x| ≤ 1 / (R : ℝ)) ∧
      (∀ v : C(X, ℝ), (∀ g : G, ∀ x : X, v (g • x) = v x) →
        (1 / 2 : ℝ) ≤ ‖u - v‖) := by
  classical
  have hRpos : 0 < (R : ℝ) := by exact_mod_cast (show 0 < R by omega)
  let P : Group.Generators G S := Group.Generators.ofSet hS
  let L : G → ℕ := P.wordLength
  let B := wordBall S R
  have hB : B.Nonempty := ⟨1, one_mem_wordBall S R⟩
  obtain ⟨x₀, g₀, hfar⟩ := exists_orbit_outside_finset S hS hinf B
  let z := g₀ • x₀
  let F : Set X := (fun g : G => g⁻¹ • z) '' (B : Set G)
  have hFc : IsClosed F := (finite_wordBall S R |>.image _).isClosed
  have hdis : Disjoint F {x₀} := by
    apply Set.disjoint_singleton_right.mpr
    rintro ⟨g, hg, he⟩
    have he' : g • x₀ = z := by rw [← he]; simp
    exact hfar g hg he'
  obtain ⟨φ, hφF, hφx, hφrange⟩ := exists_continuous_zero_one_of_isClosed
    hFc isClosed_singleton hdis
  have hφone : φ x₀ = 1 := hφx (Set.mem_singleton x₀)
  let term : G → X → ℝ := fun g x => weight (R : ℝ) (L g) * φ (g⁻¹ • x)
  let U : X → ℝ := fun x => B.sup' hB (fun g => term g x)
  have hUc : Continuous U := Continuous.finset_sup'_apply hB fun g _ =>
    continuous_const.mul (φ.continuous.comp (hcont g⁻¹))
  let u : C(X, ℝ) := ⟨U, hUc⟩
  have ht0 (g : G) (x : X) : 0 ≤ term g x :=
    mul_nonneg (weight_nonneg _ _) (hφrange _).1
  have ht1 (g : G) (x : X) : term g x ≤ 1 := by
    calc
      term g x ≤ 1 * φ (g⁻¹ • x) :=
        mul_le_mul_of_nonneg_right (weight_le_one hRpos _) (hφrange _).1
      _ ≤ 1 := by simpa using (hφrange (g⁻¹ • x)).2
  have hu0 (x : X) : 0 ≤ u x :=
    (ht0 1 x).trans (Finset.le_sup' (fun g => term g x) (one_mem_wordBall S R))
  have hu1 (x : X) : u x ≤ 1 := Finset.sup'_le hB _ (fun g _ => ht1 g x)
  have htU (g : G) (x : X) : term g x ≤ u x := by
    by_cases hg : g ∈ B
    · exact Finset.le_sup' (fun b => term b x) hg
    · have hlen : R ≤ L g := by
        have : ¬ L g ≤ R := fun h => hg ((wordBall_length_iff S hsym hS R g).mpr h)
        omega
      have hw : weight (R : ℝ) (L g) = 0 := weight_zero hRpos (by exact_mod_cast hlen)
      simpa [term, hw] using hu0 x
  have huone : u x₀ = 1 := by
    apply le_antisymm (hu1 _)
    have he : term 1 x₀ = 1 := by
      simp [term, L, Group.Generators.wordLength_one, weight, hφone]
    rw [← he]
    exact htU 1 x₀
  have huzero : u z = 0 := by
    apply le_antisymm _ (hu0 _)
    apply Finset.sup'_le hB
    intro g hg
    have hzero : φ (g⁻¹ • z) = 0 := hφF ⟨g, hg, rfl⟩
    simp [term, hzero]
  have hforward : ∀ s ∈ S, ∀ x, u (s • x) ≤ u x + 1 / (R : ℝ) := by
    intro s hs x
    apply Finset.sup'_le hB
    intro g hg
    let k := s⁻¹ * g
    have hls : L s⁻¹ ≤ 1 := by
      change P.wordLength s⁻¹ ≤ 1
      rw [P.wordLength_inv]
      exact generator_wordLength_le S hS hs
    have hlk : L k ≤ L g + 1 := by
      have hm := P.wordLength_mul_le s⁻¹ g
      dsimp [k, L] at *
      omega
    have hw := weight_step hRpos hlk
    have hp := (hφrange (k⁻¹ • x))
    have he : g⁻¹ • (s • x) = k⁻¹ • x := by simp [k, mul_smul]
    have ht : term g (s • x) ≤ term k x + 1 / (R : ℝ) := by
      dsimp [term]
      rw [he]
      have hh := mul_le_mul_of_nonneg_right hw hp.1
      have hsmall := mul_le_mul_of_nonneg_left hp.2 (one_div_pos.mpr hRpos).le
      nlinarith
    linarith [htU k x]
  refine ⟨u, x₀, g₀, (fun x => ⟨hu0 x, hu1 x⟩), huone, huzero, ?_, ?_⟩
  · intro s hs x
    apply abs_le.mpr
    have hf := hforward s hs x
    have hb := hforward s⁻¹ (hsym s hs) (s • x)
    simp only [inv_smul_smul] at hb
    constructor <;> linarith
  · intro v hv
    have h₁ := (u - v).norm_coe_le_norm x₀
    have h₂ := (u - v).norm_coe_le_norm z
    have hvz : v z = v x₀ := hv g₀ x₀
    simp only [ContinuousMap.sub_apply, Real.norm_eq_abs, huone, huzero, hvz] at h₁ h₂
    have ha := le_abs_self (1 - v x₀)
    have hb := neg_le_abs (0 - v x₀)
    linarith

#print axioms exists_continuous_wordBall_tent

end
end D5.S1.Dynamics.OrbitClosure.WordBallTent
