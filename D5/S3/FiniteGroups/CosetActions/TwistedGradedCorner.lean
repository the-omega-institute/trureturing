/- GID: D5/S3/FiniteGroups/CosetActions/TwistedGradedCorner
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/CosetActions/TwistedGradedCorner
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Nondegenerate inverse-degree products force one-dimensional saturated grades. -/

module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.GroupTheory.GroupAction.Basic
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.LinearAlgebra.Pi
import OmegaBuild.Commands

/-!
The homogeneous spanning argument comes from Davydov–Simmons, *On Lagrangian algebras in
group-theoretical modular categories*, [Lemma 2.14](https://arxiv.org/abs/1603.04650).
Here the grading group is fixed in advance. Equality of the total dimension with its order
then forces every grade to occur.

For a transitive action on the neutral coordinates, orthogonal projections confine
each homogeneous component to the coordinates fixed by its degree. The count of
fixed pairs and equality of total dimensions force each such coordinate to occur.
-/

compile_only_with_mathlib

public section

set_option autoImplicit false

namespace D5.S3.FiniteGroups.CosetActions.TwistedGradedCorner

open scoped BigOperators

variable {K B : Type*} [Group K] [AddCommGroup B] [Module ℂ B]
variable {grade : K → Submodule ℂ B} {μ : B →ₗ[ℂ] B →ₗ[ℂ] B} {e : B}
variable {α : K → K → K → ℂˣ}

section Multiplication

variable (mul_mem : ∀ {g h : K} {x y : B},
  x ∈ grade g → y ∈ grade h → μ x y ∈ grade (g * h))
variable (unit_grade : grade 1 = Submodule.span ℂ {e})
variable (pairing : ∀ {g : K} {x : B}, x ∈ grade g → x ≠ 0 →
  ∃ y ∈ grade g⁻¹, μ x y ≠ 0)
variable (twisted_assoc : ∀ {g h k : K} {x y z : B},
  x ∈ grade g → y ∈ grade h → z ∈ grade k →
    (α g h k : ℂ) • μ (μ x y) z = μ x (μ y z))
variable (left_unit : ∀ x : B, μ e x = x) (right_unit : ∀ x : B, μ x e = x)

include mul_mem unit_grade pairing in
private theorem exists_inverse_product {g : K} {x : B} (hx : x ∈ grade g) (hx₀ : x ≠ 0) :
    ∃ y ∈ grade g⁻¹, ∃ t : ℂ, t ≠ 0 ∧ μ x y = t • e := by
  obtain ⟨y, hy, hxy⟩ := pairing hx hx₀
  have hmem : μ x y ∈ grade 1 := by simpa only [mul_inv_cancel] using mul_mem hx hy
  obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp (unit_grade ▸ hmem)
  refine ⟨y, hy, t, ?_, ht.symm⟩
  intro ht₀
  exact hxy (by rw [← ht, ht₀, zero_smul])

include mul_mem unit_grade pairing twisted_assoc left_unit right_unit in
/-- Any nonzero homogeneous vector spans its grade. -/
theorem grade_eq_span_singleton {g : K} {a : B} (ha : a ∈ grade g) (ha₀ : a ≠ 0) :
    grade g = Submodule.span ℂ {a} := by
  obtain ⟨b, hb, t, ht₀, hab⟩ := exists_inverse_product mul_mem unit_grade pairing ha ha₀
  apply le_antisymm _ ((Submodule.span_singleton_le_iff_mem _ _).mpr ha)
  intro c hc
  have hbc_mem : μ b c ∈ grade 1 := by simpa only [inv_mul_cancel] using mul_mem hb hc
  obtain ⟨u, hbc⟩ := Submodule.mem_span_singleton.mp (unit_grade ▸ hbc_mem)
  have h := twisted_assoc ha hb hc
  rw [hab, map_smul, LinearMap.smul_apply, left_unit, ← hbc, map_smul, right_unit, smul_smul] at h
  have hs : (↑(α g g⁻¹ g) : ℂ) * t ≠ 0 := mul_ne_zero (Units.ne_zero _) ht₀
  have hsmul : ((↑(α g g⁻¹ g) : ℂ) * t) • c ∈ Submodule.span ℂ {a} :=
    Submodule.mem_span_singleton.mpr ⟨u, h.symm⟩
  exact (Submodule.smul_mem_iff _ hs).mp hsmul

include mul_mem unit_grade pairing twisted_assoc right_unit in
/-- Multiplication of two nonzero homogeneous vectors gives a nonzero vector. -/
theorem homogeneous_mul_ne_zero {g h : K} {x y : B}
    (hx : x ∈ grade g) (hy : y ∈ grade h) (hx₀ : x ≠ 0) (hy₀ : y ≠ 0) : μ x y ≠ 0 := by
  obtain ⟨z, hz, t, ht₀, hyz⟩ := exists_inverse_product mul_mem unit_grade pairing hy hy₀
  intro hxy
  have h := twisted_assoc hx hy hz
  rw [hxy, map_zero, LinearMap.zero_apply, smul_zero, hyz, map_smul, right_unit] at h
  exact smul_ne_zero ht₀ hx₀ h.symm

include mul_mem unit_grade pairing twisted_assoc left_unit right_unit in
/-- Under the inverse-degree pairing and twisted associativity hypotheses, an
internal grading of total dimension `|K|` has a line in every degree. -/
theorem finrank_grade_eq_one [Fintype K] [DecidableEq K]
    (decomposition : DirectSum.IsInternal grade) (dimension : Module.finrank ℂ B = Fintype.card K)
    (g : K) : Module.finrank ℂ (grade g) = 1 := by
  have : FiniteDimensional ℂ B := Module.finite_of_finrank_pos (by
    rw [dimension]
    exact Fintype.card_pos)
  have hle (h : K) : Module.finrank ℂ (grade h) ≤ 1 := by
    by_cases hbot : grade h = ⊥
    · rw [hbot, finrank_bot]
      exact Nat.zero_le _
    · obtain ⟨a, ha, ha₀⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
      rw [grade_eq_span_singleton mul_mem unit_grade pairing twisted_assoc left_unit right_unit
        ha ha₀, finrank_span_singleton ha₀]
  have hsum : (∑ h : K, Module.finrank ℂ (grade h)) = Fintype.card K := by
    rw [← Module.finrank_directSum, (LinearEquiv.ofBijective
      (DirectSum.coeLinearMap grade) decomposition).finrank_eq, dimension]
  by_contra hne
  have hlt : (∑ h : K, Module.finrank ℂ (grade h)) < ∑ _ : K, (1 : ℕ) :=
    Finset.sum_lt_sum (fun h _ => hle h) ⟨g, Finset.mem_univ g, (hle g).lt_of_ne hne⟩
  simp [hsum] at hlt

end Multiplication

private theorem finrank_eq_sum_finrank_range {ι V : Type*} [Fintype ι]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (P : ι → V →ₗ[ℂ] V)
    (hidem : ∀ i v, P i (P i v) = P i v)
    (horth : ∀ i j, i ≠ j → ∀ v, P i (P j v) = 0)
    (hsum : ∀ v, (∑ i, P i v) = v) :
    Module.finrank ℂ V = ∑ i, Module.finrank ℂ (LinearMap.range (P i)) := by
  let coordinates : V →ₗ[ℂ] (∀ i, LinearMap.range (P i)) :=
    LinearMap.pi fun i => (P i).rangeRestrict
  have hinj : Function.Injective coordinates := by
    intro v w h
    calc
      v = ∑ i, P i v := (hsum v).symm
      _ = ∑ i, P i w := Finset.sum_congr rfl fun i _ =>
        congrArg (fun a : ∀ j, LinearMap.range (P j) => (a i : V)) h
      _ = w := hsum w
  have hsurj : Function.Surjective coordinates := by
    intro a
    refine ⟨∑ j, (a j : V), ?_⟩
    funext i
    apply Subtype.ext
    change P i (∑ j, (a j : V)) = (a i : V)
    rw [map_sum, Finset.sum_eq_single_of_mem i (Finset.mem_univ i)]
    · obtain ⟨v, hv⟩ := LinearMap.mem_range.mp (a i).property
      rw [← hv]
      exact hidem i v
    · intro j _ hji
      obtain ⟨v, hv⟩ := LinearMap.mem_range.mp (a j).property
      rw [← hv]
      exact horth i j hji.symm v
  exact (LinearEquiv.ofBijective coordinates ⟨hinj, hsurj⟩).finrank_eq.trans
    (Module.finrank_pi_fintype ℂ)

/-- The finrank of degree `g` counts the neutral coordinates fixed by `g`.
Every fixed corner range is a line, and every moved corner range has dimension zero.

For a twisted graded algebra take `P g x` to be left multiplication by the
neutral idempotent at `x`, restricted to degree `g`. In `htwist`, the two
projections agree because both products equal right multiplication by the
idempotent at `x` on degree `g`. -/
theorem finrank_grade_eq_card_fixedBy {G X V : Type*} [Group G] [Fintype G] [DecidableEq G]
    [Fintype X] [DecidableEq X] [Nonempty X] [MulAction G X] [MulAction.IsPretransitive G X]
    [AddCommGroup V] [Module ℂ V] (grading : G → Submodule ℂ V)
    (decomposition : DirectSum.IsInternal grading)
    (dimension : Module.finrank ℂ V = Fintype.card G)
    (P : ∀ g : G, X → grading g →ₗ[ℂ] grading g)
    (horth : ∀ (g : G) (x y : X), x ≠ y → ∀ b, P g x (P g y b) = 0)
    (hsum : ∀ (g : G) (b : grading g), (∑ x : X, P g x b) = b)
    (htwist : ∀ (g : G) (x : X) (b : grading g), P g x b = P g (g • x) b)
    (hline : ∀ (g : G) (x : X), g • x = x →
      Module.finrank ℂ (LinearMap.range (P g x)) ≤ 1)
    (g : G) :
    Module.finrank ℂ (grading g) = Nat.card (MulAction.fixedBy X g) ∧
      ∀ x : X, Module.finrank ℂ (LinearMap.range (P g x)) = (if g • x = x then 1 else 0) := by
  letI : FiniteDimensional ℂ V := Module.finite_of_finrank_pos (by
    rw [dimension]
    exact Fintype.card_pos)
  -- Orthogonality and the resolution of the identity imply idempotence.
  have hidem (h : G) (x : X) (b : grading h) : P h x (P h x b) = P h x b := by
    calc
      P h x (P h x b) = ∑ y : X, P h x (P h y b) :=
        (Finset.sum_eq_single_of_mem x (Finset.mem_univ x)
          (fun y _ hy => horth h x y hy.symm b)).symm
      _ = P h x b := by rw [← map_sum (P h x), hsum h b]
  have hzero (h : G) (x : X) (hx : h • x ≠ x) :
      Module.finrank ℂ (LinearMap.range (P h x)) = 0 := by
    have hmap : P h x = 0 := by
      apply LinearMap.ext
      intro b
      change P h x b = 0
      calc
        P h x b = P h x (P h x b) := (hidem h x b).symm
        _ = P h x (P h (h • x) b) := congrArg (P h x) (htwist h x b)
        _ = 0 := horth h x (h • x) hx.symm b
    rw [hmap, LinearMap.range_zero, finrank_bot]
  have hgrade (h : G) :
      Module.finrank ℂ (grading h) = ∑ x : X, Module.finrank ℂ (LinearMap.range (P h x)) :=
    finrank_eq_sum_finrank_range (P h) (hidem h) (horth h) (hsum h)
  have hcount (h : G) :
      (∑ x : X, if h • x = x then (1 : ℕ) else 0) = Nat.card (MulAction.fixedBy X h) := by
    letI : Fintype (MulAction.fixedBy X h) := Fintype.ofFinite _
    rw [Finset.sum_boole, Nat.card_eq_fintype_card]
    exact (Fintype.card_of_finset' (p := MulAction.fixedBy X h) _ (by simp)).symm
  have hcorner_le (h : G) (x : X) :
      Module.finrank ℂ (LinearMap.range (P h x)) ≤ (if h • x = x then 1 else 0) := by
    by_cases hx : h • x = x
    · simpa only [if_pos hx] using hline h x hx
    · simp [if_neg hx, hzero h x hx]
  have hgrade_le (h : G) : Module.finrank ℂ (grading h) ≤ Nat.card (MulAction.fixedBy X h) := by
    rw [hgrade h, ← hcount h]
    exact Finset.sum_le_sum fun x _ => hcorner_le h x
  -- Burnside's bijection counts all the fixed pairs at once.
  have hfixed_total : (∑ h : G, Nat.card (MulAction.fixedBy X h)) = Fintype.card G := by
    letI : Unique (MulAction.orbitRel.Quotient G X) :=
      Classical.choice ((MulAction.pretransitive_iff_unique_quotient_of_nonempty G X).mp
        inferInstance)
    calc
      _ = Nat.card (Σ h : G, MulAction.fixedBy X h) := Nat.card_sigma.symm
      _ = Nat.card (MulAction.orbitRel.Quotient G X × G) :=
        Nat.card_congr (MulAction.sigmaFixedByEquivOrbitsProdGroup G X)
      _ = _ := by rw [Nat.card_prod, Nat.card_unique, one_mul, Nat.card_eq_fintype_card]
  have hgrade_total : (∑ h : G, Module.finrank ℂ (grading h)) = Fintype.card G := by
    rw [← Module.finrank_directSum, (LinearEquiv.ofBijective
      (DirectSum.coeLinearMap grading) decomposition).finrank_eq, dimension]
  have hgrade_eq : Module.finrank ℂ (grading g) = Nat.card (MulAction.fixedBy X g) :=
    (Finset.sum_eq_sum_iff_of_le (fun h _ => hgrade_le h)).mp
      (hgrade_total.trans hfixed_total.symm) g (Finset.mem_univ g)
  refine ⟨hgrade_eq, ?_⟩
  have hcorner_total :
      (∑ x : X, Module.finrank ℂ (LinearMap.range (P g x))) =
        ∑ x : X, if g • x = x then (1 : ℕ) else 0 :=
    (hgrade g).symm.trans (hgrade_eq.trans (hcount g).symm)
  intro x
  exact (Finset.sum_eq_sum_iff_of_le (fun y _ => hcorner_le g y)).mp
    hcorner_total x (Finset.mem_univ x)

#print axioms grade_eq_span_singleton
#print axioms homogeneous_mul_ne_zero
#print axioms finrank_grade_eq_one
#print axioms finrank_grade_eq_card_fixedBy

end D5.S3.FiniteGroups.CosetActions.TwistedGradedCorner
