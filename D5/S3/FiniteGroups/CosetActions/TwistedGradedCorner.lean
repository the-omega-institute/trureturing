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

include twisted_assoc in
private theorem mem_span_singleton_of_inverse_products {g : K} {a b c p : B} {t u : ℂ}
    (ha : a ∈ grade g) (hb : b ∈ grade g⁻¹) (hc : c ∈ grade g)
    (hab : μ a b = t • p) (hbc : μ b c = u • p) (ht₀ : t ≠ 0)
    (hpc : μ p c = c) (hap : μ a p = a) : c ∈ Submodule.span ℂ {a} := by
  have h := twisted_assoc ha hb hc
  rw [hab, map_smul, LinearMap.smul_apply, hpc, hbc, map_smul, hap, smul_smul] at h
  have hs : (↑(α g g⁻¹ g) : ℂ) * t ≠ 0 := mul_ne_zero (Units.ne_zero _) ht₀
  have hsmul : ((↑(α g g⁻¹ g) : ℂ) * t) • c ∈ Submodule.span ℂ {a} :=
    Submodule.mem_span_singleton.mpr ⟨u, h.symm⟩
  exact (Submodule.smul_mem_iff _ hs).mp hsmul

include mul_mem unit_grade pairing twisted_assoc left_unit right_unit in
/-- Any nonzero homogeneous vector spans its grade. -/
theorem grade_eq_span_singleton {g : K} {a : B} (ha : a ∈ grade g) (ha₀ : a ≠ 0) :
    grade g = Submodule.span ℂ {a} := by
  obtain ⟨b, hb, t, ht₀, hab⟩ := exists_inverse_product mul_mem unit_grade pairing ha ha₀
  apply le_antisymm _ ((Submodule.span_singleton_le_iff_mem _ _).mpr ha)
  intro c hc
  have hbc_mem : μ b c ∈ grade 1 := by simpa only [inv_mul_cancel] using mul_mem hb hc
  obtain ⟨u, hbc⟩ := Submodule.mem_span_singleton.mp (unit_grade ▸ hbc_mem)
  exact mem_span_singleton_of_inverse_products (grade := grade) (α := α) twisted_assoc
    ha hb hc hab hbc.symm ht₀ (left_unit c) (right_unit a)

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

section NeutralProjection

variable (mul_mem : ∀ {g h : K} {x y : B},
  x ∈ grade g → y ∈ grade h → μ x y ∈ grade (g * h))
variable (pairing : ∀ {g : K} {x : B}, x ∈ grade g → x ≠ 0 →
  ∃ y ∈ grade g⁻¹, μ x y ≠ 0)
variable (twisted_assoc : ∀ {g h k : K} {x y z : B},
  x ∈ grade g → y ∈ grade h → z ∈ grade k →
    (α g h k : ℂ) • μ (μ x y) z = μ x (μ y z))
variable (normalized : ∀ g h k : K, g = 1 ∨ h = 1 ∨ k = 1 → α g h k = 1)

variable (μ) in
/-- Left multiplication by a neutral element, restricted to a homogeneous degree. -/
def neutralProjection {p : B} (hp : p ∈ grade 1) (g : K) : grade g →ₗ[ℂ] grade g :=
  ((μ p).comp (grade g).subtype).codRestrict (grade g) fun b => by
    simpa only [LinearMap.comp_apply, Submodule.subtype_apply, one_mul] using mul_mem hp b.property

include twisted_assoc normalized in
private theorem neutral_mul_assoc {g h : K} {p a b : B}
    (hp : p ∈ grade 1) (ha : a ∈ grade g) (hb : b ∈ grade h) :
    μ (μ p a) b = μ p (μ a b) := by
  simpa only [normalized 1 g h (Or.inl rfl), Units.val_one, one_smul] using twisted_assoc hp ha hb

include pairing twisted_assoc normalized in
/-- A neutral idempotent with a one-dimensional neutral range has at most a line
in each homogeneous degree, provided it commutes with homogeneous vectors. -/
theorem finrank_neutralProjection_range_le_one {p : B} (hp : p ∈ grade 1)
    (idem : μ p p = p)
    (neutral_line : ∀ {b : B}, b ∈ grade 1 → μ p b ∈ Submodule.span ℂ {p})
    (commute : ∀ {g : K} {b : B}, b ∈ grade g → μ p b = μ b p)
    (g : K) : Module.finrank ℂ (LinearMap.range (neutralProjection μ mul_mem hp g)) ≤ 1 := by
  have fixed {h : K} (v : grade h) : μ p (neutralProjection μ mul_mem hp h v : B) =
      (neutralProjection μ mul_mem hp h v : B) := by
    change μ p (μ p (v : B)) = μ p (v : B)
    rw [← neutral_mul_assoc twisted_assoc normalized hp hp v.property, idem]
  have fixed_of_mem_range {h : K} {v : grade h}
      (hv : v ∈ LinearMap.range (neutralProjection μ mul_mem hp h)) : μ p (v : B) = v := by
    obtain ⟨w, rfl⟩ := LinearMap.mem_range.mp hv
    exact fixed w
  have mul_mem_line {h k : K} {u v : B} (hu : u ∈ grade h) (hv : v ∈ grade k)
      (hpu : μ p u = u) (hdeg : h * k = 1) : μ u v ∈ Submodule.span ℂ {p} := by
    have hmem : μ u v ∈ grade 1 := hdeg ▸ mul_mem hu hv
    simpa only [← neutral_mul_assoc twisted_assoc normalized hp hu hv, hpu] using neutral_line hmem
  let P := neutralProjection μ mul_mem hp g
  change Module.finrank ℂ (LinearMap.range P) ≤ 1
  by_cases hbot : LinearMap.range P = ⊥
  · rw [hbot, finrank_bot]
    exact Nat.zero_le _
  obtain ⟨a, ha, ha₀⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
  have hpa := fixed_of_mem_range ha
  have hap : μ (a : B) p = a := (commute a.property).symm.trans hpa
  obtain ⟨y, hy, hay⟩ := pairing a.property (fun h => ha₀ (Subtype.ext h))
  let b : grade g⁻¹ := neutralProjection μ mul_mem hp g⁻¹ ⟨y, hy⟩
  have hab : μ (a : B) (b : B) = μ (a : B) y := by
    change μ (a : B) (μ p y) = μ (a : B) y
    simpa only [normalized g 1 g⁻¹ (Or.inr (Or.inl rfl)), Units.val_one, one_smul, hap] using
      (twisted_assoc a.property hp hy).symm
  obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp
    (mul_mem_line a.property b.property hpa (mul_inv_cancel g))
  have ht₀ : t ≠ 0 := fun h => hay (by rw [← hab, ← ht, h, zero_smul])
  have hrange : LinearMap.range P = Submodule.span ℂ {a} := by
    apply le_antisymm _ ((Submodule.span_singleton_le_iff_mem _ _).mpr ha)
    intro c hc
    obtain ⟨u, hu⟩ := Submodule.mem_span_singleton.mp
      (mul_mem_line b.property c.property (fixed ⟨y, hy⟩) (inv_mul_cancel g))
    obtain ⟨s, hs⟩ := Submodule.mem_span_singleton.mp
      (mem_span_singleton_of_inverse_products (grade := grade) (α := α) twisted_assoc
        a.property b.property c.property ht.symm hu.symm ht₀ (fixed_of_mem_range hc) hap)
    exact Submodule.mem_span_singleton.mpr ⟨s, Subtype.ext hs⟩
  rw [hrange, finrank_span_singleton ha₀]

end NeutralProjection

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

section NeutralCoordinates

variable {X : Type*} [Fintype K] [DecidableEq K] [Fintype X] [DecidableEq X] [Nonempty X]
    [MulAction K X] [MulAction.IsPretransitive K X]

/-- For neutral coordinates of a twisted graded algebra, the occupied corners
of each degree are exactly the coordinates fixed by that degree. -/
theorem finrank_grade_eq_card_fixedBy_of_multiplication
    (decomposition : DirectSum.IsInternal grade)
    (dimension : Module.finrank ℂ B = Fintype.card K)
    (mul_mem : ∀ {g h : K} {a b : B}, a ∈ grade g → b ∈ grade h → μ a b ∈ grade (g * h))
    (pairing : ∀ {g : K} {a : B}, a ∈ grade g → a ≠ 0 → ∃ b ∈ grade g⁻¹, μ a b ≠ 0)
    (twisted_assoc : ∀ {g h k : K} {a b c : B}, a ∈ grade g → b ∈ grade h → c ∈ grade k →
      (α g h k : ℂ) • μ (μ a b) c = μ a (μ b c))
    (normalized : ∀ g h k : K, g = 1 ∨ h = 1 ∨ k = 1 → α g h k = 1)
    (left_unit : ∀ b : B, μ e b = b)
    (p : X → B) (neutral_mem : ∀ x, p x ∈ grade 1)
    (orthogonal : ∀ x y, x ≠ y → μ (p x) (p y) = 0)
    (sum_eq_unit : (∑ x : X, p x) = e)
    (neutral_line : ∀ (x : X) {b : B}, b ∈ grade 1 → μ (p x) b ∈ Submodule.span ℂ {p x})
    (commute : ∀ (x : X) {g : K} {b : B}, b ∈ grade g → μ (p x) b = μ b (p x))
    (braid : ∀ (x : X) {g : K} {b : B}, b ∈ grade g → μ b (p x) = μ (p (g • x)) b)
    (g : K) :
    Module.finrank ℂ (grade g) = Nat.card (MulAction.fixedBy X g) ∧
      ∀ x : X, Module.finrank ℂ (LinearMap.range (neutralProjection μ mul_mem (neutral_mem x) g)) =
        (if g • x = x then 1 else 0) := by
  let P (h : K) (x : X) := neutralProjection μ mul_mem (neutral_mem x) h
  have sum_mul (b : B) : (∑ x : X, μ (p x) b) = b := by
    simpa only [map_sum, LinearMap.sum_apply, left_unit] using
      congrArg (fun a : B => μ a b) sum_eq_unit
  have idem (x : X) : μ (p x) (p x) = p x := by
    calc
      μ (p x) (p x) = ∑ y : X, μ (p y) (p x) :=
        (Finset.sum_eq_single_of_mem x (Finset.mem_univ x) (fun y _ hy => orthogonal y x hy)).symm
      _ = p x := sum_mul (p x)
  apply finrank_grade_eq_card_fixedBy grade decomposition dimension P _ _ _ _ g
  · intro h x y hxy b
    apply Subtype.ext
    change μ (p x) (μ (p y) (b : B)) = 0
    rw [← neutral_mul_assoc twisted_assoc normalized (neutral_mem x) (neutral_mem y) b.property,
      orthogonal x y hxy, map_zero, LinearMap.zero_apply]
  · intro h b
    apply Subtype.ext
    change (grade h).subtype (∑ x : X, P h x b) = (b : B)
    rw [map_sum]
    exact sum_mul b
  · intro h x b
    exact Subtype.ext ((commute x b.property).trans (braid x b.property))
  · intro h x _
    exact finrank_neutralProjection_range_le_one (grade := grade) (α := α) mul_mem pairing
      twisted_assoc normalized (neutral_mem x) (idem x) (neutral_line x) (commute x) h

end NeutralCoordinates

#print axioms grade_eq_span_singleton
#print axioms homogeneous_mul_ne_zero
#print axioms finrank_grade_eq_one
#print axioms finrank_grade_eq_card_fixedBy
#print axioms finrank_neutralProjection_range_le_one
#print axioms finrank_grade_eq_card_fixedBy_of_multiplication

end D5.S3.FiniteGroups.CosetActions.TwistedGradedCorner
