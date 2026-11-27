/- GID: D5/S3/FiniteGroups/TwistedFixedCosetSections
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/TwistedFixedCosetSections
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Evaluation and transport identify degree-g sections with scalar functions on fixed left cosets. -/

import D5.S3.FiniteGroups.FixedCosetBranching
import Mathlib.Algebra.Group.TypeTags.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Tactic.Abel
import OmegaBuild.Commands

/-!
Davydov–Simmons (arXiv:1603.04650), Theorem 2.11 and equations (14), (15),
(22), and (25). In the induced object for a subgroup algebra, the value at
`x` in degree `g` is in the line of degree `x⁻¹ * g * x` when that
degree belongs to the subgroup. Otherwise the fiber is zero, so a section
is fully represented by its scalar values on `ConjugatingElements`.
This construction concerns the graded vector space of the induced object.
Identifying a VOA category with the relevant Drinfeld center is a separate
input to a VOA application.
-/

compile_only_with_mathlib

set_option autoImplicit false

namespace D5.S3.FiniteGroups.TwistedFixedCosetSections

open FixedCosetBranching

variable {G : Type*} [Group G] {𝕜 : Type*} [Field 𝕜]
variable {K : Subgroup G} {g : G}

/-- Right translation within the lifts of a fixed left coset. -/
def rightMul (x : ConjugatingElements K g) (h : K) : ConjugatingElements K g :=
  ⟨x.val * h.val, by
    simpa only [mul_inv_rev, mul_assoc] using
      K.mul_mem (K.mul_mem (K.inv_mem h.property) x.property) h.property⟩

private theorem toFixedCoset_rightMul (x : ConjugatingElements K g) (h : K) :
    toFixedCoset K g (rightMul x h) = toFixedCoset K g x :=
  Subtype.ext (QuotientGroup.mk_mul_of_mem x.val h.property)

/-- Transport on the right translation groupoid of the supported lifts.
The arrow from `x` to `xh` multiplies the coefficient in the source graded line by
`scalar x h`, in the chosen bases of the source and target lines. -/
structure Transport (𝕜 : Type*) [Field 𝕜] (K : Subgroup G) (g : G) where
  scalar : ConjugatingElements K g → K → 𝕜ˣ
  one : ∀ x, scalar x 1 = 1
  comp : ∀ x h j, scalar x (h * j) = scalar (rightMul x h) j * scalar x h

/-- In scalar coordinates, degree-`g` sections are the functions covariant under transport. -/
def degreeSections (T : Transport 𝕜 K g) : Submodule 𝕜 (ConjugatingElements K g → 𝕜) where
  carrier := {f | ∀ x h, f (rightMul x h) = (T.scalar x h : 𝕜) * f x}
  zero_mem' := by
    intro x h
    exact (mul_zero (T.scalar x h : 𝕜)).symm
  add_mem' {f f'} hf hf' := by
    intro x h
    change f (rightMul x h) + f' (rightMul x h) = (T.scalar x h : 𝕜) * (f x + f' x)
    rw [hf x h, hf' x h, mul_add]
  smul_mem' c {f} hf := by
    intro x h
    change c * f (rightMul x h) = (T.scalar x h : 𝕜) * (c * f x)
    rw [hf x h, mul_left_comm c]

private noncomputable def representative (q : FixedCosets K g) :
    {x : ConjugatingElements K g // toFixedCoset K g x = q} :=
  (fixedCosetFiberEquiv K g q q.val.out (QuotientGroup.out_eq' q.val)).symm 1

private noncomputable def fiberCoordinate (x : ConjugatingElements K g) : K :=
  let q := toFixedCoset K g x
  let r := representative q
  fixedCosetFiberEquiv K g q r.val.val (congrArg Subtype.val r.property) ⟨x, rfl⟩

private theorem fiberCoordinate_val (x : ConjugatingElements K g) :
    (fiberCoordinate x : G) = (representative (toFixedCoset K g x)).val.val⁻¹ * x.val := rfl

private theorem rightMul_coordinate (x : ConjugatingElements K g) :
    rightMul (representative (toFixedCoset K g x)).val (fiberCoordinate x) = x := by
  apply Subtype.ext
  change (representative (toFixedCoset K g x)).val.val * (fiberCoordinate x : G) = x.val
  rw [fiberCoordinate_val, mul_inv_cancel_left]

private theorem coordinate_rightMul (x : ConjugatingElements K g) (h : K) :
    fiberCoordinate (rightMul x h) = fiberCoordinate x * h := by
  apply Subtype.ext
  rw [Subgroup.coe_mul, fiberCoordinate_val (rightMul x h), fiberCoordinate_val x,
    toFixedCoset_rightMul x h]
  exact (mul_assoc _ _ _).symm

private theorem coordinate_representative (q : FixedCosets K g) :
    fiberCoordinate (representative q).val = 1 := by
  apply Subtype.ext
  change (fiberCoordinate (representative q).val : G) = (1 : G)
  rw [fiberCoordinate_val, (representative q).property, inv_mul_cancel]

/-- Evaluation at one representative per fixed coset. The inverse extends each
representative value along the unique right translation to the point of evaluation. -/
noncomputable def evalEquiv (T : Transport 𝕜 K g) :
    degreeSections T ≃ₗ[𝕜] (FixedCosets K g → 𝕜) where
  toFun f q := f.val (representative q).val
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun a :=
    ⟨fun x => (T.scalar (representative (toFixedCoset K g x)).val (fiberCoordinate x) : 𝕜) *
      a (toFixedCoset K g x), by
      intro x h
      dsimp only
      rw [coordinate_rightMul, toFixedCoset_rightMul, T.comp, Units.val_mul, rightMul_coordinate,
        mul_assoc]⟩
  left_inv f := by
    apply Subtype.ext
    funext x
    have hcov : ∀ y h, f.val (rightMul y h) = (T.scalar y h : 𝕜) * f.val y :=
      f.property
    have hx := hcov (representative (toFixedCoset K g x)).val (fiberCoordinate x)
    rw [rightMul_coordinate] at hx
    exact hx.symm
  right_inv a := by
    funext q
    change (T.scalar (representative (toFixedCoset K g (representative q).val)).val
      (fiberCoordinate (representative q).val) : 𝕜) *
      a (toFixedCoset K g (representative q).val) = a q
    rw [coordinate_representative, (representative q).property, T.one]
    exact one_mul _

/-- The degree-`g` dimension is the number of fixed cosets when there are finitely many. -/
theorem finrank_degreeSections (T : Transport 𝕜 K g) [Finite (FixedCosets K g)] :
    Module.finrank 𝕜 (degreeSections T) = Nat.card (FixedCosets K g) := by
  letI := Fintype.ofFinite (FixedCosets K g)
  rw [(evalEquiv T).finrank_eq, Module.finrank_pi, Nat.card_eq_fintype_card]

/-- A nonzero degree-`g` section exists exactly when there is a fixed coset. -/
theorem nontrivial_degreeSections_iff (T : Transport 𝕜 K g) :
    Nontrivial (degreeSections T) ↔ Nonempty (FixedCosets K g) := by
  rw [(evalEquiv T).toEquiv.nontrivial_congr]
  constructor
  · intro h
    obtain ⟨a, b, hab⟩ := h.exists_pair_ne
    by_contra hq
    exact hab (funext fun q => (hq ⟨q⟩).elim)
  · rintro ⟨q⟩
    exact ⟨⟨fun _ => 0, fun _ => 1, fun h => zero_ne_one (congrFun h q)⟩⟩

/-- If `g ∈ K`, the identity coset supports a section nonzero at every one of its lifts. -/
theorem exists_section_identity_support (T : Transport 𝕜 K g) (hg : g ∈ K) :
    ∃ f : degreeSections T, ∀ x : ConjugatingElements K g,
      f.val x ≠ 0 ↔ toFixedCoset K g x = toFixedCoset K g ⟨1, by simpa using hg⟩ := by
  classical
  let q : FixedCosets K g := toFixedCoset K g ⟨1, by simpa using hg⟩
  refine ⟨(evalEquiv T).symm (fun p => if p = q then 1 else 0), ?_⟩
  intro x
  change (T.scalar (representative (toFixedCoset K g x)).val (fiberCoordinate x) : 𝕜) *
    (if toFixedCoset K g x = q then 1 else 0) ≠ 0 ↔ toFixedCoset K g x = q
  by_cases hx : toFixedCoset K g x = q
  · simp [hx, Units.ne_zero]
  · simp [hx]

/-- The mixed twist `α(a,b|u)` in Davydov–Simmons equation (6). -/
def mixedTwist (ω : G → G → G → 𝕜ˣ) (a b u : G) : 𝕜ˣ :=
  (ω a b u)⁻¹ * ω a (b * u * b⁻¹) b * (ω (a * (b * u * b⁻¹) * a⁻¹) a b)⁻¹

private theorem mixedTwist_comp (ω : G → G → G → 𝕜ˣ)
    (cocycle : ∀ a b c d, ω b c d * ω a (b * c) d * ω a b c =
      ω (a * b) c d * ω a b (c * d)) (a b c u : G) :
    mixedTwist ω a (b * c) u * mixedTwist ω b c u =
      mixedTwist ω (a * b) c u * mixedTwist ω a b (c * u * c⁻¹) := by
  let v := c * u * c⁻¹
  let w := b * v * b⁻¹
  let z := a * w * a⁻¹
  have hv : v * c = c * u := by simp [v, mul_assoc]
  have hw : w * b = b * v := by simp [w, mul_assoc]
  have hz : z * a = a * w := by simp [z, mul_assoc]
  have hbc : (b * c) * u * (b * c)⁻¹ = w := by simp [w, v, mul_inv_rev, mul_assoc]
  have hab : (a * b) * v * (a * b)⁻¹ = z := by simp [z, w, mul_inv_rev, mul_assoc]
  let A : G → G → G → Additive (𝕜ˣ) := fun a b c => Additive.ofMul (ω a b c)
  let δ : G → G → G → G → Additive (𝕜ˣ) := fun a b c d =>
    A b c d + A a (b * c) d + A a b c - (A (a * b) c d + A a b (c * d))
  have hδ (a b c d : G) : δ a b c d = 0 :=
    sub_eq_zero.mpr (congrArg Additive.ofMul (cocycle a b c d))
  apply Additive.ofMul.injective
  apply sub_eq_zero.mp
  change (-A a (b * c) u + A a ((b * c) * u * (b * c)⁻¹) (b * c) +
    -A (a * ((b * c) * u * (b * c)⁻¹) * a⁻¹) a (b * c) +
    (-A b c u + A b v c + -A w b c)) -
    (-A (a * b) c u + A (a * b) v c + -A ((a * b) * v * (a * b)⁻¹) (a * b) c +
    (-A a b v + A a w b + -A z a b)) = 0
  rw [hbc, hab]
  -- The four cocycle equations move `u` through `c`, `b`, and `a` in order.
  calc
    _ = -(δ a b c u) + δ a b v c - δ a w b c + δ z a b c := by
      dsimp only [δ]
      rw [hv, hw, hz]
      abel
    _ = 0 := by simp only [hδ, neg_zero, add_zero, sub_zero]

/-- The coefficient `ε_h(u)` of the action on the basis vector of degree `u`
in Davydov–Simmons equation (22). -/
def subgroupCoefficient (γ : K → K → 𝕜ˣ) (h u : K) : 𝕜ˣ :=
  γ h u / γ (h * u * h⁻¹) h

/-- The subgroup coefficient composes by the mixed twist of the coboundary
of `γ`, with the orientation of Davydov–Simmons equations (5) and (6). -/
theorem subgroupCoefficient_comp (ω : G → G → G → 𝕜ˣ) (γ : K → K → 𝕜ˣ)
    (restricted : ∀ a b c : K, ω a b c = γ b c * γ a (b * c) / (γ (a * b) c * γ a b))
    (a b u : K) :
    mixedTwist ω a b u * subgroupCoefficient γ a (b * u * b⁻¹) *
      subgroupCoefficient γ b u = subgroupCoefficient γ (a * b) u := by
  let v := b * u * b⁻¹
  let w := a * v * a⁻¹
  have hv : v * b = b * u := by simp [v, mul_assoc]
  have hw : w * a = a * v := by simp [w, mul_assoc]
  have hab : (a * b) * u * (a * b)⁻¹ = w := by simp [w, v, mul_inv_rev, mul_assoc]
  let A : K → K → K → Additive (𝕜ˣ) := fun p q r => Additive.ofMul (ω p q r)
  let B : K → K → Additive (𝕜ˣ) := fun p q => Additive.ofMul (γ p q)
  let δ : K → K → K → Additive (𝕜ˣ) := fun p q r =>
    B q r + B p (q * r) - (B (p * q) r + B p q)
  have hδ (p q r : K) : δ p q r - A p q r = 0 :=
    sub_eq_zero.mpr (congrArg Additive.ofMul (restricted p q r)).symm
  apply Additive.ofMul.injective
  apply sub_eq_zero.mp
  change ((-A a b u + A a v b + -A w a b) + (B a v - B w a) + (B b u - B v b)) -
    (B (a * b) u - B ((a * b) * u * (a * b)⁻¹) (a * b)) = 0
  rw [hab]
  calc
    _ = (δ a b u - A a b u) - (δ a v b - A a v b) + (δ w a b - A w a b) := by
      dsimp only [δ]
      rw [← hv, ← hw]
      abel
    _ = 0 := by simp only [hδ, sub_zero, add_zero]

/-- Right-translation transport in Davydov–Simmons equation (15), using the
subgroup action coefficient from (22) when `ω|K³ = δγ`. -/
def transportOfCochain (ω : G → G → G → 𝕜ˣ) (γ : K → K → 𝕜ˣ)
    (normalized : ∀ a b c, (a = 1 ∨ b = 1 ∨ c = 1) → ω a b c = 1)
    (cocycle : ∀ a b c d, ω b c d * ω a (b * c) d * ω a b c =
      ω (a * b) c d * ω a b (c * d))
    (cochainNormalized : ∀ a b : K, (a = 1 ∨ b = 1) → γ a b = 1)
    (restricted : ∀ a b c : K, ω a b c = γ b c * γ a (b * c) / (γ (a * b) c * γ a b)) :
    Transport 𝕜 K g where
  scalar x h := mixedTwist ω h.val⁻¹ x.val⁻¹ g *
    subgroupCoefficient γ h⁻¹ ⟨x.val⁻¹ * g * x.val, x.property⟩
  one x := by
    have hfirst (a b : G) : ω 1 a b = 1 := normalized 1 a b (Or.inl rfl)
    have hsecond (a b : G) : ω a 1 b = 1 := normalized a 1 b (Or.inr (Or.inl rfl))
    have hγfirst (u : K) : γ 1 u = 1 := cochainNormalized 1 u (Or.inl rfl)
    have hγsecond (u : K) : γ u 1 = 1 := cochainNormalized u 1 (Or.inr rfl)
    change mixedTwist ω ((1 : G)⁻¹) x.val⁻¹ g *
      subgroupCoefficient γ (1 : K)⁻¹ ⟨x.val⁻¹ * g * x.val, x.property⟩ = 1
    simp only [mixedTwist, subgroupCoefficient, inv_one, hfirst, hsecond,
      hγfirst, hγsecond, one_div, one_mul]
  comp x h j := by
    let u : K := ⟨x.val⁻¹ * g * x.val, x.property⟩
    let v : K := ⟨(rightMul x h).val⁻¹ * g * (rightMul x h).val, (rightMul x h).property⟩
    have hv : v = h⁻¹ * u * h := by
      apply Subtype.ext
      simp [v, u, rightMul, mul_inv_rev, mul_assoc]
    have hcoeff := subgroupCoefficient_comp ω γ restricted j⁻¹ h⁻¹ u
    rw [inv_inv] at hcoeff
    have hcomp := mixedTwist_comp ω cocycle j.val⁻¹ h.val⁻¹ x.val⁻¹ g
    rw [inv_inv] at hcomp
    change _ = _ * mixedTwist ω (↑(j⁻¹) : G) (↑(h⁻¹) : G) (u : G) at hcomp
    change mixedTwist ω (↑(h * j) : G)⁻¹ x.val⁻¹ g * subgroupCoefficient γ (h * j)⁻¹ u =
      (mixedTwist ω j.val⁻¹ (x.val * h.val)⁻¹ g * subgroupCoefficient γ j⁻¹ v) *
        (mixedTwist ω h.val⁻¹ x.val⁻¹ g * subgroupCoefficient γ h⁻¹ u)
    simp only [Subgroup.coe_mul, mul_inv_rev, hv]
    rw [← hcoeff]
    simp only [← mul_assoc]
    rw [← hcomp]
    ac_rfl

/-- Equation (15) for the gauge in which `ω|K³ = 1` and the subgroup trivializing
cochain is `1`. The subgroup action in (22) then permutes the graded basis with
coefficient `1`. Composition follows from the mixed twist identity (8). -/
def transportOfTrivialRestriction (ω : G → G → G → 𝕜ˣ)
    (normalized : ∀ a b c, (a = 1 ∨ b = 1 ∨ c = 1) → ω a b c = 1)
    (cocycle : ∀ a b c d, ω b c d * ω a (b * c) d * ω a b c =
      ω (a * b) c d * ω a b (c * d))
    (restricted : ∀ a b c : G, a ∈ K → b ∈ K → c ∈ K → ω a b c = 1) :
    Transport 𝕜 K g where
  scalar x h := mixedTwist ω h.val⁻¹ x.val⁻¹ g
  one x := by
    have hfirst (a b : G) : ω 1 a b = 1 := normalized 1 a b (Or.inl rfl)
    have hsecond (a b : G) : ω a 1 b = 1 := normalized a 1 b (Or.inr (Or.inl rfl))
    change mixedTwist ω ((1 : G)⁻¹) x.val⁻¹ g = 1
    simp only [mixedTwist, inv_one, hfirst, hsecond, one_mul]
  comp x h j := by
    let u : G := x.val⁻¹ * g * x.val
    have hu : u ∈ K := x.property
    have hh : h.val⁻¹ ∈ K := K.inv_mem h.property
    have hj : j.val⁻¹ ∈ K := K.inv_mem j.property
    have hv : h.val⁻¹ * u * (h.val⁻¹)⁻¹ ∈ K :=
      K.mul_mem (K.mul_mem hh hu) (K.inv_mem hh)
    have hw : j.val⁻¹ * (h.val⁻¹ * u * (h.val⁻¹)⁻¹) * (j.val⁻¹)⁻¹ ∈ K :=
      K.mul_mem (K.mul_mem hj hv) (K.inv_mem hj)
    have hsub : mixedTwist ω j.val⁻¹ h.val⁻¹ u = 1 := by
      rw [mixedTwist, restricted _ _ _ hj hh hu, restricted _ _ _ hj hv hh,
        restricted _ _ _ hw hj hh]
      simp only [inv_one, one_mul]
    have hcomp := mixedTwist_comp ω cocycle j.val⁻¹ h.val⁻¹ x.val⁻¹ g
    rw [inv_inv, hsub, mul_one] at hcomp
    change mixedTwist ω ((↑(h * j) : G)⁻¹) x.val⁻¹ g =
      mixedTwist ω j.val⁻¹ ((x.val * h.val)⁻¹) g * mixedTwist ω h.val⁻¹ x.val⁻¹ g
    simpa only [Subgroup.coe_mul, mul_inv_rev] using hcomp.symm

end D5.S3.FiniteGroups.TwistedFixedCosetSections
