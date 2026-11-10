/- GID: D5/S3/FiniteGroups/Semilinear/WeightOneChart
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/Semilinear/WeightOneChart
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Nonlinear normalization identifies the weight-one chart quotient and stabilizers. -/

import D5.S3.FiniteGroups.Semilinear.WeightedOrbits

/-! The nonzero weight-one chart retains the original semilinear action. -/

set_option autoImplicit false

namespace WeightedSemilinear

universe u
variable {F K : Type} [Field F] [Field K] [Algebra F K]
variable {J : Type u} (w : J → ℕ)

/-- The distinguished coordinate has weight one. -/
def chartWeights : Option J → ℕ := fun i => i.elim 1 w

/-- The actual nonzero distinguished-coordinate locus. -/
def Chart (_w : J → ℕ) := {A : Option J → K // A none ≠ 0}

/-- Restriction of the existing weighted action, with the same coordinate formula. -/
@[instance_reducible] def chartAction : MulAction (Group F K) (Chart (K := K) (J := J) w) where
  smul g A := ⟨act (chartWeights w) g A.val, by
    simp [act, chartWeights, A.property]⟩
  one_smul A := by
    apply Subtype.ext
    exact (weightedAction (F := F) (K := K) (chartWeights w)).one_smul A.val
  mul_smul g h A := by
    apply Subtype.ext
    exact (weightedAction (F := F) (K := K) (chartWeights w)).mul_smul g h A.val

local instance : MulAction (Group F K) (Chart (K := K) (J := J) w) := chartAction w

/-- Remove the leading scalar using the actual inverse weight powers. -/
def normalize (A : Chart (K := K) (J := J) w) : J → K :=
  fun j => (A.val none)⁻¹ ^ w j * A.val (some j)

/-- The native section has leading coordinate one, with no residual nonzero condition. -/
def chartSection (b : J → K) : Chart (K := K) (J := J) w :=
  ⟨fun i => i.elim 1 b, one_ne_zero⟩

private theorem normalize_section (b : J → K) : normalize w (chartSection w b) = b := by
  funext j
  simp [normalize, chartSection]

private theorem reconstruct (A : Chart (K := K) (J := J) w) (j : J) :
    A.val none ^ w j * normalize w A j = A.val (some j) := by
  simp [normalize, A.property]

private theorem chart_ext {A B : Chart (K := K) (J := J) w}
    (ha : A.val none = B.val none) (hb : normalize w A = normalize w B) : A = B := by
  apply Subtype.ext
  funext i
  cases i with
  | none => exact ha
  | some j => rw [← reconstruct w A j, ← reconstruct w B j, ha, hb]

/-- Normalization cancels the scalar part and retains the Galois dynamics. -/
theorem normalize_smul (g : Group F K) (A : Chart (K := K) (J := J) w) :
    normalize w (g • A) = g.right • normalize w A := by
  funext j
  change (((g.left⁻¹ : Kˣ) : K) * g.right (A.val none))⁻¹ ^ w j *
    (((g.left⁻¹ : Kˣ) : K) ^ w j * g.right (A.val (some j))) =
      g.right ((A.val none)⁻¹ ^ w j * A.val (some j))
  simp [mul_inv_rev, mul_pow, map_mul, map_pow, map_inv₀,
    mul_assoc, mul_left_comm, mul_comm]

/-- The scalar required to carry A to B over the prescribed automorphism. -/
def chartTransport (A B : Chart (K := K) (J := J) w) (σ : Gal(K/F)) : Group F K :=
  ⟨Units.mk0 (σ (A.val none) / B.val none)
    (div_ne_zero ((map_ne_zero σ).mpr A.property) B.property), σ⟩

private theorem transport_head (A B : Chart (K := K) (J := J) w) (σ : Gal(K/F)) :
    ((chartTransport w A B σ) • A).val none = B.val none := by
  change (σ (A.val none) / B.val none)⁻¹ * σ (A.val none) = B.val none
  simp [div_eq_mul_inv, A.property, B.property]

private theorem transport_eq (A B : Chart (K := K) (J := J) w) (σ : Gal(K/F))
    (h : σ • normalize w A = normalize w B) : chartTransport w A B σ • A = B := by
  apply chart_ext w (transport_head w A B σ)
  exact (normalize_smul w _ A).trans h

/-- Equality of native chart orbits is exactly equality of normalized Galois orbits. -/
theorem chart_orbit_iff (A B : Chart (K := K) (J := J) w) :
    MulAction.orbitRel (Group F K) _ A B ↔
      MulAction.orbitRel Gal(K/F) (J → K) (normalize w A) (normalize w B) := by
  constructor
  · rintro ⟨g, hg⟩
    exact ⟨g.right, (normalize_smul w g B).symm.trans (congrArg (normalize w) hg)⟩
  · rintro ⟨σ, hσ⟩
    exact ⟨chartTransport w B A σ, transport_eq w B A σ hσ⟩

/-- The actual native orbit quotients, induced by normalization and its section. -/
def chartQuotientEquiv :
    MulAction.orbitRel.Quotient (Group F K) (Chart (K := K) (J := J) w) ≃
      MulAction.orbitRel.Quotient Gal(K/F) (J → K) where
  toFun := Quotient.map (normalize w) (fun A B h => (chart_orbit_iff w A B).mp h)
  invFun := Quotient.map (chartSection w) (fun a b h => (chart_orbit_iff w _ _).mpr (by
    simpa only [normalize_section] using h))
  left_inv q := by
    induction q using Quotient.inductionOn with | _ A =>
      apply Quotient.sound
      apply (chart_orbit_iff w _ _).mpr
      rw [normalize_section]
  right_inv q := by
    induction q using Quotient.inductionOn with | _ b =>
      change Quotient.mk _ (normalize w (chartSection w b)) = _
      rw [normalize_section]

private theorem stabilizer_scalar (A : Chart (K := K) (J := J) w)
    (g : MulAction.stabilizer (Group F K) A) :
    (g.val.left : K) = g.val.right (A.val none) / A.val none := by
  have h := congrArg (fun B : Chart (K := K) (J := J) w => B.val none)
    (MulAction.mem_stabilizer_iff.mp g.property)
  change ((g.val.left⁻¹ : Kˣ) : K) * g.val.right (A.val none) = A.val none at h
  apply (eq_div_iff A.property).mpr
  calc
    (g.val.left : K) * A.val none =
        (g.val.left : K) * (((g.val.left⁻¹ : Kˣ) : K) * g.val.right (A.val none)) := by rw [h]
    _ = g.val.right (A.val none) := by simp [← mul_assoc]

/-- Projection is a group isomorphism; its inverse has scalar sigma(a)/a. -/
def chartStabilizerEquiv (A : Chart (K := K) (J := J) w) :
    MulAction.stabilizer (Group F K) A ≃*
      MulAction.stabilizer Gal(K/F) (normalize w A) where
  toFun g := ⟨g.val.right, MulAction.mem_stabilizer_iff.mpr (by
    rw [← normalize_smul w g.val A, MulAction.mem_stabilizer_iff.mp g.property])⟩
  invFun σ := ⟨chartTransport w A A σ.val,
    MulAction.mem_stabilizer_iff.mpr
      (transport_eq w A A σ.val (MulAction.mem_stabilizer_iff.mp σ.property))⟩
  left_inv g := by
    apply Subtype.ext
    apply SemidirectProduct.ext
    · apply Units.ext
      exact (stabilizer_scalar w A g).symm
    · rfl
  right_inv σ := rfl
  map_mul' g h := rfl

#print axioms chartQuotientEquiv
#print axioms chartStabilizerEquiv

end WeightedSemilinear
