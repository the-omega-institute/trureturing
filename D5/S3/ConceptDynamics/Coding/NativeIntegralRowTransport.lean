/- GID: D5/S3/ConceptDynamics/Coding/NativeIntegralRowTransport
   generality: I
   mirror-B: D5/B/S3/ConceptDynamics/Coding/NativeIntegralRowTransport
   mirror-E: none(waiver:symbolic-structural-theorems)
   anchors: []
   utility: none
   digest: Same-stage integral coefficient transport for the original two-sign row module. -/
import D5.S3.ConceptDynamics.Coding.InertGroupBlockConjugacy
import D5.S3.ConceptDynamics.Coding.ResetNumberedHistories
import D5.S3.ConceptDynamics.Coding.StandardBeamColimitCuts
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S3.ConceptDynamics.Coding.NativeIntegralRowTransport

open D5.S3.ConceptDynamics.Coding.CountedGroupOverlap
open D5.S3.ConceptDynamics.Coding.InertGroupBlockConjugacy
open D5.S3.ConceptDynamics.Coding.ResetNumberedHistories (Sign resetMatrix)
open Multiplicative
open scoped BigOperators Matrix

abbrev ExpandedRow (q : ℕ) := Fin q × Sign → ℤ
abbrev NativeRow (q : ℕ) := VertexModule Sign q

def signFlip : Sign := ofAdd true

/-- The TRUE two-coordinate Z[C2] basis map: the coefficient at absolute
sign false goes to 1 and the coefficient at absolute sign true goes to signFlip. -/
def encode {q : ℕ} (v : ExpandedRow q) : NativeRow q := fun i =>
  MonoidAlgebra.single 1 (v (i, 1)) + MonoidAlgebra.single signFlip (v (i, signFlip))

def decode {q : ℕ} (z : NativeRow q) : ExpandedRow q := fun p => (z p.1).coeff p.2

theorem encode_coeff {q : ℕ} (v : ExpandedRow q) (i : Fin q) (h : Sign) :
    (encode v i).coeff h = v (i, h) := by
  classical
  unfold encode
  rw [MonoidAlgebra.coeff_add, Finsupp.add_apply,
    MonoidAlgebra.coeff_single_apply, MonoidAlgebra.coeff_single_apply]
  have hcases : h = 1 ∨ h = signFlip := by
    rcases Bool.dichotomy (toAdd h) with hb | hb
    · left
      exact congrArg (fun b : Bool => (ofAdd b : Sign)) hb
    · right
      exact congrArg (fun b : Bool => (ofAdd b : Sign)) hb
  rcases hcases with rfl | rfl
  · rw [if_pos rfl, if_neg (show signFlip ≠ (1 : Sign) from by decide)]
    exact add_zero _
  · rw [if_neg (show (1 : Sign) ≠ signFlip from by decide), if_pos rfl]
    exact zero_add _

theorem decode_encode {q : ℕ} (v : ExpandedRow q) : decode (encode v) = v := by
  funext p
  exact encode_coeff v p.1 p.2

theorem encode_decode {q : ℕ} (z : NativeRow q) : encode (decode z) = z := by
  funext i
  ext h
  exact encode_coeff (decode z) i h

def basisEquiv (q : ℕ) : ExpandedRow q ≃ₗ[ℤ] NativeRow q where
  toFun := encode
  invFun := decode
  left_inv := decode_encode
  right_inv := encode_decode
  map_add' v w := by
    funext i
    ext h
    simp [encode_coeff, Pi.add_apply]
  map_smul' c v := by
    funext i
    ext h
    change (encode (c • v) i).coeff h = (c • encode v i).coeff h
    rw [encode_coeff, MonoidAlgebra.coeff_smul_apply, encode_coeff]
    rfl

/-- Original expanded integer adjacency, in the exact (i,h) coordinates.
It counts every numbered edge with label h^{-1}t, with no quotient. -/
def expansionMatrix {q : ℕ} (M : GroupMat Sign q q) :
    Matrix (Fin q × Sign) (Fin q × Sign) ℤ := fun p t =>
  ((M p.1 t.1).coeff (p.2⁻¹ * t.2) : ℤ)

/-- Original ROW transition v -> vB, never a transpose convention. -/
def rowTransition {q : ℕ} (M : GroupMat Sign q q) : Module.End ℤ (ExpandedRow q) :=
  (expansionMatrix M).toLinearMapRight'

def rowVertex {q : ℕ} (i : Fin q) (h : Sign) : ExpandedRow q := Pi.single (i, h) 1

lemma decode_vertex {q : ℕ} (i : Fin q) (h : Sign) :
    decode (vertex i h) = rowVertex i h := by
  funext p
  rcases p with ⟨j, t⟩
  by_cases hj : j = i
  · subst j
    by_cases ht : t = h
    · subst t
      simp [decode, vertex, rowVertex]
    · simp [decode, vertex, rowVertex, ht, Ne.symm ht, Pi.single_apply,
        MonoidAlgebra.coeff_single]
  · have hne : (j, t) ≠ (i, h) := by
      intro hEq
      exact hj (congrArg Prod.fst hEq)
    simp [decode, vertex, rowVertex, Pi.single_apply, hj, hne,
      Prod.mk.injEq, Fin.ext_iff]

lemma rowTransition_vertex {q : ℕ} (M : GroupMat Sign q q)
    (i j : Fin q) (h t : Sign) :
    (rowTransition M (rowVertex i h)) (j, t) =
      ((M i j).coeff (h⁻¹ * t) : ℤ) := by
  change ((Pi.single (i, h) 1) ᵥ* expansionMatrix M) (j, t) = _
  rw [Matrix.single_vecMul]
  simp [expansionMatrix, Matrix.row]

/-- Reuses actual_expansion_adjacency on each native basis vertex, then the
native vertex basis extends the equality to ALL integral rows. -/
theorem transport_transition {q : ℕ} (M : GroupMat Sign q q) (v : ExpandedRow q) :
    basisEquiv q (rowTransition M v) = transition M (basisEquiv q v) := by
  have hmaps : ((basisEquiv q).toLinearMap.comp (rowTransition M)).comp
      (basisEquiv q).symm.toLinearMap = transition M := by
    apply (vertexBasis (H := Sign) (n := q)).ext
    intro p
    rcases p with ⟨i, h⟩
    simp only [vertexBasis, Pi.basis_apply, MonoidAlgebra.basis_apply]
    change encode (rowTransition M (decode (vertex i h))) = transition M (vertex i h)
    rw [decode_vertex]
    funext j
    ext t
    rw [encode_coeff, rowTransition_vertex]
    exact (actual_expansion_adjacency M i j h t).symm
  have h := LinearMap.congr_fun hmaps (basisEquiv q v)
  simpa using h

theorem transport_power {q : ℕ} (M : GroupMat Sign q q) (k : ℕ) (v : ExpandedRow q) :
    basisEquiv q (((rowTransition M)^k) v) = ((transition M)^k) (basisEquiv q v) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply, transport_transition, ih,
      pow_succ', Module.End.mul_apply]

lemma inverse_transport_power {q : ℕ} (M : GroupMat Sign q q)
    (k : ℕ) (z : NativeRow q) :
    (basisEquiv q).symm (((transition M)^k) z) =
      ((rowTransition M)^k) ((basisEquiv q).symm z) := by
  apply (basisEquiv q).injective
  rw [(basisEquiv q).apply_symm_apply, transport_power,
    (basisEquiv q).apply_symm_apply]

abbrev ExpandedLimit {q : ℕ} (M : GroupMat Sign q q) := StationaryModule (rowTransition M)

def toNativeLimit {q : ℕ} (M : GroupMat Sign q q) :
    ExpandedLimit M →ₗ[ℤ] DimensionGroup M :=
  Module.DirectLimit.map (fun _ : ℕ => (basisEquiv q).toLinearMap) (by
    intro i j hij
    apply LinearMap.ext
    intro v
    change basisEquiv q (((rowTransition M)^(j - i)) v) =
      ((transition M)^(j - i)) (basisEquiv q v)
    exact transport_power M (j - i) v)

def fromNativeLimit {q : ℕ} (M : GroupMat Sign q q) :
    DimensionGroup M →ₗ[ℤ] ExpandedLimit M :=
  Module.DirectLimit.map (fun _ : ℕ => (basisEquiv q).symm.toLinearMap) (by
    intro i j hij
    apply LinearMap.ext
    intro z
    change (basisEquiv q).symm (((transition M)^(j - i)) z) =
      ((rowTransition M)^(j - i)) ((basisEquiv q).symm z)
    exact inverse_transport_power M (j - i) z)

/-- Exact SAME-STAGE transport on every original stationary stage and every
integral row. This is an algebraic coordinate isomorphism, not a beam action. -/
theorem toNativeLimit_stage {q : ℕ} (M : GroupMat Sign q q) (n : ℕ) (v : ExpandedRow q) :
    toNativeLimit M
      (Module.DirectLimit.of ℤ ℕ (fun _ : ℕ => ExpandedRow q)
        (stationaryTransition (rowTransition M)) n v) =
      Module.DirectLimit.of ℤ ℕ (fun _ : ℕ => NativeRow q)
        (stationaryTransition (transition M)) n (basisEquiv q v) := by
  change Module.DirectLimit.map (fun _ : ℕ => (basisEquiv q).toLinearMap) _
      (Module.DirectLimit.of ℤ ℕ (fun _ : ℕ => ExpandedRow q)
        (stationaryTransition (rowTransition M)) n v) = _
  rw [Module.DirectLimit.map_apply_of]
  rfl

theorem fromNativeLimit_stage {q : ℕ} (M : GroupMat Sign q q) (n : ℕ) (z : NativeRow q) :
    fromNativeLimit M
      (Module.DirectLimit.of ℤ ℕ (fun _ : ℕ => NativeRow q)
        (stationaryTransition (transition M)) n z) =
      Module.DirectLimit.of ℤ ℕ (fun _ : ℕ => ExpandedRow q)
        (stationaryTransition (rowTransition M)) n ((basisEquiv q).symm z) := by
  change Module.DirectLimit.map (fun _ : ℕ => (basisEquiv q).symm.toLinearMap) _
      (Module.DirectLimit.of ℤ ℕ (fun _ : ℕ => NativeRow q)
        (stationaryTransition (transition M)) n z) = _
  rw [Module.DirectLimit.map_apply_of]
  rfl

lemma limits_left_inverse {q : ℕ} (M : GroupMat Sign q q) :
    (fromNativeLimit M).comp (toNativeLimit M) = LinearMap.id := by
  apply Module.DirectLimit.hom_ext
  intro n
  apply LinearMap.ext
  intro v
  change fromNativeLimit M (toNativeLimit M
    (Module.DirectLimit.of ℤ ℕ (fun _ : ℕ => ExpandedRow q)
      (stationaryTransition (rowTransition M)) n v)) =
    Module.DirectLimit.of ℤ ℕ (fun _ : ℕ => ExpandedRow q)
      (stationaryTransition (rowTransition M)) n v
  rw [toNativeLimit_stage, fromNativeLimit_stage]
  simp

lemma limits_right_inverse {q : ℕ} (M : GroupMat Sign q q) :
    (toNativeLimit M).comp (fromNativeLimit M) = LinearMap.id := by
  apply Module.DirectLimit.hom_ext
  intro n
  apply LinearMap.ext
  intro z
  change toNativeLimit M (fromNativeLimit M
    (Module.DirectLimit.of ℤ ℕ (fun _ : ℕ => NativeRow q)
      (stationaryTransition (transition M)) n z)) =
    Module.DirectLimit.of ℤ ℕ (fun _ : ℕ => NativeRow q)
      (stationaryTransition (transition M)) n z
  rw [fromNativeLimit_stage, toNativeLimit_stage]
  simp

def limitEquiv {q : ℕ} (M : GroupMat Sign q q) : ExpandedLimit M ≃ₗ[ℤ] DimensionGroup M where
  toFun := toNativeLimit M
  invFun := fromNativeLimit M
  map_add' := (toNativeLimit M).map_add
  map_smul' := (toNativeLimit M).map_smul
  left_inv x := LinearMap.congr_fun (limits_left_inverse M) x
  right_inv z := LinearMap.congr_fun (limits_right_inverse M) z

end D5.S3.ConceptDynamics.Coding.NativeIntegralRowTransport
