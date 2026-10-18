/- GID: D5/S3/ConceptDynamics/Coding/ResponseRealization/CentredResponseCorrection
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Coding/ResponseRealization/CentredResponseCorrection
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The numbered response lift is uncentred by a forward translation and recovered by the literal negative centring correction. -/

/- The numbered response lift is recovered from the actual uncentred lift by negative centring time. Histories and their full legal response words retain the same integer coordinates. -/
import D5.S3.ConceptDynamics.Coding.ResponseGraphs.OriginalResponseGraph

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section
namespace D5.S3.ConceptDynamics.Coding.CentredResponseCorrection
open EssentialWordRealization FiniteWindowTableCriterion StandardBeamHomeomorphisms
open OriginalResponseGraph OriginalResponseNumbering
variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
variable [TopologicalSpace E] [DiscreteTopology E]
variable (G : DirectedMultigraph V E)
variable {a b c d : ℕ} (pair : TablePair G G a b c d)

/-- Uncentre the already constructed finite response lift. Its coordinate
formula below is the actual complete future block [t,t+a+b+1]. -/
def uncentred : History G ≃ₜ CountedMatrixOverlap.Path (matrix G pair) :=
  { toFun := fun x => numberedLift G pair (translate G (a:ℤ) x)
    invFun := fun z => translate G (-(a:ℤ)) ((numberedLift G pair).symm z)
    left_inv := by
      intro x
      change translate G (-(a:ℤ)) ((numberedLift G pair).symm
        (numberedLift G pair (translate G (a:ℤ) x))) = x
      rw [(numberedLift G pair).symm_apply_apply]
      apply Subtype.ext
      funext t
      exact congrArg x.val (by omega)
    right_inv := by
      intro z
      change numberedLift G pair (translate G (a:ℤ)
        (translate G (-(a:ℤ)) ((numberedLift G pair).symm z))) = z
      calc
        _ = numberedLift G pair ((numberedLift G pair).symm z) := by
          apply congrArg (numberedLift G pair)
          apply Subtype.ext
          funext t
          exact congrArg ((numberedLift G pair).symm z).val (by omega)
        _ = z := (numberedLift G pair).apply_symm_apply z
    continuous_toFun := by
      apply (numberedLift G pair).continuous.comp
      apply Continuous.subtype_mk
      apply continuous_pi
      intro t
      exact (continuous_apply (t+(a:ℤ))).comp continuous_subtype_val
    continuous_invFun := by
      apply Continuous.subtype_mk
      apply continuous_pi
      intro t
      exact ((continuous_apply (t+(-(a:ℤ)))).comp continuous_subtype_val).comp
        (numberedLift G pair).symm.continuous }

theorem uncentred_coordinate (x : History G) (t : ℤ) :
    edgeEquiv G pair ((uncentred G pair x).val t) =
      makeEdge G pair (historyWindow G x t (a+b+1+1)) := by
  change edgeEquiv G pair ((edgeEquiv G pair).symm
    (makeEdge G pair (historyWindow G (translate G (a:ℤ) x) (t-(a:ℤ)) _))) = _
  rw [(edgeEquiv G pair).apply_symm_apply]
  congr 1
  apply legalWord_ext
  funext j
  change x.val (t-(a:ℤ)+(j.val:ℤ)+(a:ℤ)) = x.val (t+(j.val:ℤ))
  exact congrArg x.val (by omega)

/-- Literal -a correction; positive a would produce the wrong history. -/
theorem centred_eq_uncentred_negative (x : History G) :
    numberedLift G pair x = uncentred G pair (translate G (-(a:ℤ)) x) := by
  change numberedLift G pair x =
    numberedLift G pair (translate G (a:ℤ) (translate G (-(a:ℤ)) x))
  apply congrArg (numberedLift G pair)
  apply Subtype.ext
  funext t
  change x.val t = x.val (t+(a:ℤ)+(-(a:ℤ)))
  exact congrArg x.val (by omega)
end D5.S3.ConceptDynamics.Coding.CentredResponseCorrection
