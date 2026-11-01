import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Geometry.Polygons.PolygonEarSlideGeometry
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Geometry.Polygons.PolygonEarSlideGeometry
open _root_.D5.S3.Geometry.Polygons.PolygonEarSlide.Carrier
open _root_.D5.S3.Geometry.Polygons.PolygonEarSlide.Actual
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

abbrev signature : Signature where
  Params := {n : ℕ // 6 ≤ n}
  State n := Sym2 (ZMod n.1) × Sym2 (ZMod n.1)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

noncomputable def actual : Realization signature :=
  realize signature (fun _ n ef => by
    letI : NeZero n.1 := ⟨by have := n.2; omega⟩
    exact Cross ef.1 ef.2) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law O := ∀ (n : ℕ) [NeZero n] (hn : 6 ≤ n)
    (e f : Sym2 (ZMod n)), AvoidTwo e → AvoidTwo f →
    (O.readout () ⟨n, hn⟩ (chordSwap e, chordSwap f) ↔
      O.readout () ⟨n, hn⟩ (e, f))

theorem actual_law : arena.Law actual := by
  intro n _ hn e f he hf
  exact cross_chordSwap_of_avoidTwo hn he hf

/-!
The actual dependent-family readout and its law retain the full source domain.
No Contract.Registration is asserted. Source reconstruction and binding,
a lawful enrolled-template readout, a rejected realization, whole-family
sensitivity, and actual observational dependence remain unproved.
-/

namespace Source

abbrev cross_symm_scope := type_of% (@_root_.D5.S3.Geometry.Polygons.PolygonEarSlide.Carrier.cross_symm)

def cross_symm : cross_symm_scope :=
  @_root_.D5.S3.Geometry.Polygons.PolygonEarSlide.Carrier.cross_symm

abbrev not_cross_self_scope := type_of% (@_root_.D5.S3.Geometry.Polygons.PolygonEarSlide.Carrier.not_cross_self)

def not_cross_self : not_cross_self_scope :=
  @_root_.D5.S3.Geometry.Polygons.PolygonEarSlide.Carrier.not_cross_self

abbrev sbtw_val_scope := type_of% (@_root_.D5.S3.Geometry.Polygons.PolygonEarSlide.Actual.sbtw_val)

def sbtw_val : sbtw_val_scope :=
  @_root_.D5.S3.Geometry.Polygons.PolygonEarSlide.Actual.sbtw_val

abbrev vertexSwap_val_scope := type_of% (@_root_.D5.S3.Geometry.Polygons.PolygonEarSlide.Actual.vertexSwap_val)

def vertexSwap_val : vertexSwap_val_scope :=
  @_root_.D5.S3.Geometry.Polygons.PolygonEarSlide.Actual.vertexSwap_val

abbrev vertexSwap_val_of_ne_two_scope := type_of% (@_root_.D5.S3.Geometry.Polygons.PolygonEarSlide.Actual.vertexSwap_val_of_ne_two)

def vertexSwap_val_of_ne_two : vertexSwap_val_of_ne_two_scope :=
  @_root_.D5.S3.Geometry.Polygons.PolygonEarSlide.Actual.vertexSwap_val_of_ne_two

abbrev sbtw_swap_of_avoid_two_scope := type_of% (@_root_.D5.S3.Geometry.Polygons.PolygonEarSlide.Actual.sbtw_swap_of_avoid_two)

def sbtw_swap_of_avoid_two : sbtw_swap_of_avoid_two_scope :=
  @_root_.D5.S3.Geometry.Polygons.PolygonEarSlide.Actual.sbtw_swap_of_avoid_two

abbrev vertexSwap_apply_one_scope := type_of% (@_root_.D5.S3.Geometry.Polygons.PolygonEarSlide.Actual.vertexSwap_apply_one)

def vertexSwap_apply_one : vertexSwap_apply_one_scope :=
  @_root_.D5.S3.Geometry.Polygons.PolygonEarSlide.Actual.vertexSwap_apply_one

abbrev vertexSwap_apply_two_scope := type_of% (@_root_.D5.S3.Geometry.Polygons.PolygonEarSlide.Actual.vertexSwap_apply_two)

def vertexSwap_apply_two : vertexSwap_apply_two_scope :=
  @_root_.D5.S3.Geometry.Polygons.PolygonEarSlide.Actual.vertexSwap_apply_two

abbrev vertexSwap_apply_apply_scope := type_of% (@_root_.D5.S3.Geometry.Polygons.PolygonEarSlide.Actual.vertexSwap_apply_apply)

def vertexSwap_apply_apply : vertexSwap_apply_apply_scope :=
  @_root_.D5.S3.Geometry.Polygons.PolygonEarSlide.Actual.vertexSwap_apply_apply

abbrev chordSwap_involutive_scope := type_of% (@_root_.D5.S3.Geometry.Polygons.PolygonEarSlide.Actual.chordSwap_involutive)

def chordSwap_involutive : chordSwap_involutive_scope :=
  @_root_.D5.S3.Geometry.Polygons.PolygonEarSlide.Actual.chordSwap_involutive

abbrev chordSwap_mk_scope := type_of% (@_root_.D5.S3.Geometry.Polygons.PolygonEarSlide.Actual.chordSwap_mk)

def chordSwap_mk : chordSwap_mk_scope :=
  @_root_.D5.S3.Geometry.Polygons.PolygonEarSlide.Actual.chordSwap_mk

abbrev ear_zero_scope := type_of% (@_root_.D5.S3.Geometry.Polygons.PolygonEarSlide.Actual.ear_zero)

def ear_zero : ear_zero_scope :=
  @_root_.D5.S3.Geometry.Polygons.PolygonEarSlide.Actual.ear_zero

abbrev ear_one_scope := type_of% (@_root_.D5.S3.Geometry.Polygons.PolygonEarSlide.Actual.ear_one)

def ear_one : ear_one_scope :=
  @_root_.D5.S3.Geometry.Polygons.PolygonEarSlide.Actual.ear_one

abbrev ear_two_scope := type_of% (@_root_.D5.S3.Geometry.Polygons.PolygonEarSlide.Actual.ear_two)

def ear_two : ear_two_scope :=
  @_root_.D5.S3.Geometry.Polygons.PolygonEarSlide.Actual.ear_two

abbrev ear_three_scope := type_of% (@_root_.D5.S3.Geometry.Polygons.PolygonEarSlide.Actual.ear_three)

def ear_three : ear_three_scope :=
  @_root_.D5.S3.Geometry.Polygons.PolygonEarSlide.Actual.ear_three

abbrev val_neg_one_of_ge_scope := type_of% (@_root_.D5.S3.Geometry.Polygons.PolygonEarSlide.Actual.val_neg_one_of_ge)

def val_neg_one_of_ge : val_neg_one_of_ge_scope :=
  @_root_.D5.S3.Geometry.Polygons.PolygonEarSlide.Actual.val_neg_one_of_ge

abbrev sbtw_const_scope := type_of% (@_root_.D5.S3.Geometry.Polygons.PolygonEarSlide.Actual.sbtw_const)

def sbtw_const : sbtw_const_scope :=
  @_root_.D5.S3.Geometry.Polygons.PolygonEarSlide.Actual.sbtw_const

abbrev local_crossings_scope := type_of% (@_root_.D5.S3.Geometry.Polygons.PolygonEarSlide.Actual.local_crossings)

def local_crossings : local_crossings_scope :=
  @_root_.D5.S3.Geometry.Polygons.PolygonEarSlide.Actual.local_crossings

abbrev avoidTwo_mk_iff_scope := type_of% (@_root_.D5.S3.Geometry.Polygons.PolygonEarSlide.Actual.avoidTwo_mk_iff)

def avoidTwo_mk_iff : avoidTwo_mk_iff_scope :=
  @_root_.D5.S3.Geometry.Polygons.PolygonEarSlide.Actual.avoidTwo_mk_iff

abbrev cross_chordSwap_of_avoidTwo_scope := type_of% (@_root_.D5.S3.Geometry.Polygons.PolygonEarSlide.Actual.cross_chordSwap_of_avoidTwo)

def cross_chordSwap_of_avoidTwo : cross_chordSwap_of_avoidTwo_scope :=
  @_root_.D5.S3.Geometry.Polygons.PolygonEarSlide.Actual.cross_chordSwap_of_avoidTwo

abbrev cross_incident_two_scope := type_of% (@_root_.D5.S3.Geometry.Polygons.PolygonEarSlide.Actual.cross_incident_two)

def cross_incident_two : cross_incident_two_scope :=
  @_root_.D5.S3.Geometry.Polygons.PolygonEarSlide.Actual.cross_incident_two

abbrev cross_incident_one_scope := type_of% (@_root_.D5.S3.Geometry.Polygons.PolygonEarSlide.Actual.cross_incident_one)

def cross_incident_one : cross_incident_one_scope :=
  @_root_.D5.S3.Geometry.Polygons.PolygonEarSlide.Actual.cross_incident_one

abbrev cross_s_implies_incident_one_scope := type_of% (@_root_.D5.S3.Geometry.Polygons.PolygonEarSlide.Actual.cross_s_implies_incident_one)

def cross_s_implies_incident_one : cross_s_implies_incident_one_scope :=
  @_root_.D5.S3.Geometry.Polygons.PolygonEarSlide.Actual.cross_s_implies_incident_one

abbrev cross_t_implies_incident_two_scope := type_of% (@_root_.D5.S3.Geometry.Polygons.PolygonEarSlide.Actual.cross_t_implies_incident_two)

def cross_t_implies_incident_two : cross_t_implies_incident_two_scope :=
  @_root_.D5.S3.Geometry.Polygons.PolygonEarSlide.Actual.cross_t_implies_incident_two

abbrev not_cross_t_of_avoidTwo_scope := type_of% (@_root_.D5.S3.Geometry.Polygons.PolygonEarSlide.Actual.not_cross_t_of_avoidTwo)

def not_cross_t_of_avoidTwo : not_cross_t_of_avoidTwo_scope :=
  @_root_.D5.S3.Geometry.Polygons.PolygonEarSlide.Actual.not_cross_t_of_avoidTwo

abbrev avoidTwo_of_diagonal_not_cross_t_scope := type_of% (@_root_.D5.S3.Geometry.Polygons.PolygonEarSlide.Actual.avoidTwo_of_diagonal_not_cross_t)

def avoidTwo_of_diagonal_not_cross_t : avoidTwo_of_diagonal_not_cross_t_scope :=
  @_root_.D5.S3.Geometry.Polygons.PolygonEarSlide.Actual.avoidTwo_of_diagonal_not_cross_t

abbrev not_cross_s_of_avoidOne_scope := type_of% (@_root_.D5.S3.Geometry.Polygons.PolygonEarSlide.Actual.not_cross_s_of_avoidOne)

def not_cross_s_of_avoidOne : not_cross_s_of_avoidOne_scope :=
  @_root_.D5.S3.Geometry.Polygons.PolygonEarSlide.Actual.not_cross_s_of_avoidOne

abbrev avoidOne_of_diagonal_not_cross_s_scope := type_of% (@_root_.D5.S3.Geometry.Polygons.PolygonEarSlide.Actual.avoidOne_of_diagonal_not_cross_s)

def avoidOne_of_diagonal_not_cross_s : avoidOne_of_diagonal_not_cross_s_scope :=
  @_root_.D5.S3.Geometry.Polygons.PolygonEarSlide.Actual.avoidOne_of_diagonal_not_cross_s

abbrev avoidTwo_of_chordSwap_of_avoidOne_scope := type_of% (@_root_.D5.S3.Geometry.Polygons.PolygonEarSlide.Actual.avoidTwo_of_chordSwap_of_avoidOne)

def avoidTwo_of_chordSwap_of_avoidOne : avoidTwo_of_chordSwap_of_avoidOne_scope :=
  @_root_.D5.S3.Geometry.Polygons.PolygonEarSlide.Actual.avoidTwo_of_chordSwap_of_avoidOne

abbrev chordSwap_not_incident_one_of_avoidTwo_scope := type_of% (@_root_.D5.S3.Geometry.Polygons.PolygonEarSlide.Actual.chordSwap_not_incident_one_of_avoidTwo)

def chordSwap_not_incident_one_of_avoidTwo : chordSwap_not_incident_one_of_avoidTwo_scope :=
  @_root_.D5.S3.Geometry.Polygons.PolygonEarSlide.Actual.chordSwap_not_incident_one_of_avoidTwo

abbrev avoidOne_of_chordSwap_of_avoidTwo_scope := type_of% (@_root_.D5.S3.Geometry.Polygons.PolygonEarSlide.Actual.avoidOne_of_chordSwap_of_avoidTwo)

def avoidOne_of_chordSwap_of_avoidTwo : avoidOne_of_chordSwap_of_avoidTwo_scope :=
  @_root_.D5.S3.Geometry.Polygons.PolygonEarSlide.Actual.avoidOne_of_chordSwap_of_avoidTwo

abbrev chordSwap_not_incident_two_of_avoidOne_scope := type_of% (@_root_.D5.S3.Geometry.Polygons.PolygonEarSlide.Actual.chordSwap_not_incident_two_of_avoidOne)

def chordSwap_not_incident_two_of_avoidOne : chordSwap_not_incident_two_of_avoidOne_scope :=
  @_root_.D5.S3.Geometry.Polygons.PolygonEarSlide.Actual.chordSwap_not_incident_two_of_avoidOne

abbrev cross_chordSwap_of_avoidOne_scope := type_of% (@_root_.D5.S3.Geometry.Polygons.PolygonEarSlide.Actual.cross_chordSwap_of_avoidOne)

def cross_chordSwap_of_avoidOne : cross_chordSwap_of_avoidOne_scope :=
  @_root_.D5.S3.Geometry.Polygons.PolygonEarSlide.Actual.cross_chordSwap_of_avoidOne

end Source

end Reg.D5.S3.Geometry.Polygons.PolygonEarSlideGeometry
