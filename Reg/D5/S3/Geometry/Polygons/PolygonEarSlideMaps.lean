import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Geometry.Polygons.PolygonEarSlideMaps
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Geometry.Polygons.PolygonEarSlideMaps
open _root_.D5.S3.Geometry.Polygons.PolygonEarSlide.Carrier
open _root_.D5.S3.Geometry.Polygons.PolygonEarSlide.Actual
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

abbrev signature : Signature where
  Params := {n : ℕ // 6 ≤ n}
  State n := Finset (Sym2 (ZMod n.1))
  Role := Bool
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ n := Finset (Sym2 (ZMod n.1))
  Anchor := Empty
  finiteAnchor := inferInstance

noncomputable def actual : Realization signature :=
  realize signature (fun role n T => by
    letI : NeZero n.1 := ⟨by have := n.2; omega⟩
    exact if role then phi T else psi T) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law O := ∀ (n : ℕ) [NeZero n] (hn : 6 ≤ n),
    (∀ T, IsTriangulation T → tEar ∈ T →
      IsTriangulation (O.readout true ⟨n, hn⟩ T)) ∧
    (∀ U, IsTriangulation U → sEar ∈ U →
      IsTriangulation (O.readout false ⟨n, hn⟩ U)) ∧
    (∀ T, (∀ e ∈ T, IsDiagonal e) → tEar ∈ T → sEar ∉ T →
      O.readout false ⟨n, hn⟩ (O.readout true ⟨n, hn⟩ T) = T) ∧
    (∀ U, (∀ e ∈ U, IsDiagonal e) → sEar ∈ U → tEar ∉ U →
      O.readout true ⟨n, hn⟩ (O.readout false ⟨n, hn⟩ U) = U)

theorem actual_law : arena.Law actual := by
  intro n _ hn
  exact ⟨fun T hT ht => phi_isTriangulation hn hT ht,
    fun U hU hs => psi_isTriangulation hn hU hs,
    fun T hT ht hs => psi_phi hn hT ht hs,
    fun U hU hs ht => phi_psi hn hU hs ht⟩

/-!
The actual dependent-family readout and its law retain the full source domain.
No Contract.Registration is asserted. Source reconstruction and binding,
a lawful enrolled-template readout, a rejected realization, whole-family
sensitivity, and actual observational dependence remain unproved.
-/

namespace Source

abbrev isDiagonal_chordSwap_of_ne_scope := type_of% (@_root_.D5.S3.Geometry.Polygons.PolygonEarSlide.Actual.isDiagonal_chordSwap_of_ne)

def isDiagonal_chordSwap_of_ne : isDiagonal_chordSwap_of_ne_scope :=
  @_root_.D5.S3.Geometry.Polygons.PolygonEarSlide.Actual.isDiagonal_chordSwap_of_ne

abbrev avoidTwo_of_mem_triangulation_scope := type_of% (@_root_.D5.S3.Geometry.Polygons.PolygonEarSlide.Actual.avoidTwo_of_mem_triangulation)

def avoidTwo_of_mem_triangulation : avoidTwo_of_mem_triangulation_scope :=
  @_root_.D5.S3.Geometry.Polygons.PolygonEarSlide.Actual.avoidTwo_of_mem_triangulation

abbrev avoidOne_of_mem_triangulation_scope := type_of% (@_root_.D5.S3.Geometry.Polygons.PolygonEarSlide.Actual.avoidOne_of_mem_triangulation)

def avoidOne_of_mem_triangulation : avoidOne_of_mem_triangulation_scope :=
  @_root_.D5.S3.Geometry.Polygons.PolygonEarSlide.Actual.avoidOne_of_mem_triangulation

abbrev isDiagonal_sEar_scope := type_of% (@_root_.D5.S3.Geometry.Polygons.PolygonEarSlide.Actual.isDiagonal_sEar)

def isDiagonal_sEar : isDiagonal_sEar_scope :=
  @_root_.D5.S3.Geometry.Polygons.PolygonEarSlide.Actual.isDiagonal_sEar

abbrev chordSwap_sEar_scope := type_of% (@_root_.D5.S3.Geometry.Polygons.PolygonEarSlide.Actual.chordSwap_sEar)

def chordSwap_sEar : chordSwap_sEar_scope :=
  @_root_.D5.S3.Geometry.Polygons.PolygonEarSlide.Actual.chordSwap_sEar

abbrev chordSwap_tEar_scope := type_of% (@_root_.D5.S3.Geometry.Polygons.PolygonEarSlide.Actual.chordSwap_tEar)

def chordSwap_tEar : chordSwap_tEar_scope :=
  @_root_.D5.S3.Geometry.Polygons.PolygonEarSlide.Actual.chordSwap_tEar

abbrev chordSwap_ne_sEar_of_diagonal_scope := type_of% (@_root_.D5.S3.Geometry.Polygons.PolygonEarSlide.Actual.chordSwap_ne_sEar_of_diagonal)

def chordSwap_ne_sEar_of_diagonal : chordSwap_ne_sEar_of_diagonal_scope :=
  @_root_.D5.S3.Geometry.Polygons.PolygonEarSlide.Actual.chordSwap_ne_sEar_of_diagonal

abbrev phi_erase_s_scope := type_of% (@_root_.D5.S3.Geometry.Polygons.PolygonEarSlide.Actual.phi_erase_s)

def phi_erase_s : phi_erase_s_scope :=
  @_root_.D5.S3.Geometry.Polygons.PolygonEarSlide.Actual.phi_erase_s

abbrev psi_phi_scope := type_of% (@_root_.D5.S3.Geometry.Polygons.PolygonEarSlide.Actual.psi_phi)

def psi_phi : psi_phi_scope :=
  @_root_.D5.S3.Geometry.Polygons.PolygonEarSlide.Actual.psi_phi

abbrev phi_image_members_are_diagonal_scope := type_of% (@_root_.D5.S3.Geometry.Polygons.PolygonEarSlide.Actual.phi_image_members_are_diagonal)

def phi_image_members_are_diagonal : phi_image_members_are_diagonal_scope :=
  @_root_.D5.S3.Geometry.Polygons.PolygonEarSlide.Actual.phi_image_members_are_diagonal

abbrev phi_isTriangulation_scope := type_of% (@_root_.D5.S3.Geometry.Polygons.PolygonEarSlide.Actual.phi_isTriangulation)

def phi_isTriangulation : phi_isTriangulation_scope :=
  @_root_.D5.S3.Geometry.Polygons.PolygonEarSlide.Actual.phi_isTriangulation

abbrev isDiagonal_tEar_scope := type_of% (@_root_.D5.S3.Geometry.Polygons.PolygonEarSlide.Actual.isDiagonal_tEar)

def isDiagonal_tEar : isDiagonal_tEar_scope :=
  @_root_.D5.S3.Geometry.Polygons.PolygonEarSlide.Actual.isDiagonal_tEar

abbrev psi_image_members_are_diagonal_scope := type_of% (@_root_.D5.S3.Geometry.Polygons.PolygonEarSlide.Actual.psi_image_members_are_diagonal)

def psi_image_members_are_diagonal : psi_image_members_are_diagonal_scope :=
  @_root_.D5.S3.Geometry.Polygons.PolygonEarSlide.Actual.psi_image_members_are_diagonal

abbrev psi_isTriangulation_scope := type_of% (@_root_.D5.S3.Geometry.Polygons.PolygonEarSlide.Actual.psi_isTriangulation)

def psi_isTriangulation : psi_isTriangulation_scope :=
  @_root_.D5.S3.Geometry.Polygons.PolygonEarSlide.Actual.psi_isTriangulation

abbrev chordSwap_ne_tEar_of_diagonal_scope := type_of% (@_root_.D5.S3.Geometry.Polygons.PolygonEarSlide.Actual.chordSwap_ne_tEar_of_diagonal)

def chordSwap_ne_tEar_of_diagonal : chordSwap_ne_tEar_of_diagonal_scope :=
  @_root_.D5.S3.Geometry.Polygons.PolygonEarSlide.Actual.chordSwap_ne_tEar_of_diagonal

abbrev psi_erase_t_scope := type_of% (@_root_.D5.S3.Geometry.Polygons.PolygonEarSlide.Actual.psi_erase_t)

def psi_erase_t : psi_erase_t_scope :=
  @_root_.D5.S3.Geometry.Polygons.PolygonEarSlide.Actual.psi_erase_t

abbrev phi_psi_scope := type_of% (@_root_.D5.S3.Geometry.Polygons.PolygonEarSlide.Actual.phi_psi)

def phi_psi : phi_psi_scope :=
  @_root_.D5.S3.Geometry.Polygons.PolygonEarSlide.Actual.phi_psi

end Source

end Reg.D5.S3.Geometry.Polygons.PolygonEarSlideMaps
