/- GID: D5/S3/Combinatorics/PerfectMatchings/PlanarSewing
   generality: I
   mirror-B: D5/B/S3/Combinatorics/PerfectMatchings/PlanarSewing
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Logic.Relation]
   utility: none
   digest: Adjacent planar sewing preserves the surviving endpoint components. -/

/-
admission_basis: open-problem-resolution (#27843; Refuted)
escape_witness: none (the settlement of the external open problem is the new content)
Qualified-name abbreviations:
PlanarDiagramAlgebra = D5.S3.Combinatorics.PerfectMatchings.PlanarDiagramAlgebra
concat = D5.S3.Combinatorics.PerfectMatchings.PlanarDiagramAlgebra.concat
generator = D5.S3.Combinatorics.PerfectMatchings.PlanarDiagramAlgebra.generator
PlanarSewing = D5.S3.Combinatorics.PerfectMatchings.PlanarSewing
appendMatching = D5.S3.Combinatorics.PerfectMatchings.PlanarSewing.appendMatching
graphEquiv = D5.S3.Combinatorics.PerfectMatchings.PlanarSewing.graphEquiv

Direct frozen dependencies (declaration statement_ids):
D5/S3/Combinatorics/PerfectMatchings/AdjacentCapSurgery.capConjugate
  sha256:2667f5ba82fd113fcc41c8be263525060382bd4605c2d950e21b4032cd3a46d9
D5/S3/Combinatorics/PerfectMatchings/AdjacentCapSurgery.capConjugate_apply
  sha256:458b832b49f5dd41089b9b568d15db79eaf986e065235a99a81704f5b8068ebc
D5/S3/Combinatorics/PerfectMatchings/AdjacentCapSurgery.capConjugate_involutive
  sha256:eb48432c20f35b33ba5c3673f2294a7acf13b7025d56e26ec097f77b4f21bb4b
D5/S3/Combinatorics/PerfectMatchings/AdjacentCapSurgery.capConjugate_left
  sha256:8424704803e5beade64b1bde9dc71a72d5d48385efec65054d5486dab6af2bdc
D5/S3/Combinatorics/PerfectMatchings/AdjacentCapSurgery.capConjugate_noFixed
  sha256:161538eefe81bd30a519bbe5036308f21345e72249c152e10076a95883bfb825
D5/S3/Combinatorics/PerfectMatchings/AdjacentCapSurgery.capConjugate_reconnect
  sha256:258194a977c3304068c82908b33ca11726aa1d48710351cd9dfcbf974eb9ac41
D5/S3/Combinatorics/PerfectMatchings/AdjacentCapSurgery.capConjugate_right
  sha256:7bf5882cb6accf4c88c1c538ceafc1514950083730d84ee6aaf790730b114499
D5/S3/Combinatorics/PerfectMatchings/AdjacentCapSurgery.capSurgery
  sha256:a631f23e62289e48c80ab8bd5e6a7f6c67372c17cbc52d772995fea3f08f6961
D5/S3/Combinatorics/PerfectMatchings/AdjacentCapSurgery.capSurgery_reconnect
  sha256:23f9ff8934d691e5681a7588d07f70783cac9803ee51c2fb4d7afc5620bae541
D5/S3/Combinatorics/PerfectMatchings/AdjacentCapSurgery.reconnect_noncrossing
  sha256:5e29e7921d2a5eb1a18c596269e08e0c0b58535b1783afa7ea27e434ec142c71
D5/S3/Combinatorics/PerfectMatchings/AdjacentCapSurgery.skipPair_injective
  sha256:8017c8dae5ea74706f5941c3b89c442f40c5286d1b875bc77b4b9db286b38d1c
D5/S3/Combinatorics/PerfectMatchings/AdjacentCapSurgery.skipPair_survives
  sha256:a25644c56aa92e3b28f386d06632e314ee8eb8b712a8c8e936c486a113e7b66c
D5/S3/Combinatorics/PerfectMatchings/OrderedMatchingCore.NCMatching
  sha256:e57e27461371a52ec60ddecf793e8636b33575dfd226354a0a39adeb4fc8c180
D5/S3/Combinatorics/PerfectMatchings/OrderedMatchingCore.involutive
  sha256:952f851e97f388905a3dabd603163f6a982fb69def10d7f46e7025a15586d2cd
D5/S3/Combinatorics/PerfectMatchings/OrderedMatchingCore.mk
  sha256:1030e558b1b45ecad828047a2e74ca2b713f7ccccb2635bfc0ed184729e87833
D5/S3/Combinatorics/PerfectMatchings/OrderedMatchingCore.noFixed
  sha256:edf38b300ee64671505ee0a1ee035db055015154013b789b9bff36a9ea8b281a
D5/S3/Combinatorics/PerfectMatchings/OrderedMatchingCore.noncrossing
  sha256:016d7f6e08c51271aee709de3227ded20ca9bf8ad61d56d28d7a7a6e715406df
D5/S3/Combinatorics/PerfectMatchings/OrderedMatchingCore.partner
  sha256:dd556735d78c793bfd2175e29f8de27dfff0f136b93fec8869630147a20628b4
D5/S3/Combinatorics/PerfectMatchings/OrderedMatchingCore.reconnectPartner
  sha256:c084a718d2a19017506efc26f7cb79068bce60f96a328ee5ae7e97c6982a4062
D5/S3/Combinatorics/PerfectMatchings/OrderedMatchingCore.skipPair
  sha256:3a5680065337c528c0efdbc07564bbab0594072ab7c635e2b9effb7216674946
D5/S3/Topology/FiniteMatchingClosure.Boundary
  sha256:2d22740b62cc9ff6a486d404f032436c21abd62130e080eb9e91719ecefa9bc6
D5/S3/Topology/FiniteMatchingClosure.Component
  sha256:5642ad6195d55697fcc1797d055319337e1d732d175cb3aea76182cc0cdf9f7c
D5/S3/Topology/FiniteMatchingClosure.Matching
  sha256:fd9df4ba1fc572f200a8c9ff58f36e53a205ade28d7c790a87120a8723a6cdb9
D5/S3/Topology/FiniteMatchingClosure.component
  sha256:c03bf702b492a3e83913d14d733d79ae45b49e152d146fa6b487bd400bdef2fc
D5/S3/Topology/FiniteMatchingClosure.contractionEquiv
  sha256:b9724ea28e62cb3a74b5c6f3bb144d6e06ebf94bf52e5e306136a4e4ab8793d1
D5/S3/Topology/FiniteMatchingClosure.cupcapMatching
  sha256:c244a1d0c295526be0811c97ed793929c5a156f92b1269a8c33c7bfda9bf3109
D5/S3/Topology/FiniteMatchingClosure.cupcapMate
  sha256:321e04f02fe4129cecb2018815c823a262827fb136c444f3f99d1d4471162f9f
D5/S3/Topology/FiniteMatchingClosure.fixedPointFree
  sha256:7e2300a12c5c75ab082a687677905e6360d7f3c6ba04162ecd59d5c5f03f894e
D5/S3/Topology/FiniteMatchingClosure.identityMatching
  sha256:4e81ed32fda7d78d7b0879b1359e8b4456fd02d02a1bddfc3866467d3101eef3
D5/S3/Topology/FiniteMatchingClosure.mate
  sha256:28b6db6a4ff9477dd543699cd3439ba967d854c089c412870c9eb135520ccf46
D5/S3/Topology/FiniteMatchingClosure.mk
  sha256:4fc3fe85063d058b492fafe29ae20fa10dfffad523cd690c888db9e20db73eae
D5/S3/Topology/FiniteMatchingComposition.Piece
  sha256:e72dfa50ef04ae4d4e6de55d69e4dc57394cad0a583db1c27c79b96530667750
D5/S3/Topology/FiniteMatchingComposition.composite
  sha256:916faedcd34e169a2fbdf6728df71f94600d26fc1f3c6b285d74c8f06225beff
D5/S3/Topology/FiniteMatchingComposition.composite_component_iff
  sha256:be312f600ea4ca4bbcccb5b57ae14d3f2185e967de1270a0e82c21fbe8136ff9
D5/S3/Topology/FiniteMatchingComposition.halfEdgeStep
  sha256:e69270f68620c6cf1c2ed2a5e10366812ee45336d79a74b56fc32ba1f344af88
D5/S3/Topology/FiniteMatchingComposition.outerPiece
  sha256:6c21173b5d70ba5684e939385e1dada6eacb74080d881a04c316994d0bbfb2fb
D5/S3/Topology/FiniteMatchingComposition.piecesMate
  sha256:fdcd9c399baea0d8d59316b5afc30b29bce9cada400909e1a4bd08353972343f
D5/S3/Topology/FiniteMatchingComposition.piecesPerm
  sha256:a81b0ecde851ecf043055e8d0b04a77ca43406b09951e6cc70e37cf2de0ad565
D5/S3/Topology/FiniteMatchingComposition.seamPerm
  sha256:2bd72984b5e26bd5e7a6da3a4a5674caf55288cd9e08a2c672a3a9ed630d0f22
D5/S3/Topology/FiniteMatchingSewing.matching_ext
  sha256:c122a00bd61ef1c7696ea12717caa82fe0b7d18ae95f1c43e0f1984a19ffa070
capStep: proof_shape=bind-only; consumers=PlanarSewing.capSurgery_comap,
  PlanarSewing.capSurgery_component_iff
reconnect_path: proof_shape=bind-only; consumers=PlanarSewing.capSurgery_path
capSurgery_path: proof_shape=bind-only; consumers=PlanarSewing.capSurgery_component_iff
Patch: proof_shape=bind-only; consumers=PlanarSewing.cap_component, PlanarSewing.patch_mate
patch_mate: proof_shape=bind-only; consumers=PlanarSewing.cap_component
cap_component: proof_shape=bind-only; consumers=PlanarSewing.survivor_component
survivor_component: proof_shape=bind-only; consumers=PlanarSewing.capSurgery_component_iff
capSurgery_component_iff: proof_shape=bind-only; consumers=PlanarSewing.capSurgery_comap
matchingSetoid: proof_shape=bind-only; consumers=PlanarSewing.capSurgery_comap,
  PlanarSewing.composite_planar
capSurgery_comap: proof_shape=bind-only; consumers=PlanarSewing.sewn_comap
seamLeft: proof_shape=bind-only; consumers=PlanarSewing.flat_seam_left,
  PlanarSewing.graphEquiv._proof_4
seamRight: proof_shape=bind-only; consumers=PlanarSewing.flat_seam_right,
  PlanarSewing.graphEquiv._proof_4
seamSetoid: proof_shape=bind-only; consumers=PlanarSewing.composite_planar,
  PlanarSewing.graphStep_setoid
seam_skip_left: proof_shape=bind-only; consumers=PlanarSewing.seam_reduction
seam_skip_right: proof_shape=bind-only; consumers=PlanarSewing.seam_reduction
rel_sup_left: proof_shape=bind-only; consumers=PlanarSewing.graphStep_setoid,
  PlanarSewing.seam_reduction
rel_sup_right: proof_shape=bind-only; consumers=PlanarSewing.graphStep_setoid,
  PlanarSewing.seam_reduction
rel_map: proof_shape=bind-only; consumers=PlanarSewing.seam_reduction
seam_reduction: proof_shape=bind-only; consumers=PlanarSewing.sewn_comap
sewn_comap: proof_shape=bind-only; consumers=PlanarSewing.sewn_planar
gapEmbedding: proof_shape=bind-only; consumers=PlanarSewing.composite_planar,
  PlanarSewing.flat_outer
gapEmbedding_step: proof_shape=bind-only; consumers=PlanarSewing.sewn_planar
seamSetoid_zero: proof_shape=bind-only; consumers=PlanarSewing.sewn_planar
sewn_planar: proof_shape=bind-only; consumers=PlanarSewing.composite_planar
appendPartner: proof_shape=bind-only; consumers=PlanarSewing.appendMatching,
  PlanarSewing.appendMatching._proof_1
appendPartner_left: proof_shape=bind-only; consumers=PlanarSewing.appendMatching._proof_1,
  PlanarSewing.appendMatching._proof_4
appendPartner_right: proof_shape=bind-only; consumers=PlanarSewing.appendMatching._proof_1,
  PlanarSewing.appendMatching._proof_4
appendMatching: proof_shape=bind-only; consumers=PlanarSewing.composite_planar,
  PlanarSewing.flat_mate
boundaryEquiv: proof_shape=bind-only; consumers=PlanarSewing.boundary_bottom,
  PlanarSewing.boundary_top
toMatching: proof_shape=bind-only; consumers=PlanarDiagramAlgebra.Diagram,
  PlanarDiagramAlgebra.basisProduct
flatEquiv: proof_shape=bind-only; consumers=PlanarSewing.composite_planar, PlanarSewing.flat_left
flat_left: proof_shape=bind-only; consumers=PlanarSewing.flat_mate, PlanarSewing.flat_outer
flat_right: proof_shape=bind-only; consumers=PlanarSewing.flat_mate, PlanarSewing.flat_outer
boundary_top: proof_shape=bind-only; consumers=PlanarSewing.cupcap_planar_succ,
  PlanarSewing.flat_outer
boundary_bottom: proof_shape=bind-only; consumers=PlanarSewing.cupcap_planar_succ,
  PlanarSewing.flat_outer
flat_mate: proof_shape=bind-only; consumers=PlanarSewing.graphEquiv._proof_4,
  PlanarSewing.graphEquiv._proof_5
flat_outer: proof_shape=bind-only; consumers=PlanarSewing.composite_planar
flat_seam_left: proof_shape=bind-only; consumers=PlanarSewing.graphEquiv._proof_4,
  PlanarSewing.graphEquiv._proof_5
flat_seam_right: proof_shape=bind-only; consumers=PlanarSewing.graphEquiv._proof_4,
  PlanarSewing.graphEquiv._proof_5
graphStep: proof_shape=bind-only; consumers=PlanarSewing.composite_planar, PlanarSewing.graphEquiv
graphStep_setoid: proof_shape=bind-only; consumers=PlanarSewing.composite_planar
graphEquiv: proof_shape=bind-only; consumers=PlanarSewing.composite_planar
composite_planar: proof_shape=bind-only; consumers=PlanarDiagramAlgebra.concat._proof_1
identityNC: proof_shape=bind-only; consumers=PlanarSewing.cupcap_planar_succ,
  PlanarSewing.identity_planar
identity_planar: proof_shape=bind-only; consumers=PlanarDiagramAlgebra.identity,
  PlanarDiagramAlgebra.mul_one'
capReconnection: proof_shape=bind-only; consumers=PlanarSewing.cupcap_planar_succ
swap_val: proof_shape=bind-only; consumers=PlanarSewing.cupcap_planar_succ
cupcap_planar_succ: proof_shape=bind-only; consumers=PlanarSewing.cupcap_planar
cupcap_planar: proof_shape=bind-only; consumers=PlanarDiagramAlgebra.generator._proof_3
-/
import D5.S3.Combinatorics.PerfectMatchings.OrderedMatchingCore
import D5.S3.Combinatorics.PerfectMatchings.AdjacentCapSurgery
import D5.S3.Combinatorics.PerfectMatchings.AraujoBrauerSourceMonoids
import D5.S3.Topology.FiniteMatchingClosure
import D5.S3.Topology.FiniteMatchingComposition
import D5.S3.Topology.FiniteMatchingSewing
import Mathlib.Logic.Relation
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Equiv.Prod

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable

namespace D5.S3.Combinatorics.PerfectMatchings.PlanarSewing
open CupCapBridgeProposal
open D5.S3.Topology.FiniteMatchingClosure
open D5.S3.Topology.FiniteMatchingComposition
open D5.S3.Topology.FiniteMatchingSewing
open D5.S3.Combinatorics.PerfectMatchings.AraujoBrauerSourceMonoids

def capStep {m : ℕ} (M : NCMatching (m+2)) (j : Fin (m+1))
    (x y : Fin (m+2)) : Prop :=
  y = M.partner x ∨ (x = j.castSucc ∧ y = j.succ)

private theorem reconnect_path {m : ℕ} (M : NCMatching (m+2)) (j : Fin (m+1))
    (x : Fin (m+2)) :
    Relation.EqvGen (capStep M j) x (reconnectPartner M j x) := by
  unfold reconnectPartner
  split_ifs with ha hb
  · exact .trans _ _ _ (.rel _ _ (Or.inl ha.symm))
      (.trans _ _ _ (.rel _ _ (Or.inr ⟨rfl,rfl⟩)) (.rel _ _ (Or.inl rfl)))
  · exact .trans _ _ _ (.rel _ _ (Or.inl hb.symm))
      (.trans _ _ _ (.symm _ _ (.rel _ _ (Or.inr ⟨rfl,rfl⟩)))
        (.rel _ _ (Or.inl rfl)))
  · exact .rel _ _ (Or.inl rfl)

private theorem capSurgery_path {m : ℕ} (M : NCMatching (m+2)) (j : Fin (m+1))
    (x : Fin m) :
    Relation.EqvGen (capStep M j) (skipPair j x)
      (skipPair j ((capSurgery M j).partner x)) := by
  rw [capSurgery_reconnect]
  exact reconnect_path M j _

private def Patch {m : ℕ} (M : NCMatching (m+2)) (j : Fin (m+1)) (x : Fin (m+2)) : Prop :=
  x = j.castSucc ∨ x = j.succ ∨ x = M.partner j.castSucc ∨ x = M.partner j.succ

private theorem patch_mate {m : ℕ} (M : NCMatching (m+2)) (j : Fin (m+1))
    (x : Fin (m+2)) : Patch M j (M.partner x) ↔ Patch M j x := by
  unfold Patch
  constructor
  · rintro (h | h | h | h)
    · right; right; left
      exact (M.involutive x).symm.trans (congrArg M.partner h)
    · right; right; right
      exact (M.involutive x).symm.trans (congrArg M.partner h)
    · exact Or.inl (M.partner.injective h)
    · exact Or.inr (Or.inl (M.partner.injective h))
  · rintro (rfl | rfl | rfl | rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr rfl))
    · exact Or.inl (M.involutive _)
    · exact Or.inr (Or.inl (M.involutive _))

private theorem cap_component {m : ℕ} (M : NCMatching (m+2)) (j : Fin (m+1))
    (x y : Fin (m+2)) :
    Relation.EqvGen (capStep M j) x y ↔
      y = x ∨ y = M.partner x ∨ (Patch M j x ∧ Patch M j y) := by
  constructor
  · intro h
    induction h with
    | rel x y h =>
      rcases h with h | ⟨rfl,rfl⟩
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr ⟨Or.inl rfl, Or.inr (Or.inl rfl)⟩)
    | refl => exact Or.inl rfl
    | symm x y h ih =>
      rcases ih with h | h | ⟨hx,hy⟩
      · exact Or.inl h.symm
      · exact Or.inr (Or.inl (by rw [h, M.involutive]))
      · exact Or.inr (Or.inr ⟨hy,hx⟩)
    | trans x y z hxy hyz ih₁ ih₂ =>
      rcases ih₁ with rfl | rfl | ⟨hx,hy⟩
      · exact ih₂
      · rcases ih₂ with h | h | ⟨hy,hz⟩
        · exact Or.inr (Or.inl h)
        · exact Or.inl (h.trans (M.involutive x))
        · exact Or.inr (Or.inr ⟨(patch_mate M j x).mp hy,hz⟩)
      · rcases ih₂ with rfl | rfl | ⟨_,hz⟩
        · exact Or.inr (Or.inr ⟨hx,hy⟩)
        · exact Or.inr (Or.inr ⟨hx,(patch_mate M j y).mpr hy⟩)
        · exact Or.inr (Or.inr ⟨hx,hz⟩)
  · have hp (z : Fin (m+2)) (hz : Patch M j z) :
        Relation.EqvGen (capStep M j) j.castSucc z := by
      rcases hz with rfl | rfl | rfl | rfl
      · exact .refl _
      · exact .rel _ _ (Or.inr ⟨rfl,rfl⟩)
      · exact .rel _ _ (Or.inl rfl)
      · exact .trans _ _ _ (.rel _ _ (Or.inr ⟨rfl,rfl⟩)) (.rel _ _ (Or.inl rfl))
    rintro (rfl | rfl | ⟨hx,hy⟩)
    · exact .refl _
    · exact .rel _ _ (Or.inl rfl)
    · exact .trans _ _ _ (.symm _ _ (hp x hx)) (hp y hy)

private theorem survivor_component {m : ℕ} (M : NCMatching (m+2)) (j : Fin (m+1))
    (x y : Fin (m+2)) (hxa : x ≠ j.castSucc) (hxb : x ≠ j.succ)
    (hya : y ≠ j.castSucc) (hyb : y ≠ j.succ)
    (h : Relation.EqvGen (capStep M j) x y) :
    y = x ∨ y = reconnectPartner M j x := by
  have hab : j.castSucc ≠ j.succ := by
    intro h; have := congrArg Fin.val h; simp only [Fin.val_castSucc, Fin.val_succ] at this; omega
  rcases (cap_component M j x y).mp h with h | h | ⟨hx,hy⟩
  · exact Or.inl h
  · right
    have hpa : M.partner x ≠ j.castSucc := fun hh => hya (h.trans hh)
    have hpb : M.partner x ≠ j.succ := fun hh => hyb (h.trans hh)
    simpa only [reconnectPartner, ite_eq_right hpa, ite_eq_right hpb] using h
  · rcases hx with hx | hx | rfl | rfl
    · exact False.elim (hxa hx)
    · exact False.elim (hxb hx)
    · rcases hy with hy | hy | rfl | rfl
      · exact False.elim (hya hy)
      · exact False.elim (hyb hy)
      · exact Or.inl rfl
      · exact Or.inr (by unfold reconnectPartner; rw [M.involutive _]; simp only [ite_true])
    · rcases hy with hy | hy | rfl | rfl
      · exact False.elim (hya hy)
      · exact False.elim (hyb hy)
      · exact Or.inr (by unfold reconnectPartner; rw [M.involutive _]; simp only [ite_eq_right hab.symm, ite_true])
      · exact Or.inl rfl

/-- Removing a sewn adjacent pair preserves precisely the endpoint relation. -/
theorem capSurgery_component_iff {m : ℕ} (M : NCMatching (m+2)) (j : Fin (m+1))
    (x y : Fin m) :
    Relation.EqvGen (capStep M j) (skipPair j x) (skipPair j y) ↔
      y = x ∨ y = (capSurgery M j).partner x := by
  constructor
  · intro h
    rcases survivor_component M j _ _
      (skipPair_survives j x).1 (skipPair_survives j x).2
      (skipPair_survives j y).1 (skipPair_survives j y).2 h with h | h
    · exact Or.inl (skipPair_injective j h)
    · right
      apply skipPair_injective j
      rw [capSurgery_reconnect]
      exact h
  · rintro (rfl | rfl)
    · exact .refl _
    · exact capSurgery_path M j x

private def matchingSetoid {m : ℕ} (M : NCMatching m) : Setoid (Fin m) :=
  involutionSetoid M.partner M.involutive

private theorem capSurgery_comap {m : ℕ} (M : NCMatching (m+2)) (j : Fin (m+1)) :
    Setoid.comap (skipPair j) (Relation.EqvGen.setoid (capStep M j)) =
      matchingSetoid (capSurgery M j) := by
  ext x y
  change Relation.EqvGen (capStep M j) (skipPair j x) (skipPair j y) ↔
    (x = y ∨ (capSurgery M j).partner x = y)
  rw [capSurgery_component_iff]
  exact or_congr eq_comm eq_comm

private def seamLeft (p k N : ℕ) (h : p+2*k ≤ N) (t : Fin k) : Fin N :=
  ⟨p+t, by omega⟩

private def seamRight (p k N : ℕ) (h : p+2*k ≤ N) (t : Fin k) : Fin N :=
  ⟨p+(2*k-1-t), by omega⟩

private def seamSetoid (p k N : ℕ) (h : p+2*k ≤ N) : Setoid (Fin N) :=
  Relation.EqvGen.setoid (fun x y =>
    ∃ t : Fin k, x = seamLeft p k N h t ∧ y = seamRight p k N h t)

private theorem seam_skip_left {p k m : ℕ} (h : p+2*(k+1) ≤ m+2) (t : Fin k) :
    skipPair (⟨p+k,by omega⟩ : Fin (m+1)) (seamLeft p k m (by omega) t) =
      seamLeft p (k+1) (m+2) h t.castSucc := by
  apply Fin.ext
  change (if p+t.val < p+k then p+t.val else p+t.val+2) = p+t.val
  rw [ite_eq_left (by omega)]

private theorem seam_skip_right {p k m : ℕ} (h : p+2*(k+1) ≤ m+2) (t : Fin k) :
    skipPair (⟨p+k,by omega⟩ : Fin (m+1)) (seamRight p k m (by omega) t) =
      seamRight p (k+1) (m+2) h t.castSucc := by
  apply Fin.ext
  change (if p+(2*k-1-t.val) < p+k then p+(2*k-1-t.val) else p+(2*k-1-t.val)+2) =
    p+(2*(k+1)-1-t.val)
  rw [ite_eq_right (by omega)]
  omega

private theorem rel_sup_left {X : Type*} {R S : Setoid X} {x y : X}
    (h : R x y) : (R ⊔ S) x y := Setoid.le_def.mp le_sup_left h

private theorem rel_sup_right {X : Type*} {R S : Setoid X} {x y : X}
    (h : S x y) : (R ⊔ S) x y := Setoid.le_def.mp le_sup_right h

private theorem rel_map {X Y : Type*} (R : Setoid X) (f : X → Y) {x y : X}
    (h : R x y) : (R.map f) (f x) (f y) := Setoid.le_def.mp Setoid.le_comap_map h

private theorem seam_reduction {p k m : ℕ} (M : NCMatching (m+2))
    (h : p+2*(k+1) ≤ m+2) :
    matchingSetoid M ⊔ seamSetoid p (k+1) (m+2) h =
      Relation.EqvGen.setoid (capStep M (⟨p+k,by omega⟩ : Fin (m+1))) ⊔
        (seamSetoid p k m (by omega)).map (skipPair (⟨p+k,by omega⟩ : Fin (m+1))) := by
  let j : Fin (m+1) := ⟨p+k,by omega⟩
  apply le_antisymm
  · apply sup_le
    · intro x y hxy
      apply rel_sup_left
      rcases hxy with rfl | rfl
      · exact .refl _
      · exact .rel _ _ (Or.inl rfl)
    · apply Setoid.eqvGen_le
      rintro x y ⟨t,rfl,rfl⟩
      by_cases ht : t.val < k
      · let s : Fin k := ⟨t.val,ht⟩
        have he : s.castSucc = t := Fin.ext rfl
        rw [← he, ← seam_skip_left h s, ← seam_skip_right h s]
        apply rel_sup_right
        exact rel_map _ _ (Relation.EqvGen.rel _ _ ⟨s,rfl,rfl⟩)
      · have ht : t.val = k := by omega
        have ha : seamLeft p (k+1) (m+2) h t = j.castSucc := Fin.ext (by simp [seamLeft,j,ht])
        have hb : seamRight p (k+1) (m+2) h t = j.succ := Fin.ext (by dsimp [seamRight,j]; omega)
        rw [ha,hb]
        exact rel_sup_left (Relation.EqvGen.rel _ _ (Or.inr ⟨rfl,rfl⟩))
  · apply sup_le
    · apply Setoid.eqvGen_le
      intro x y hxy
      rcases hxy with rfl | ⟨rfl,rfl⟩
      · exact rel_sup_left (Or.inr rfl)
      · apply rel_sup_right
        apply Relation.EqvGen.rel
        refine ⟨Fin.last k,?_,?_⟩
        · apply Fin.ext; rfl
        · apply Fin.ext; dsimp [seamRight,j]; omega
    · apply Setoid.gc_map_comap.le_iff_le.mpr
      apply Setoid.eqvGen_le
      rintro x y ⟨t,rfl,rfl⟩
      change (matchingSetoid M ⊔ seamSetoid p (k+1) (m+2) h).r
        (skipPair j (seamLeft p k m _ t)) (skipPair j (seamRight p k m _ t))
      rw [seam_skip_left h, seam_skip_right h]
      exact rel_sup_right (Relation.EqvGen.rel _ _ ⟨t.castSucc,rfl,rfl⟩)

private theorem sewn_comap {p k m : ℕ} (M : NCMatching (m+2))
    (h : p+2*(k+1) ≤ m+2) :
    Setoid.comap (skipPair (⟨p+k,by omega⟩ : Fin (m+1)))
      (matchingSetoid M ⊔ seamSetoid p (k+1) (m+2) h) =
      matchingSetoid (capSurgery M (⟨p+k,by omega⟩ : Fin (m+1))) ⊔
        seamSetoid p k m (by omega) := by
  rw [seam_reduction M h, comap_sup_map, capSurgery_comap]

private def gapEmbedding (p k m N : ℕ) (h : m+2*k ≤ N) (x : Fin m) : Fin N :=
  ⟨if x.val < p then x.val else x.val+2*k, by split_ifs <;> omega⟩

private theorem gapEmbedding_step {p k m N : ℕ} (hp : p ≤ m) (hN : N = m+2*k)
    (x : Fin m) :
    gapEmbedding p (k+1) m (N+2) (by omega) x =
      skipPair (⟨p+k,by omega⟩ : Fin (N+1)) (gapEmbedding p k m N (by omega) x) := by
  apply Fin.ext
  simp only [gapEmbedding, skipPair, insertPort, Fin.val_mk]
  split_ifs <;> omega

private theorem seamSetoid_zero (p N : ℕ) (h : p+2*0 ≤ N) :
    seamSetoid p 0 N h = ⊥ := by
  apply le_antisymm
  · apply Setoid.eqvGen_le
    rintro x y ⟨t,_⟩
    exact Fin.elim0 t
  · exact bot_le

/-- Sewing any number of nested adjacent seam pairs leaves a planar pairing
on the surviving boundary, with exactly the induced component relation. -/
private theorem sewn_planar (m p k N : ℕ) (hp : p ≤ m) (hN : N = m+2*k)
    (M : NCMatching N) :
    ∃ Q : NCMatching m,
      matchingSetoid Q = Setoid.comap (gapEmbedding p k m N (by omega))
        (matchingSetoid M ⊔ seamSetoid p k N (by omega)) := by
  induction k generalizing N with
  | zero =>
    simp only [Nat.mul_zero, Nat.add_zero] at hN
    subst N
    refine ⟨M,?_⟩
    rw [seamSetoid_zero, sup_bot_eq]
    have hg : gapEmbedding p 0 m m (by omega) = id := by
      funext x
      apply Fin.ext
      dsimp [gapEmbedding]
      split_ifs <;> omega
    rw [hg, Setoid.comap_id]
  | succ k ih =>
    obtain ⟨t,rfl⟩ : ∃ t, N = t+2 := ⟨N-2,by omega⟩
    have ht : t = m+2*k := by omega
    let j : Fin (t+1) := ⟨p+k,by omega⟩
    obtain ⟨Q,hQ⟩ := ih t ht (capSurgery M j)
    refine ⟨Q,?_⟩
    have hg : gapEmbedding p (k+1) m (t+2) (by omega) =
        skipPair j ∘ gapEmbedding p k m t (by omega) := by
      funext x
      exact gapEmbedding_step hp ht x
    rw [hg, Setoid.comap_comp, sewn_comap M (by omega)]
    exact hQ

private def appendPartner {m n : ℕ} (M : NCMatching m) (N : NCMatching n) :
    Equiv.Perm (Fin (m+n)) :=
  finSumFinEquiv.symm.trans ((Equiv.sumCongr M.partner N.partner).trans finSumFinEquiv)

private theorem appendPartner_left {m n : ℕ} (M : NCMatching m) (N : NCMatching n)
    (i : Fin m) : appendPartner M N (Fin.castAdd n i) = Fin.castAdd n (M.partner i) := by
  simp [appendPartner]

private theorem appendPartner_right {m n : ℕ} (M : NCMatching m) (N : NCMatching n)
    (i : Fin n) : appendPartner M N (Fin.natAdd m i) = Fin.natAdd m (N.partner i) := by
  simp [appendPartner]

private def appendMatching {m n : ℕ} (M : NCMatching m) (N : NCMatching n) :
    NCMatching (m+n) where
  partner := appendPartner M N
  involutive i := by
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · rw [appendPartner_left, appendPartner_left, M.involutive]
    · rw [appendPartner_right, appendPartner_right, N.involutive]
  noFixed i := by
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · rw [appendPartner_left]
      exact fun h => M.noFixed j (Fin.ext (congrArg (fun z : Fin (m+n) => z.val) h))
    · rw [appendPartner_right]
      exact fun h => N.noFixed j (Fin.ext (Nat.add_left_cancel (congrArg Fin.val h)))
  noncrossing a b := by
    refine Fin.addCases (fun x => ?_) (fun x => ?_) a <;>
      refine Fin.addCases (fun y => ?_) (fun y => ?_) b
    · simpa only [appendPartner_left, Fin.lt_def, Fin.val_castAdd] using M.noncrossing x y
    · rw [appendPartner_left, appendPartner_right]
      intro _ h _
      have := (M.partner x).isLt
      simp only [Fin.lt_def, Fin.val_natAdd, Fin.val_castAdd] at h
      omega
    · rw [appendPartner_right, appendPartner_left]
      intro h _ _
      have := y.isLt
      simp only [Fin.lt_def, Fin.val_natAdd, Fin.val_castAdd] at h
      omega
    · simpa only [appendPartner_right, Fin.natAdd_lt_natAdd_iff] using N.noncrossing x y

/-- Rectangle boundary order, with the lower row reversed. -/
def boundaryEquiv (n : ℕ) : Bool × Fin n ≃ Fin (2*n) :=
  (Equiv.boolProdEquivSum (Fin n)).trans
    ((Equiv.sumCongr (Equiv.refl _) Fin.revPerm).trans
      (finSumFinEquiv.trans (finCongr (by omega))))

noncomputable def toMatching {n : ℕ} (M : NCMatching (2*n)) :
    D5.S3.Topology.FiniteMatchingClosure.Matching (Bool × Fin n) where
  mate x := (boundaryEquiv n).symm (M.partner (boundaryEquiv n x))
  involutive x := by
    dsimp only
    rw [(boundaryEquiv n).apply_symm_apply, M.involutive,
      (boundaryEquiv n).symm_apply_apply]
  fixedPointFree x := by
    intro h
    have h' := congrArg (boundaryEquiv n) h
    simp only [(boundaryEquiv n).apply_symm_apply] at h'
    exact M.noFixed _ h'


private def flatEquiv (n : ℕ) : Piece n ≃ Fin (2*n+2*n) :=
  (Equiv.boolProdEquivSum (Boundary n)).trans
    ((Equiv.sumCongr (boundaryEquiv n) (boundaryEquiv n)).trans finSumFinEquiv)

private theorem flat_left {n : ℕ} (b : Boundary n) :
    flatEquiv n (false,b) = Fin.castAdd (2*n) (boundaryEquiv n b) := by
  simp [flatEquiv, Equiv.boolProdEquivSum]

private theorem flat_right {n : ℕ} (b : Boundary n) :
    flatEquiv n (true,b) = Fin.natAdd (2*n) (boundaryEquiv n b) := by
  simp [flatEquiv, Equiv.boolProdEquivSum]

private theorem boundary_top {n : ℕ} (i : Fin n) :
    (boundaryEquiv n (false,i)).val = i.val := by
  simp [boundaryEquiv, Equiv.boolProdEquivSum]

private theorem boundary_bottom {n : ℕ} (i : Fin n) :
    (boundaryEquiv n (true,i)).val = 2*n-1-i.val := by
  simp [boundaryEquiv, Equiv.boolProdEquivSum, Fin.rev]
  omega

private theorem flat_mate {n : ℕ} (M N : NCMatching (2*n)) (x : Piece n) :
    flatEquiv n (piecesMate (toMatching M) (toMatching N) x) =
      (appendMatching M N).partner (flatEquiv n x) := by
  rcases x with ⟨l,b⟩
  cases l
  · change flatEquiv n (false,(toMatching M).mate b) =
      appendPartner M N (flatEquiv n (false,b))
    rw [flat_left, flat_left, appendPartner_left]
    change Fin.castAdd (2*n) (boundaryEquiv n ((boundaryEquiv n).symm
      (M.partner (boundaryEquiv n b)))) = _
    rw [Equiv.apply_symm_apply]
  · change flatEquiv n (true,(toMatching N).mate b) =
      appendPartner M N (flatEquiv n (true,b))
    rw [flat_right, flat_right, appendPartner_right]
    change Fin.natAdd (2*n) (boundaryEquiv n ((boundaryEquiv n).symm
      (N.partner (boundaryEquiv n b)))) = _
    rw [Equiv.apply_symm_apply]

private theorem flat_outer {n : ℕ} (b : Boundary n) :
    flatEquiv n (outerPiece b) = gapEmbedding n n (2*n) (2*n+2*n) (by omega)
      (boundaryEquiv n b) := by
  rcases b with ⟨b,i⟩
  cases b
  · rw [show outerPiece (false,i) = (false,(false,i)) from rfl, flat_left]
    apply Fin.ext
    change (boundaryEquiv n (false,i)).val =
      if (boundaryEquiv n (false,i)).val < n then (boundaryEquiv n (false,i)).val
      else (boundaryEquiv n (false,i)).val+2*n
    rw [boundary_top, ite_eq_left i.isLt]
  · rw [show outerPiece (true,i) = (true,(true,i)) from rfl, flat_right]
    apply Fin.ext
    change 2*n+(boundaryEquiv n (true,i)).val =
      if (boundaryEquiv n (true,i)).val < n then (boundaryEquiv n (true,i)).val
      else (boundaryEquiv n (true,i)).val+2*n
    rw [boundary_bottom, ite_eq_right (by omega)]
    omega

private theorem flat_seam_left {n : ℕ} (i : Fin n) :
    flatEquiv n (false,(true,i)) =
      seamLeft n n (2*n+2*n) (by omega) (⟨n-1-i.val,by omega⟩ : Fin n) := by
  rw [flat_left]
  apply Fin.ext
  change (boundaryEquiv n (true,i)).val = n+(n-1-i.val)
  rw [boundary_bottom]
  omega

private theorem flat_seam_right {n : ℕ} (i : Fin n) :
    flatEquiv n (true,(false,i)) =
      seamRight n n (2*n+2*n) (by omega) (⟨n-1-i.val,by omega⟩ : Fin n) := by
  rw [flat_right]
  apply Fin.ext
  change 2*n+(boundaryEquiv n (false,i)).val = n+(2*n-1-(n-1-i.val))
  rw [boundary_top]
  omega

private def graphStep {n : ℕ} (M N : NCMatching (2*n)) (x y : Fin (2*n+2*n)) : Prop :=
  y = (appendMatching M N).partner x ∨
    ∃ t : Fin n, x = seamLeft n n (2*n+2*n) (by omega) t ∧
      y = seamRight n n (2*n+2*n) (by omega) t

private theorem graphStep_setoid {n : ℕ} (M N : NCMatching (2*n)) :
    Relation.EqvGen.setoid (graphStep M N) =
      matchingSetoid (appendMatching M N) ⊔ seamSetoid n n (2*n+2*n) (by omega) := by
  apply le_antisymm
  · apply Setoid.eqvGen_le
    intro x y h
    rcases h with rfl | h
    · exact rel_sup_left (Or.inr rfl)
    · exact rel_sup_right (Relation.EqvGen.rel _ _ h)
  · apply sup_le
    · intro x y h
      rcases h with rfl | rfl
      · exact .refl _
      · exact .rel _ _ (Or.inl rfl)
    · apply Setoid.eqvGen_le
      intro x y h
      exact .rel _ _ (Or.inr h)

private def graphEquiv {n : ℕ} (M N : NCMatching (2*n)) :
    Component (graphStep M N) ≃ Component (halfEdgeStep (toMatching M) (toMatching N)) := by
  apply contractionEquiv _ _ (flatEquiv n).symm (flatEquiv n)
    (flatEquiv n).symm_apply_apply
  · intro x y h
    rcases h with rfl | ⟨t,rfl,rfl⟩
    · apply Relation.EqvGen.rel
      left
      apply (flatEquiv n).injective
      change flatEquiv n ((flatEquiv n).symm ((appendMatching M N).partner x)) =
        flatEquiv n (piecesMate (toMatching M) (toMatching N) ((flatEquiv n).symm x))
      rw [flat_mate, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    · let i : Fin n := ⟨n-1-t.val,by omega⟩
      have hi : (⟨n-1-i.val,by omega⟩ : Fin n) = t := Fin.ext (by dsimp [i]; omega)
      have hl := flat_seam_left i
      have hr := flat_seam_right i
      rw [hi] at hl hr
      rw [← hl, ← hr, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
      exact .rel _ _ (Or.inr rfl)
  · intro x y h
    rcases h with h | h
    · subst y
      change Relation.EqvGen (graphStep M N) _ (flatEquiv n (piecesMate _ _ x))
      rw [flat_mate]
      exact .rel _ _ (Or.inl rfl)
    · subst y
      rcases x with ⟨l,b,i⟩
      cases l <;> cases b
      · exact .refl _
      · change Relation.EqvGen (graphStep M N) (flatEquiv n (false,(true,i)))
          (flatEquiv n (true,(false,i)))
        rw [flat_seam_left, flat_seam_right]
        exact .rel _ _ (Or.inr ⟨_,rfl,rfl⟩)
      · change Relation.EqvGen (graphStep M N) (flatEquiv n (true,(false,i)))
          (flatEquiv n (false,(true,i)))
        rw [flat_seam_left, flat_seam_right]
        exact .symm _ _ (.rel _ _ (Or.inr ⟨_,rfl,rfl⟩))
      · exact .refl _
  · intro x
    rw [Equiv.apply_symm_apply]
    exact .refl _

/-- Literal path composition of two planar rectangle matchings is planar. -/
theorem composite_planar {n : ℕ} (M N : NCMatching (2*n)) :
    ∃ Q : NCMatching (2*n), toMatching Q = composite (toMatching M) (toMatching N) := by
  obtain ⟨Q,hQ⟩ := sewn_planar (2*n) n n (2*n+2*n) (by omega) rfl (appendMatching M N)
  refine ⟨Q,?_⟩
  apply matching_ext
  intro a
  let b := (toMatching Q).mate a
  have h : Relation.EqvGen (graphStep M N) (flatEquiv n (outerPiece a))
      (flatEquiv n (outerPiece b)) := by
    change (Relation.EqvGen.setoid (graphStep M N)) _ _
    rw [graphStep_setoid, flat_outer, flat_outer]
    change (Setoid.comap (gapEmbedding n n (2*n) (2*n+2*n) _)
      (matchingSetoid (appendMatching M N) ⊔ seamSetoid n n (2*n+2*n) _))
      (boundaryEquiv n a) (boundaryEquiv n b)
    rw [← hQ]
    right
    exact (Equiv.apply_symm_apply (boundaryEquiv n) _).symm
  have he := congrArg (graphEquiv M N) (Quotient.sound h)
  change component (halfEdgeStep (toMatching M) (toMatching N))
      ((flatEquiv n).symm (flatEquiv n (outerPiece a))) =
    component (halfEdgeStep (toMatching M) (toMatching N))
      ((flatEquiv n).symm (flatEquiv n (outerPiece b))) at he
  rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply] at he
  rcases (composite_component_iff (toMatching M) (toMatching N) a b).mp he with he | he
  · exact False.elim ((toMatching Q).fixedPointFree a he)
  · exact he

private def identityNC (n : ℕ) : NCMatching (2*n) where
  partner := Fin.revPerm
  involutive x := Fin.rev_rev x
  noFixed x := by
    intro h
    have he := congrArg Fin.val h
    simp only [Fin.revPerm_apply, Fin.val_rev] at he
    omega
  noncrossing a b hab hba hends := by
    simp only [Fin.revPerm_apply, Fin.lt_def, Fin.val_rev] at hends
    have ha := a.isLt
    have hb := b.isLt
    change a.val < b.val at hab
    omega

theorem identity_planar (n : ℕ) :
    ∃ Q : NCMatching (2*n), toMatching Q = identityMatching n := by
  refine ⟨identityNC n,?_⟩
  apply matching_ext
  rintro ⟨b,i⟩
  apply (boundaryEquiv n).injective
  change boundaryEquiv n ((boundaryEquiv n).symm
    ((identityNC n).partner (boundaryEquiv n (b,i)))) = boundaryEquiv n (!b,i)
  rw [Equiv.apply_symm_apply]
  apply Fin.ext
  change (Fin.revPerm (boundaryEquiv n (b,i))).val = (boundaryEquiv n (!b,i)).val
  simp only [Fin.revPerm_apply, Fin.val_rev]
  cases b <;> simp only [Bool.not_false, Bool.not_true, boundary_top, boundary_bottom] <;> omega

/-- Reconnect an adjacent pair while retaining the new adjacent cup. -/
def capReconnection {m : ℕ} (M : NCMatching (m+2)) (j : Fin (m+1)) : NCMatching (m+2) where
  partner := capConjugate M j
  involutive := capConjugate_involutive M j
  noFixed := capConjugate_noFixed M j
  noncrossing x y hxy hyx hends := by
    by_cases hxa : x = j.castSucc
    · subst x
      rw [capConjugate_left] at hyx
      have h₁ : j.val < y.val := hxy
      have h₂ : y.val < j.val+1 := hyx
      omega
    by_cases hxb : x = j.succ
    · subst x
      rw [capConjugate_right] at hyx
      have h₁ : j.val+1 < y.val := hxy
      have h₂ : y.val < j.val := hyx
      omega
    by_cases hya : y = j.castSucc
    · subst y
      rw [capConjugate_left] at hends
      have h₁ : j.val < (capConjugate M j x).val := hyx
      have h₂ : (capConjugate M j x).val < j.val+1 := hends
      omega
    by_cases hyb : y = j.succ
    · subst y
      rw [capConjugate_right] at hends
      have h₁ : j.val+1 < (capConjugate M j x).val := hyx
      have h₂ : (capConjugate M j x).val < j.val := hends
      omega
    rw [capConjugate_reconnect M j x hxa hxb] at hyx hends
    rw [capConjugate_reconnect M j y hya hyb] at hends
    exact reconnect_noncrossing M j x y hxa hxb hya hyb hxy hyx hends

private theorem swap_val {t : ℕ} (a b x : Fin t) :
    (Equiv.swap a b x).val = if x.val = a.val then b.val else
      if x.val = b.val then a.val else x.val := by
  simp only [Equiv.swap_apply_def, Fin.ext_iff]
  split_ifs <;> rfl

/-- Each standard cup-cap generator is a planar rectangle matching. -/
private theorem cupcap_planar_succ (m j : ℕ) (hj : j+1 < m+2) :
    ∃ Q : NCMatching (2*(m+2)), toMatching Q = cupcapMatching j hj := by
  let k : Fin (2*m+3) := ⟨j, by omega⟩
  let Q : NCMatching (2*(m+2)) := capReconnection (identityNC (m+2)) k
  refine ⟨Q, ?_⟩
  apply matching_ext
  rintro ⟨b,i⟩
  apply (boundaryEquiv (m+2)).injective
  change boundaryEquiv (m+2) ((boundaryEquiv (m+2)).symm
    (Q.partner (boundaryEquiv (m+2) (b,i)))) =
      boundaryEquiv (m+2) (cupcapMate j hj (b,i))
  rw [Equiv.apply_symm_apply]
  change capConjugate (identityNC (m+2)) k (boundaryEquiv (m+2) (b,i)) = _
  rw [capConjugate_apply]
  apply Fin.ext
  change (Equiv.swap k.succ (Fin.rev k.castSucc)
    (Fin.rev (Equiv.swap k.succ (Fin.rev k.castSucc) (boundaryEquiv (m+2) (b,i))))).val = _
  simp only [swap_val, Fin.val_rev, Fin.val_succ, Fin.val_castSucc, cupcapMate, k]
  cases b <;> simp only [Bool.not_false, Bool.not_true, boundary_top, boundary_bottom]
  all_goals split_ifs <;> simp only [boundary_top, boundary_bottom] <;> omega

/-- Standard generators are planar for every admissible strand index. -/
theorem cupcap_planar (n j : ℕ) (hj : j+1 < n) :
    ∃ Q : NCMatching (2*n), toMatching Q = cupcapMatching j hj := by
  obtain ⟨m,rfl⟩ : ∃ m, n = m+2 := ⟨n-2, by omega⟩
  exact cupcap_planar_succ m j hj

end D5.S3.Combinatorics.PerfectMatchings.PlanarSewing
