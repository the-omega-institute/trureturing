/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9StarPartnerWitness
   generality: I
   mirror-B: none(waiver:standalone-research-source)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Archive.Sensitivity]
   utility: none
   digest: An explicit connected balanced cubic partner of order ninety for the nine-cube star. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9StarPartnerBound
import D5.S3.Combinatorics.Graph.HypercubeCritical.Q9OrbitCertificateProbe

/-! The vertex and switching tables are the little-endian data from
`q9-star-partner-90-witness.json`. The spanning tree and the finite checks
certify the induced subgraph in the actual cube. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9StarPartnerWitness

open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open BalancedCriticalSpectrum (Q flip flip_adj IsBalanced)
open BalancedCubeComponentBoundary (directions)
open private directions_card mem_directions from
  D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeComponentBoundary
open Q9StarPartnerBound (Sstar)
open private eligible inStar from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9StarPartnerBound
open private adjacent_exists_flip from
  D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeGirth
open private selected_neighbor_card from
  D5.S3.Combinatorics.Graph.HypercubeCritical.SupportedEigenSaturation
open private huangMatrix from D5.S3.Combinatorics.Graph.HypercubeSubQuorum
open private matrix_flip_zero matrix_flip_succ from
  D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCriticalSpectrum

private def labels : List (BitVec 9) :=
[
  138, 170, 171, 174, 194, 200, 201, 202, 209, 210, 213, 214,
  215, 217, 219, 226, 227, 229, 231, 232, 235, 236, 237, 238,
  245, 246, 250, 251, 254, 266, 298, 299, 302, 322, 328, 329,
  330, 337, 338, 341, 342, 343, 345, 347, 354, 355, 357, 359,
  360, 363, 364, 365, 366, 373, 374, 378, 379, 382, 393, 394,
  401, 402, 405, 406, 407, 409, 410, 411, 421, 422, 423, 425,
  427, 429, 430, 437, 438, 457, 465, 466, 471, 475, 482, 487,
  488, 490, 493, 501, 502, 506]

private def negativeLabels : List (BitVec 9) :=
[
  138, 170, 171, 200, 201, 202, 210, 213, 217, 226, 227, 231,
  235, 246, 254, 302, 322, 337, 342, 343, 347, 357, 360, 364,
  365, 366, 373, 378, 379, 393, 402, 405, 409, 422, 423, 425,
  430, 438, 457, 466, 482, 487, 502]

/-- Each entry gives a child and the flip from that child to its parent. -/
private def treeSteps : List (BitVec 9 × Fin 9) :=
[
  (170, 5), (202, 6), (394, 8), (171, 0), (174, 2), (200, 1), (194, 3), (410, 4),
  (266, 7), (235, 6), (427, 8), (238, 6), (430, 8), (201, 0), (232, 5), (210, 4),
  (226, 5), (411, 0), (402, 3), (298, 5), (330, 6), (227, 3), (251, 4), (425, 1),
  (299, 7), (236, 1), (254, 4), (422, 3), (302, 7), (217, 4), (457, 8), (488, 8),
  (214, 2), (466, 8), (482, 8), (409, 1), (475, 6), (406, 2), (328, 1), (322, 3),
  (231, 2), (250, 0), (219, 5), (429, 2), (393, 5), (363, 6), (237, 0), (246, 3),
  (423, 0), (438, 4), (366, 6), (209, 3), (329, 7), (490, 1), (360, 7), (215, 0),
  (338, 7), (354, 7), (401, 3), (347, 7), (407, 0), (229, 1), (487, 8), (506, 8),
  (421, 3), (493, 6), (355, 3), (379, 4), (502, 8), (364, 1), (382, 4), (213, 2),
  (465, 8), (345, 4), (471, 8), (342, 2), (405, 2), (245, 4), (359, 7), (378, 7),
  (437, 4), (365, 7), (374, 7), (337, 7), (343, 7), (501, 8), (357, 1), (341, 2),
  (373, 7)]

private abbrev vertex : BitVec 9 ≃ Q 9 := cubeBitVec 9

private def toggle (a : BitVec 9) (i : Fin 9) : BitVec 9 :=
  a ^^^ BitVec.ofNat 9 (2 ^ i.val)

private theorem vertex_toggle (a : BitVec 9) (i : Fin 9) :
    vertex (toggle a i) = flip (vertex a) i :=
  cubeBitVec_xor_single a i

/-- The actual cube vertices given by the ninety little-endian labels. -/
def Partner : Finset (Q 9) := labels.toFinset.map vertex.toEmbedding

private theorem mem_partner (a : BitVec 9) : vertex a ∈ Partner ↔ a ∈ labels := by
  change vertex.toEmbedding a ∈ labels.toFinset.map vertex.toEmbedding ↔ a ∈ labels
  rw [Finset.mem_map]
  exact ⟨fun ⟨b, hb, he⟩ => List.mem_toFinset.mp (vertex.injective he ▸ hb),
    fun ha => ⟨a, List.mem_toFinset.mpr ha, rfl⟩⟩

/-- The literal witness has ninety vertices. -/
theorem partner_card : Partner.card = 90 := by
  rw [Partner, Finset.card_map]
  decide +kernel

private def treeCheck (seen : List (BitVec 9)) : List (BitVec 9 × Fin 9) → Bool
  | [] => labels.all fun a => seen.contains a
  | (a, i) :: rest =>
      labels.contains a && seen.contains (toggle a i) && treeCheck (a :: seen) rest

private abbrev partnerGraph := (hypercube 9).induce (Partner : Set (Q 9))

private def root : (Partner : Set (Q 9)) :=
  ⟨vertex 138, (mem_partner 138).mpr (by decide +kernel)⟩

private theorem treeCheck_reachable (seen : List (BitVec 9))
    (steps : List (BitVec 9 × Fin 9))
    (hseen : ∀ a ∈ seen, ∃ ha : vertex a ∈ Partner,
      partnerGraph.Reachable root ⟨vertex a, ha⟩)
    (hcheck : treeCheck seen steps = true) :
    ∀ a ∈ labels, ∃ ha : vertex a ∈ Partner, partnerGraph.Reachable root ⟨vertex a, ha⟩ := by
  induction steps generalizing seen with
  | nil =>
      intro a ha
      exact hseen a (List.contains_iff_mem.mp (List.all_eq_true.mp hcheck a ha))
  | cons step steps ih =>
      obtain ⟨a, i⟩ := step
      simp only [treeCheck, Bool.and_eq_true, List.contains_iff_mem] at hcheck
      obtain ⟨⟨ha, hparent⟩, hrest⟩ := hcheck
      obtain ⟨hp, hreach⟩ := hseen _ hparent
      have hchild := (mem_partner a).mpr ha
      have hedge : partnerGraph.Adj ⟨vertex (toggle a i), hp⟩ ⟨vertex a, hchild⟩ := by
        change (hypercube 9).Adj (vertex (toggle a i)) (vertex a)
        rw [vertex_toggle]
        exact (flip_adj _ _).symm
      apply ih (a :: seen) (hcheck := hrest)
      intro b hb
      rcases List.mem_cons.mp hb with rfl | hb
      · exact ⟨hchild, hreach.trans hedge.reachable⟩
      · exact hseen _ hb

set_option maxRecDepth 8192 in
/-- The spanning tree connects the whole actual induced subgraph. -/
theorem partner_connected : ((hypercube 9).induce (Partner : Set (Q 9))).Connected := by
  apply (SimpleGraph.connected_iff_exists_forall_reachable partnerGraph).mpr
  refine ⟨root, fun ⟨x, hx⟩ => ?_⟩
  obtain ⟨a, rfl⟩ := vertex.surjective x
  obtain ⟨_, h⟩ := treeCheck_reachable [138] treeSteps
    (by simp only [List.mem_singleton]; rintro _ rfl; exact ⟨root.property, .rfl⟩)
    (by decide +kernel) a ((mem_partner a).mp hx)
  exact h

set_option maxRecDepth 8192 in
private theorem cubicCertificate :
    ∀ a ∈ labels.toFinset, (Finset.univ.filter fun i => toggle a i ∈ labels).card = 3 := by
  decide +kernel

open Classical in
/-- Every vertex has degree three in the actual induced subgraph. -/
theorem partner_cubic :
    ((hypercube 9).induce (Partner : Set (Q 9))).IsRegularOfDegree 3 := by
  intro ⟨x, hx⟩
  obtain ⟨a, rfl⟩ := vertex.surjective x
  have hdirs : directions Partner (vertex a) =
      Finset.univ.filter (fun i => toggle a i ∈ labels) := by
    ext i
    simp [mem_directions, ← vertex_toggle, mem_partner]
  have hneigh : Partner.filter (fun y => (hypercube 9).Adj (vertex a) y) =
      (hypercube 9).neighborFinset (vertex a) ∩ Partner := by
    ext y
    simp [SimpleGraph.mem_neighborFinset, and_comm]
  rw [← selected_neighbor_card hx, ← hneigh, ← directions_card, hdirs]
  exact cubicCertificate a (List.mem_toFinset.mpr ((mem_partner a).mp hx))

private def rawSign (a : BitVec 9) : ℤ := if a ∈ negativeLabels then -1 else 1

/-- Multiplication by this gauge changes true-prefix signs to false-prefix signs. -/
private def gauge (a : BitVec 9) : ℤ :=
  (-1) ^ (∑ i : Fin 9, if vertex a i then i.val else 0)

private def falsePrefixSign : {n : ℕ} → Fin n → Q n → ℤ
  | 0, i, _ => Fin.elim0 i
  | _n + 1, i, x => Fin.cases 1
      (fun j => (if x 0 then 1 else -1) * falsePrefixSign j (Sensitivity.π x)) i

private theorem falsePrefixSign_cast {n : ℕ} (i : Fin n) (x : Q n) :
    (falsePrefixSign i x : ℝ) = huangMatrix n x (flip x i) := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
      induction i using Fin.cases with
      | zero =>
          rw [matrix_flip_zero]
          exact Int.cast_one
      | succ i =>
          rw [matrix_flip_succ]
          change ((↑((if x 0 then 1 else -1) * falsePrefixSign i (Sensitivity.π x)) : ℝ)) = _
          rw [Int.cast_mul, ih]
          cases x 0 <;> simp

set_option maxRecDepth 8192 in
private theorem signCertificate :
    ∀ a ∈ labels.toFinset, ∀ i : Fin 9, toggle a i ∈ labels →
      gauge a * gauge (toggle a i) = (-1 : ℤ) ^ i.val ∧
      falsePrefixSign i (vertex a) =
        (-1 : ℤ) ^ i.val * (rawSign a * rawSign (toggle a i)) := by
  decide +kernel

private noncomputable def switchingSign (x : Q 9) : ℝ :=
  ↑(gauge (vertex.symm x) * rawSign (vertex.symm x))

private theorem switchingSign_vertex (a : BitVec 9) :
    switchingSign (vertex a) = ↑(gauge a * rawSign a) := by
  simp [switchingSign]

/-- The selected edges are balanced in the project's real Huang matrix. -/
theorem partner_balanced : IsBalanced Partner := by
  refine ⟨switchingSign, ?_, ?_⟩
  · intro x _
    obtain ⟨a, rfl⟩ := vertex.surjective x
    rw [switchingSign_vertex]
    rcases neg_one_pow_eq_or ℤ (∑ i : Fin 9, if vertex a i then i.val else 0) with h | h <;>
      simp only [gauge, h, rawSign] <;> split <;> norm_num
  · intro x hx y hy hadj
    obtain ⟨a, rfl⟩ := vertex.surjective x
    obtain ⟨i, rfl⟩ := adjacent_exists_flip hadj
    rw [← vertex_toggle] at hy ⊢
    obtain ⟨hg, hs⟩ := signCertificate a (List.mem_toFinset.mpr ((mem_partner a).mp hx))
      i ((mem_partner _).mp hy)
    have he : falsePrefixSign i (vertex a) =
        (gauge a * rawSign a) * (gauge (toggle a i) * rawSign (toggle a i)) := by
      rw [hs, ← hg]
      ring
    rw [switchingSign_vertex, switchingSign_vertex, vertex_toggle, ← falsePrefixSign_cast]
    exact_mod_cast he

set_option maxRecDepth 8192 in
private theorem eligibleCertificate :
    ∀ a ∈ labels.toFinset, eligible (vertex a) = true := by
  decide +kernel

/-- The partner is disjoint from the fixed star and there are no cube edges between them. -/
theorem partner_separated : Disjoint Sstar Partner ∧
    ∀ s ∈ Sstar, ∀ d ∈ Partner, ¬ (hypercube 9).Adj s d := by
  have h (x : Q 9) (hx : x ∈ Partner) : eligible x = true := by
    obtain ⟨a, rfl⟩ := vertex.surjective x
    exact eligibleCertificate a (List.mem_toFinset.mpr ((mem_partner a).mp hx))
  constructor
  · refine Finset.disjoint_left.mpr (fun {x} hs hd => ?_)
    have he := (Bool.and_eq_true_iff.mp (h x hd)).1
    have hx : inStar x = true := (Finset.mem_filter.mp hs).2
    simp [hx] at he
  · intro s hs d hd hadj
    obtain ⟨i, rfl⟩ := adjacent_exists_flip hadj.symm
    have he := List.all_eq_true.mp (Bool.and_eq_true_iff.mp (h d hd)).2
      i (List.mem_finRange i)
    have hx : inStar (flip d i) = true := (Finset.mem_filter.mp hs).2
    simp [hx] at he

open Classical in
/-- A partner of order ninety gives the lower bound for this specific star. -/
theorem exists_connected_partner_90 :
    ∃ D : Finset (Q 9), D.card = 90 ∧
      ((hypercube 9).induce (D : Set (Q 9))).Connected ∧
      ((hypercube 9).induce (D : Set (Q 9))).IsRegularOfDegree 3 ∧
      IsBalanced D ∧ Disjoint Sstar D ∧
      (∀ s ∈ Sstar, ∀ d ∈ D, ¬ (hypercube 9).Adj s d) :=
  ⟨Partner, partner_card, partner_connected, partner_cubic, partner_balanced, partner_separated⟩

#print axioms partner_card
#print axioms partner_connected
#print axioms partner_cubic
#print axioms partner_balanced
#print axioms partner_separated
#print axioms exists_connected_partner_90

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9StarPartnerWitness
