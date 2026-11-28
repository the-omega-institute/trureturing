/- GID: D5/S3/Combinatorics/SpectralGraph/KeplerSupportTwo
   generality: G
   mirror-B: D5/B/S3/Combinatorics/SpectralGraph/KeplerSupportTwo
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Kepler's class sum counts supports, with two signed vectors per support. -/

import OmegaBuild.Commands
import Mathlib.Combinatorics.SimpleGraph.LapMatrix
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Data.Fintype.BigOperators

/-!
# Kepler's signed support-two eigenvectors

The graph is a Mathlib simple graph. The twin relation compares adjacency to every vertex
outside the pair. It relates each vertex to itself, so its quotient indexes the twin classes.
-/

compile_only_with_mathlib

open Matrix
open scoped BigOperators

namespace D5.S3.Combinatorics.SpectralGraph.KeplerSupportTwo

variable {V : Type*}

def Twins (G : SimpleGraph V) (u v : V) : Prop :=
  ∀ w, w ≠ u → w ≠ v → (G.Adj w u ↔ G.Adj w v)

private theorem twins_equivalence (G : SimpleGraph V) : Equivalence (Twins G) where
  refl _ _ _ _ := Iff.rfl
  symm huv w hwv hwu := (huv w hwu hwv).symm
  trans := by
    intro u v z huv hvz w hwu hwz
    by_cases hwv : w = v
    · subst w
      by_cases huz : u = z
      · subst z
        rfl
      calc
        G.Adj v u ↔ G.Adj u v := G.adj_comm _ _
        _ ↔ G.Adj u z := hvz u hwu.symm huz
        _ ↔ G.Adj z u := G.adj_comm _ _
        _ ↔ G.Adj z v := huv z (Ne.symm huz) hwz.symm
        _ ↔ G.Adj v z := G.adj_comm _ _
    · exact (huv w hwu hwv).trans (hvz w hwv hwz)

section SignedPair

variable [DecidableEq V]

def signedPair (u v : V) : V → ℝ :=
  Pi.single u 1 - Pi.single v 1

private theorem signedPair_apply (u v w : V) :
    signedPair u v w = (if w = u then 1 else 0) - (if w = v then 1 else 0) := by
  simp [signedPair, Pi.single_apply, eq_comm]

private theorem signedPair_left {u v : V} (huv : u ≠ v) : signedPair u v u = 1 := by
  simp [signedPair_apply, huv]

private theorem signedPair_right {u v : V} (huv : u ≠ v) : signedPair u v v = -1 := by
  simp [signedPair_apply, huv.symm]

private theorem signedPair_outside {u v w : V} (hwu : w ≠ u) (hwv : w ≠ v) :
    signedPair u v w = 0 := by
  simp [signedPair_apply, hwu, hwv]

private theorem signed_coordinates_iff (x : V → ℝ) (u v : V) (huv : u ≠ v) :
    (x u = 1 ∧ x v = -1 ∧ ∀ w, w ≠ u → w ≠ v → x w = 0) ↔ x = signedPair u v := by
  constructor
  · rintro ⟨hpos, hneg, hout⟩
    funext w
    by_cases hwu : w = u
    · simpa [hwu, signedPair_left huv] using hpos
    by_cases hwv : w = v
    · simpa [hwv, signedPair_right huv] using hneg
    · rw [hout w hwu hwv, signedPair_outside hwu hwv]
  · rintro rfl
    exact ⟨signedPair_left huv, signedPair_right huv, fun _ => signedPair_outside⟩

end SignedPair

section Matrix

variable [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Kepler, Definition 1.5. Mathlib's Laplacian is the degree matrix minus adjacency. -/
def bAlpha (α : ℝ) : Matrix V V ℝ :=
  α • G.adjMatrix ℝ + (1 - α) • G.lapMatrix ℝ

private theorem bAlpha_expanded (α : ℝ) :
    bAlpha G α = (1 - α) • G.degMatrix ℝ + (2 * α - 1) • G.adjMatrix ℝ := by
  ext i j
  simp only [bAlpha, SimpleGraph.lapMatrix, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.sub_apply]
  ring

private theorem bAlpha_mulVec_apply (α : ℝ) (x : V → ℝ) (w : V) :
    (bAlpha G α *ᵥ x) w = (1 - α) * (G.degree w : ℝ) * x w +
      (2 * α - 1) * (G.adjMatrix ℝ *ᵥ x) w := by
  rw [bAlpha_expanded, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, G.degMatrix_mulVec_apply]
  ring

private theorem bAlpha_signedPair_apply (α : ℝ) (u v w : V) :
    (bAlpha G α *ᵥ signedPair u v) w =
      (1 - α) * (G.degree w : ℝ) * signedPair u v w +
        (2 * α - 1) * ((if G.Adj w u then 1 else 0) - (if G.Adj w v then 1 else 0)) := by
  rw [bAlpha_mulVec_apply]
  simp only [signedPair, Matrix.mulVec_sub, Matrix.mulVec_single_one, Pi.sub_apply,
    Matrix.col_apply, SimpleGraph.adjMatrix_apply]

private theorem bAlpha_signedPair_outside (α : ℝ) {u v w : V} (hwu : w ≠ u) (hwv : w ≠ v) :
    (bAlpha G α *ᵥ signedPair u v) w =
      (2 * α - 1) * ((if G.Adj w u then 1 else 0) - (if G.Adj w v then 1 else 0)) := by
  rw [bAlpha_signedPair_apply, signedPair_outside hwu hwv, mul_zero, zero_add]

omit [DecidableEq V] in
private theorem twins_degree_eq {u v : V} (h : Twins G u v) : G.degree u = G.degree v := by
  classical
  by_cases huv : u = v
  · subst v
    rfl
  have heq (w : V) : G.Adj u w ↔ G.Adj v (Equiv.swap u v w) := by
    by_cases hwu : w = u
    · subst w
      simp [Equiv.swap_apply_left]
    by_cases hwv : w = v
    · subst w
      simpa only [Equiv.swap_apply_right] using G.adj_comm u v
    rw [Equiv.swap_apply_of_ne_of_ne hwu hwv]
    exact (G.adj_comm u w).trans ((h w hwu hwv).trans (G.adj_comm w v))
  have hs (w : V) :
      (if G.Adj u w then 1 else 0 : ℕ) =
        (if G.Adj v (Equiv.swap u v w) then 1 else 0) := by simp only [heq w]
  calc
    G.degree u = ∑ w, if G.Adj u w then 1 else 0 := G.degree_eq_sum_if_adj u
    _ = ∑ w, if G.Adj v (Equiv.swap u v w) then 1 else 0 := Finset.sum_congr rfl fun w _ => hs w
    _ = ∑ w, if G.Adj v w then 1 else 0 :=
      Equiv.sum_comp (Equiv.swap u v) (fun w => if G.Adj v w then (1 : ℕ) else 0)
    _ = G.degree v := (G.degree_eq_sum_if_adj (R := ℕ) v).symm

def pairEigenvalue (α : ℝ) (u v : V) : ℝ :=
  (1 - α) * (G.degree u : ℝ) - (2 * α - 1) * (if G.Adj u v then 1 else 0)

private theorem bAlpha_signedPair_left (α : ℝ) {u v : V} (huv : u ≠ v) :
    (bAlpha G α *ᵥ signedPair u v) u = pairEigenvalue G α u v := by
  rw [bAlpha_signedPair_apply, signedPair_left huv, pairEigenvalue]
  simp
  ring

private theorem bAlpha_signedPair_right (α : ℝ) {u v : V} (huv : u ≠ v) :
    (bAlpha G α *ᵥ signedPair u v) v = -pairEigenvalue G α v u := by
  rw [bAlpha_signedPair_apply, signedPair_right huv, pairEigenvalue]
  simp
  ring

def classSetoid (α : ℝ) : Setoid V where
  r := if α = 1 / 2 then fun u v => G.degree u = G.degree v else Twins G
  iseqv := by
    split
    · exact ⟨fun _ => rfl, Eq.symm, Eq.trans⟩
    · exact twins_equivalence G

omit [DecidableEq V] in
private theorem classSetoid_rel_half {α : ℝ} (h : α = 1 / 2) (u v : V) :
    (classSetoid G α).r u v ↔ G.degree u = G.degree v := by
  change (if α = 1 / 2 then (fun a b => G.degree a = G.degree b) else Twins G) u v ↔ _
  rw [ite_eq_left h]

omit [DecidableEq V] in
private theorem classSetoid_rel_ne_half {α : ℝ} (h : α ≠ 1 / 2) (u v : V) :
    (classSetoid G α).r u v ↔ Twins G u v := by
  change (if α = 1 / 2 then (fun a b => G.degree a = G.degree b) else Twins G) u v ↔ _
  rw [ite_eq_right h]

private theorem signedPair_equation_iff (α eigenvalue : ℝ) {u v : V} (huv : u ≠ v) :
    bAlpha G α *ᵥ signedPair u v = eigenvalue • signedPair u v ↔
      (classSetoid G α).r u v ∧ eigenvalue = pairEigenvalue G α u v := by
  have edge_symm :
      (if G.Adj u v then 1 else 0 : ℝ) = (if G.Adj v u then 1 else 0) := by
    simp only [G.adj_comm u v]
  constructor
  · intro heigenvalue
    have hleft := congrFun heigenvalue u
    simp only [bAlpha_signedPair_left G α huv, Pi.smul_apply, smul_eq_mul,
      signedPair_left huv, mul_one] at hleft
    refine ⟨?_, hleft.symm⟩
    by_cases hα : α = 1 / 2
    · rw [classSetoid_rel_half G hα]
      have hright := congrFun heigenvalue v
      simp only [bAlpha_signedPair_right G α huv, Pi.smul_apply, smul_eq_mul,
        signedPair_right huv] at hright
      have hd : (G.degree u : ℝ) = (G.degree v : ℝ) := by
        simp [pairEigenvalue, hα] at hleft hright
        linarith
      exact_mod_cast hd
    · rw [classSetoid_rel_ne_half G hα]
      intro w hwu hwv
      have hout := congrFun heigenvalue w
      simp only [bAlpha_signedPair_outside G α hwu hwv, signedPair_outside hwu hwv,
        Pi.smul_apply, smul_eq_mul, mul_zero] at hout
      have hcoeff : 2 * α - 1 ≠ 0 := by
        intro hz
        apply hα
        linarith
      have hdiff := (mul_eq_zero.mp hout).resolve_left hcoeff
      by_cases h₁ : G.Adj w u <;> by_cases h₂ : G.Adj w v <;>
        simp_all
  · rintro ⟨h, rfl⟩
    have hd : G.degree u = G.degree v := by
      by_cases hα : α = 1 / 2
      · exact (classSetoid_rel_half G hα u v).mp h
      · exact twins_degree_eq G ((classSetoid_rel_ne_half G hα u v).mp h)
    funext w
    by_cases hwu : w = u
    · subst w
      simp [bAlpha_signedPair_left G α huv, signedPair_left huv]
    by_cases hwv : w = v
    · subst w
      simp [bAlpha_signedPair_right G α huv, signedPair_right huv, pairEigenvalue, hd, edge_symm]
    simp only [bAlpha_signedPair_outside G α hwu hwv, signedPair_outside hwu hwv,
      Pi.smul_apply, smul_eq_mul, mul_zero]
    by_cases hα : α = 1 / 2
    · norm_num [hα]
    · simp only [((classSetoid_rel_ne_half G hα u v).mp h) w hwu hwv, sub_self, mul_zero]

private theorem signedPair_eigen_iff (α : ℝ) {u v : V} (huv : u ≠ v) :
    (∃ eigenvalue : ℝ, bAlpha G α *ᵥ signedPair u v = eigenvalue • signedPair u v) ↔
      (classSetoid G α).r u v := by
  constructor
  · rintro ⟨eigenvalue, h⟩
    exact ((signedPair_equation_iff G α eigenvalue huv).mp h).1
  · intro h
    exact ⟨_, (signedPair_equation_iff G α _ huv).mpr ⟨h, rfl⟩⟩

/-- The literal coordinate condition of Remark 4.3, with an existential real eigenvalue. -/
def IsSignedEigenvector (α : ℝ) (x : V → ℝ) : Prop :=
  (∃ u v : V, u ≠ v ∧ x u = 1 ∧ x v = -1 ∧ ∀ w, w ≠ u → w ≠ v → x w = 0) ∧
    ∃ eigenvalue : ℝ, bAlpha G α *ᵥ x = eigenvalue • x

end Matrix

/-- The graph consisting of pairs of distinct vertices in the same equivalence class. -/
def classGraph (s : Setoid V) : SimpleGraph V where
  Adj u v := u ≠ v ∧ s.r u v
  symm := ⟨fun _ _ h => ⟨h.1.symm, s.symm h.2⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- The vertices of a quotient class. -/
abbrev Class (s : Setoid V) (q : Quotient s) := {v : V // Quotient.mk s v = q}

private def classDartsEquiv (s : Setoid V) :
    (classGraph s).Dart ≃ (Σ q : Quotient s, (⊤ : SimpleGraph (Class s q)).Dart) where
  toFun d :=
    ⟨Quotient.mk s d.fst,
      ⟨(⟨d.fst, rfl⟩, ⟨d.snd, (Quotient.sound d.adj.2).symm⟩),
        fun h => d.adj.1 (congrArg Subtype.val h)⟩⟩
  invFun p :=
    ⟨(p.2.fst.val, p.2.snd.val),
      ⟨fun h => p.2.adj (Subtype.ext h),
        Quotient.exact (p.2.fst.property.trans p.2.snd.property.symm)⟩⟩
  left_inv d := SimpleGraph.Dart.ext _ _ rfl
  right_inv := by
    rintro ⟨q, ⟨⟨⟨u, hu⟩, ⟨v, hv⟩⟩, h⟩⟩
    subst q
    rfl

open Classical in
/-- Sum of the binomial numbers of pairs in the quotient classes. -/
noncomputable def classPairSum [Fintype V] (s : Setoid V) : ℕ :=
  ∑ q : Quotient s, (Nat.card (Class s q)).choose 2

private theorem card_classGraph_edges [Fintype V] (s : Setoid V) :
    Nat.card (classGraph s).edgeSet = classPairSum s := by
  classical
  have h : 2 * Nat.card (classGraph s).edgeSet = 2 * classPairSum s := calc
    _ = Fintype.card (classGraph s).Dart := by
      rw [Nat.card_eq_fintype_card, SimpleGraph.dart_card_eq_twice_card_edges,
        SimpleGraph.card_edgeSet]
    _ = Fintype.card (Σ q : Quotient s, (⊤ : SimpleGraph (Class s q)).Dart) :=
      Fintype.card_congr (classDartsEquiv s)
    _ = ∑ q : Quotient s, Fintype.card (⊤ : SimpleGraph (Class s q)).Dart :=
      Fintype.card_sigma
    _ = 2 * classPairSum s := by
      rw [classPairSum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q _
      rw [Nat.card_eq_fintype_card, SimpleGraph.dart_card_eq_twice_card_edges,
        SimpleGraph.card_edgeFinset_top_eq_card_choose_two]
  omega

section Count

variable [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

abbrev SignedEigenvectors (α : ℝ) := {x : V → ℝ // IsSignedEigenvector G α x}

abbrev SupportPairs (α : ℝ) := (classGraph (classSetoid G α)).edgeSet

/-- Admissible unordered supports, represented by Mathlib's unordered pairs. -/
private theorem mem_supportPairs_iff (α : ℝ) (u v : V) :
    s(u, v) ∈ (classGraph (classSetoid G α)).edgeSet ↔
      u ≠ v ∧ ∃ eigenvalue : ℝ, bAlpha G α *ᵥ signedPair u v = eigenvalue • signedPair u v := by
  rw [SimpleGraph.mem_edgeSet]
  change (u ≠ v ∧ (classSetoid G α).r u v) ↔ _
  exact and_congr_right fun huv => (signedPair_eigen_iff G α huv).symm

/-- The realization sends a dart (u,v) of the class graph to e_u - e_v. -/
noncomputable def directedRealization (α : ℝ) :
    (classGraph (classSetoid G α)).Dart ≃ SignedEigenvectors G α :=
  Equiv.ofBijective
    (fun d => ⟨signedPair d.fst d.snd,
      ⟨⟨d.fst, d.snd, d.adj.1, (signed_coordinates_iff _ _ _ d.adj.1).mpr rfl⟩,
        ((mem_supportPairs_iff G α d.fst d.snd).mp d.edge_mem).2⟩⟩) <| by
    constructor
    · intro d e h
      have hv := congrArg Subtype.val h
      have hfst : d.fst = e.fst := by
        have hpos : signedPair e.fst e.snd d.fst = 1 :=
          (congrFun hv d.fst).symm.trans (signedPair_left d.adj.1)
        by_contra hne
        by_cases hsnd : d.fst = e.snd <;> norm_num [signedPair_apply, hne, hsnd] at hpos
      have hsnd : d.snd = e.snd := by
        have hneg : signedPair e.fst e.snd d.snd = -1 :=
          (congrFun hv d.snd).symm.trans (signedPair_right d.adj.1)
        by_contra hne
        by_cases hfirst : d.snd = e.fst <;> norm_num [signedPair_apply, hne, hfirst] at hneg
      exact SimpleGraph.Dart.ext _ _ (Prod.ext hfst hsnd)
    · rintro ⟨x, ⟨⟨u, v, huv, hcoords⟩, heigen⟩⟩
      have hx := (signed_coordinates_iff _ _ _ huv).mp hcoords
      subst x
      have hedge := (mem_supportPairs_iff G α u v).mpr ⟨huv, heigen⟩
      rw [SimpleGraph.mem_edgeSet] at hedge
      exact ⟨⟨(u, v), hedge⟩, rfl⟩

omit [DecidableEq V] in
private theorem card_supportPairs (α : ℝ) :
    Nat.card (SupportPairs G α) = classPairSum (classSetoid G α) :=
  card_classGraph_edges _

private theorem card_signedEigenvectors_eq_twice (α : ℝ) :
    Nat.card (SignedEigenvectors G α) = 2 * Nat.card (SupportPairs G α) := by
  classical
  rw [← Nat.card_congr (directedRealization G α)]
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
    SimpleGraph.dart_card_eq_twice_card_edges, SimpleGraph.card_edgeSet]

/-- Both graphwise counts in Remark 4.3, for every real parameter. -/
theorem graphwise_count (α : ℝ) :
    Nat.card (SupportPairs G α) = classPairSum (classSetoid G α) ∧
    Nat.card (SignedEigenvectors G α) = 2 * classPairSum (classSetoid G α) :=
  ⟨card_supportPairs G α, (card_signedEigenvectors_eq_twice G α).trans
    (congrArg (2 * ·) (card_supportPairs G α))⟩

end Count

end D5.S3.Combinatorics.SpectralGraph.KeplerSupportTwo
