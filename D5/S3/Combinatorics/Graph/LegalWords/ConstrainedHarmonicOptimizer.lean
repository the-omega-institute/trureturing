/- GID: D5/S3/Combinatorics/Graph/LegalWords/ConstrainedHarmonicOptimizer
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/LegalWords/ConstrainedHarmonicOptimizer
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.Convex.StdSimplex, mathlib/module/Mathlib.Analysis.Calculus.Deriv.Slope]
   utility: none
   digest: Complete native harmonic-edge optimization on a positive normalized simplex. -/

import D5.S3.Combinatorics.Graph.LegalWords.EdgeCount
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Topology.Order.Compact

set_option autoImplicit false

noncomputable section

namespace D5.S3.Combinatorics.Graph.LegalWords.ConstrainedHarmonicOptimizer

open scoped BigOperators Classical Topology
open D5.S1.Words.AdmissibleWords.AdmissibleCount
open D5.S3.Quantum.FockSpace.ForbiddenNeighbourDeterminant
open D5.S3.Combinatorics.Graph.LegalWordDegree
open D5.S3.Combinatorics.Graph.LegalWords.EdgeCount
open Set Filter

/-- Real division includes the zero-zero convention. -/
noncomputable def harmonic (s t : ℝ) : ℝ := s * t / (s + t)

private theorem harmonic_symm (s t : ℝ) : harmonic s t = harmonic t s := by
  simp [harmonic, mul_comm, add_comm]

/-- The sum over the complete original unordered edge finset. -/
noncomputable def objective (n : ℕ) (p : Legal n → ℝ) : ℝ :=
  ∑ e ∈ (legalWordGraph n).edgeFinset,
    Sym2.lift ⟨fun a b => harmonic (p a) (p b), fun _ _ => harmonic_symm _ _⟩ e

/-- The entire normalized epsilon simplex; no insertion inequality is imposed. -/
def epsilonSimplex (n : ℕ) (ε : ℝ) : Set (Legal n → ℝ) :=
  {p | (∀ b, ε ≤ p b) ∧ ∑ b, p b = 1}

/-- Neighbouring positions belong to the open path, without cyclic wraparound. -/
def Near {n : ℕ} (i j : Fin n) : Prop := i.val + 1 = j.val ∨ j.val + 1 = i.val

noncomputable def positionDegree {n : ℕ} (i : Fin n) : ℕ :=
  (Finset.univ.filter (Near i)).card

noncomputable def insertionLower {n : ℕ} (i : Fin n) : ℝ :=
  (4 - (positionDegree i : ℝ)) / (4 + (positionDegree i : ℝ))

def InsertionBounds (n : ℕ) (p : Legal n → ℝ) : Prop :=
  ∀ e : Marked n,
    insertionLower e.2.val * p (erase e.1 e.2.val) ≤ p e.1 ∧
    p e.1 ≤ p (erase e.1 e.2.val)

private theorem objective_unordered (n : ℕ) (p : Legal n → ℝ) :
    objective n p = ∑ e : Marked n,
      harmonic (p (erase e.1 e.2.val)) (p e.1) := by
  unfold objective
  classical
  rw [← Finset.sum_coe_sort]
  have he := Equiv.sum_comp (Equiv.ofBijective (deletionEdge n) (deletionEdge_bijective n))
    (fun e : ↥((legalWordGraph n).edgeFinset) =>
      Sym2.lift ⟨fun a b => harmonic (p a) (p b), fun a b => harmonic_symm _ _⟩ e.val)
  simpa [deletionEdge, harmonic_symm] using he.symm

theorem adj_iff (n : ℕ) (a b : Legal n) :
    (legalWordGraph n).Adj a b ↔
      ∃ i : Fin n, a.val i ≠ b.val i ∧ ∀ j, j ≠ i → a.val j = b.val j := by
  classical
  change (Finset.univ.filter (fun i => a.val i ≠ b.val i)).card = 1 ↔ _
  rw [Finset.card_eq_one]
  constructor
  · rintro ⟨i, hi⟩
    have hm (j : Fin n) : a.val j ≠ b.val j ↔ j = i := by
      simpa using Finset.ext_iff.mp hi j
    refine ⟨i, (hm i).mpr rfl, ?_⟩
    intro j hj
    exact not_ne_iff.mp (fun h => hj ((hm j).mp h))
  · rintro ⟨i, hi, haway⟩
    refine ⟨i, ?_⟩
    ext j
    by_cases hj : j = i
    · subst j; simp [hi]
    · simp [hj, haway j hj]

private theorem erase_at {n : ℕ} (b : Legal n) (i : Fin n) :
    (erase b i).val i = false := by simp [erase]

private theorem erase_away {n : ℕ} (b : Legal n) (i j : Fin n) (hj : j ≠ i) :
    (erase b i).val j = b.val j := by simp [erase, hj]

private theorem upper_ne_lower {n : ℕ} (e : Marked n) : e.1 ≠ erase e.1 e.2.val := by
  intro h
  have hv := congrArg (fun b : Legal n => b.val e.2.val) h
  simpa [erase, e.2.property] using hv

private theorem erased_flippable {n : ℕ} (e : Marked n) :
    FlippableZero (erase e.1 e.2.val).val e.2.val := by
  refine ⟨erase_at _ _, ?_⟩
  intro j hj
  have hji : j ≠ e.2.val := by intro he; subst j; omega
  rw [erase_away _ _ _ hji]
  have hlegal := (adm_iff_no_adjacent_true n e.1.val).mp e.1.property
  rcases hj with hj | hj
  · have := hlegal j e.2.val hj
    simpa [e.2.property] using this
  · have := hlegal e.2.val j hj
    simpa [e.2.property] using this

private def insert {n : ℕ} (b : Legal n) (i : Fin n)
    (hi : FlippableZero b.val i) : Legal n :=
  ⟨Function.update b.val i true, by
    rw [adm_iff_no_adjacent_true]
    intro j k hjk
    by_cases hj : j = i
    · subst j
      right
      have hki : k ≠ i := by intro h; subst k; omega
      simpa [hki] using hi.2 k (Or.inr hjk)
    by_cases hk : k = i
    · subst k
      left
      simpa [hj] using hi.2 j (Or.inl hjk)
    simpa [hj, hk] using (adm_iff_no_adjacent_true n b.val).mp b.property j k hjk⟩

private theorem insert_at {n : ℕ} (b : Legal n) (i : Fin n) (h) :
    (insert b i h).val i = true := by simp [insert]

private theorem erase_insert {n : ℕ} (b : Legal n) (i : Fin n) (hi) :
    erase (insert b i hi) i = b := by
  apply Subtype.ext
  funext j
  by_cases hj : j = i
  · subst j; simp [erase, hi.1]
  · simp [erase, insert, hj]

private theorem insert_erase {n : ℕ} (e : Marked n) :
    insert (erase e.1 e.2.val) e.2.val (erased_flippable e) = e.1 := by
  apply Subtype.ext
  funext j
  by_cases hj : j = e.2.val
  · subst j; simp [insert, e.2.property]
  · simp [erase, insert, hj]

private theorem upper_neighbor_retains {n : ℕ} (e : Marked n) (z : Legal n)
    (hz : (legalWordGraph n).Adj e.1 z) (hne : z ≠ erase e.1 e.2.val) :
    z.val e.2.val = true := by
  obtain ⟨j, hj, haway⟩ := (adj_iff n e.1 z).mp hz
  by_cases hji : j = e.2.val
  · subst j
    have hzi : z.val e.2.val = false := by
      cases h : z.val e.2.val <;> simp_all [e.2.property]
    have he : z = erase e.1 e.2.val := by
      apply Subtype.ext
      funext k
      by_cases hk : k = e.2.val
      · subst k; simpa [erase] using hzi
      · simpa [erase, hk] using (haway k hk).symm
    exact (hne he).elim
  · exact (haway _ (Ne.symm hji)).symm.trans e.2.property

private theorem erase_upper_neighbor {n : ℕ} (e : Marked n) (z : Legal n)
    (hz : (legalWordGraph n).Adj e.1 z) (hne : z ≠ erase e.1 e.2.val) :
    (legalWordGraph n).Adj (erase e.1 e.2.val) (erase z e.2.val) := by
  obtain ⟨j, hj, haway⟩ := (adj_iff n e.1 z).mp hz
  have hji : j ≠ e.2.val := by
    intro h
    subst j
    rw [e.2.property, upper_neighbor_retains e z hz hne] at hj
    exact hj rfl
  apply (adj_iff n _ _).mpr
  refine ⟨j, ?_, ?_⟩
  · simpa [erase, hji] using hj
  · intro k hk
    by_cases hki : k = e.2.val
    · subst k; simp [erase]
    · simpa [erase, hki] using haway k hk

private theorem insert_lower_neighbor {n : ℕ} (e : Marked n) (w : Legal n)
    (hw : (legalWordGraph n).Adj (erase e.1 e.2.val) w)
    (hi : FlippableZero w.val e.2.val) :
    (legalWordGraph n).Adj e.1 (insert w e.2.val hi) := by
  obtain ⟨j, hj, haway⟩ := (adj_iff n (erase e.1 e.2.val) w).mp hw
  have hji : j ≠ e.2.val := by
    intro h; subst j
    simpa [erase, hi.1] using hj
  apply (adj_iff n _ _).mpr
  refine ⟨j, ?_, ?_⟩
  · simpa [erase, insert, hji] using hj
  · intro k hk
    by_cases hki : k = e.2.val
    · subst k; simp [insert, e.2.property]
    · simpa [erase, insert, hki] using haway k hk

private abbrev PairedLower {n : ℕ} (e : Marked n) :=
  {w : Legal n // (legalWordGraph n).Adj (erase e.1 e.2.val) w ∧
    FlippableZero w.val e.2.val}

private abbrev PairedUpper {n : ℕ} (e : Marked n) :=
  {z : Legal n // (legalWordGraph n).Adj e.1 z ∧ z ≠ erase e.1 e.2.val}

private def neighborPairing {n : ℕ} (e : Marked n) : PairedLower e ≃ PairedUpper e where
  toFun w := ⟨insert w.val e.2.val w.property.2,
    insert_lower_neighbor e w.val w.property.1 w.property.2, by
      intro he
      have := congrArg (fun b : Legal n => b.val e.2.val) he
      simp [insert, erase] at this⟩
  invFun z := ⟨erase z.val e.2.val,
    erase_upper_neighbor e z.val z.property.1 z.property.2,
    erased_flippable ⟨z.val, ⟨e.2.val,
      upper_neighbor_retains e z.val z.property.1 z.property.2⟩⟩⟩
  left_inv w := Subtype.ext (erase_insert w.val e.2.val w.property.2)
  right_inv z := Subtype.ext (insert_erase
    ⟨z.val, ⟨e.2.val, upper_neighbor_retains e z.val z.property.1 z.property.2⟩⟩)

private theorem lower_neighbor_partition {n : ℕ} (e : Marked n) (w : Legal n)
    (hw : (legalWordGraph n).Adj (erase e.1 e.2.val) w) :
    w = e.1 ∨ FlippableZero w.val e.2.val ∨
      ∃ j : Fin n, Near e.2.val j ∧
        ∃ h : FlippableZero (erase e.1 e.2.val).val j,
          w = insert (erase e.1 e.2.val) j h := by
  obtain ⟨j, hj, haway⟩ := (adj_iff n (erase e.1 e.2.val) w).mp hw
  by_cases hji : j = e.2.val
  · left
    subst j
    apply Subtype.ext
    funext k
    by_cases hk : k = e.2.val
    · subst k
      have hwi : w.val e.2.val = true := by
        cases h : w.val e.2.val <;> simp_all [erase]
      exact hwi.trans e.2.property.symm
    · simpa [erase, hk] using (haway k hk).symm
  · by_cases hn : Near e.2.val j
    · right; right
      have hzj : (erase e.1 e.2.val).val j = false := by
        rcases hn with hn | hn
        · exact (erased_flippable e).2 j (Or.inr hn)
        · exact (erased_flippable e).2 j (Or.inl hn)
      have hwj : w.val j = true := by cases h : w.val j <;> simp_all
      have hfj : FlippableZero (erase e.1 e.2.val).val j := by
        refine ⟨hzj, ?_⟩
        intro k hk
        have hkj : k ≠ j := by intro he; subst k; omega
        rw [haway k hkj]
        have hl := (adm_iff_no_adjacent_true n w.val).mp w.property
        rcases hk with hk | hk
        · simpa [hwj] using hl k j hk
        · simpa [hwj] using hl j k hk
      refine ⟨j, hn, hfj, ?_⟩
      apply Subtype.ext
      funext k
      by_cases hk : k = j
      · subst k; simp [insert, hwj]
      · simpa [insert, hk] using (haway k hk).symm
    · right; left
      refine ⟨?_, ?_⟩
      · exact (haway _ (Ne.symm hji)).symm.trans (erase_at _ _)
      · intro k hk
        have hkj : k ≠ j := by
          intro h; subst k
          exact hn (by rcases hk with hk | hk
                       · exact Or.inr hk
                       · exact Or.inl hk)
        exact (haway k hkj).symm.trans ((erased_flippable e).2 k hk)

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private abbrev realAdd : AddCommGroup ℝ := Real.normedAddCommGroup.toAddCommGroup
private abbrev realNormed : NormedAddCommGroup ℝ := Real.normedAddCommGroup
private abbrev realSpace : NormedSpace ℝ ℝ := NormedAlgebra.toNormedSpace ℝ
private abbrev realModule : Module ℝ ℝ := (NormedAlgebra.toNormedSpace ℝ).toModule
attribute [local instance 2000] realAdd realNormed realSpace realModule

private theorem harmonic_hasDerivAt (s t a b : ℝ) (hs : 0 < s) (ht : 0 < t) :
    HasDerivAt (fun u : ℝ => harmonic (s + u * a) (t + u * b))
      (a * (t / (s + t)) ^ 2 + b * (s / (s + t)) ^ 2) 0 := by
  have hsa : HasDerivAt (fun u : ℝ => s + u * a) a 0 := by
    convert! (hasDerivAt_const (0 : ℝ) s).add ((hasDerivAt_id (0 : ℝ)).mul_const a) using 1 <;> first | rfl | ring
  have htb : HasDerivAt (fun u : ℝ => t + u * b) b 0 := by
    convert! (hasDerivAt_const (0 : ℝ) t).add ((hasDerivAt_id (0 : ℝ)).mul_const b) using 1 <;> first | rfl | ring
  have hne : s + t ≠ 0 := ne_of_gt (add_pos hs ht)
  have hd := (hsa.mul htb).div (hsa.add htb) (by simpa using hne)
  have he : a * (t / (s + t)) ^ 2 + b * (s / (s + t)) ^ 2 =
      ((a * t + s * b) * (s + t) - s * t * (a + b)) / (s + t) ^ 2 := by
    field_simp [hne]
    <;> ring
  rw [he]
  convert! hd using 1 <;> first
    | rfl
    | simp only [Pi.add_apply, Pi.mul_apply, zero_mul, add_zero]

/-- A mass transfer on the original word carrier. -/
noncomputable def transfer {n : ℕ} (p : Legal n → ℝ) (donor receiver : Legal n)
    (u : ℝ) : Legal n → ℝ :=
  fun b => p b + u * ((if b = receiver then 1 else 0) - (if b = donor then 1 else 0))

private theorem transfer_zero {n : ℕ} (p : Legal n → ℝ) (donor receiver : Legal n) :
    transfer p donor receiver 0 = p := by
  funext b; simp [transfer]

private theorem transfer_feasible {n : ℕ} (ε : ℝ) (p : Legal n → ℝ)
    (hp : p ∈ epsilonSimplex n ε) (donor receiver : Legal n) (hne : donor ≠ receiver)
    (u : ℝ) (hu : 0 ≤ u) (hsmall : u ≤ p donor - ε) :
    transfer p donor receiver u ∈ epsilonSimplex n ε := by
  constructor
  · intro b
    by_cases hb : b = donor
    · subst b; simp [transfer, hne]; linarith
    by_cases hc : b = receiver
    · subst b
      simp [transfer, Ne.symm hne]
      have := hp.1 receiver
      linarith
    · simpa [transfer, hb, hc] using hp.1 b
  · simp [transfer, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      ← Finset.mul_sum, hp.2]

private theorem epsilon_nonempty (n : ℕ) (ε : ℝ)
    (hsmall : ε ≤ 1 / (Fintype.card (Legal n) : ℝ)) :
    (epsilonSimplex n ε).Nonempty := by
  have hz : Nonempty (Legal n) := ⟨⟨fun _ => false, by
    rw [adm_iff_no_adjacent_true]; intro j k _; simp⟩⟩
  letI := hz
  refine ⟨fun _ => 1 / (Fintype.card (Legal n) : ℝ), ?_, ?_⟩
  · intro _; exact hsmall
  · simp [Fintype.card_ne_zero]

private theorem epsilon_compact (n : ℕ) (ε : ℝ) (hε : 0 ≤ ε) :
    IsCompact (epsilonSimplex n ε) := by
  have he : epsilonSimplex n ε = stdSimplex ℝ (Legal n) ∩
      ⋂ b : Legal n, {p : Legal n → ℝ | ε ≤ p b} := by
    ext p
    simp only [epsilonSimplex, stdSimplex, mem_setOf_eq, mem_inter_iff, mem_iInter]
    constructor
    · rintro ⟨hp, hsum⟩; exact ⟨⟨fun b => hε.trans (hp b), hsum⟩, hp⟩
    · rintro ⟨⟨_, hsum⟩, hp⟩; exact ⟨hp, hsum⟩
  rw [he]
  exact (isCompact_stdSimplex ℝ (Legal n)).inter_right
    (isClosed_iInter fun b => isClosed_le continuous_const (continuous_apply b))

private theorem objective_continuousOn (n : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ContinuousOn (objective n) (epsilonSimplex n ε) := by
  have he : objective n = fun p => ∑ e : Marked n,
      harmonic (p (erase e.1 e.2.val)) (p e.1) := funext (objective_unordered n)
  rw [he]
  unfold harmonic
  apply continuousOn_finset_sum
  intro e _
  apply ((continuous_apply (erase e.1 e.2.val)).continuousOn.mul
    (continuous_apply e.1).continuousOn).div
    ((continuous_apply (erase e.1 e.2.val)).continuousOn.add
      (continuous_apply e.1).continuousOn)
  intro p hp
  exact ne_of_gt (add_pos (hε.trans_le (hp.1 _)) (hε.trans_le (hp.1 _)))

private theorem exists_constrained_optimizer (n : ℕ) (ε : ℝ) (hε : 0 < ε)
    (hsmall : ε ≤ 1 / (Fintype.card (Legal n) : ℝ)) :
    ∃ p, p ∈ epsilonSimplex n ε ∧ IsMaxOn (objective n) (epsilonSimplex n ε) p :=
  (epsilon_compact n ε hε.le).exists_isMaxOn (epsilon_nonempty n ε hsmall)
    (objective_continuousOn n ε hε)

private abbrev Incident {n : ℕ} (b : Legal n) :=
  {e : Marked n // b = e.1 ∨ b = erase e.1 e.2.val}

private def incidentNeighbor {n : ℕ} (b : Legal n) (m : Incident b) :
    {z : Legal n // (legalWordGraph n).Adj b z} := by
  by_cases h : b = m.val.1
  · exact ⟨erase m.val.1 m.val.2.val, by simpa only [SimpleGraph.mem_neighborSet, h] using erase_adj m.val.1 m.val.2.val m.val.2.property⟩
  · have hl : b = erase m.val.1 m.val.2.val := m.property.resolve_left h
    exact ⟨m.val.1, by simpa only [SimpleGraph.mem_neighborSet, hl] using (erase_adj m.val.1 m.val.2.val m.val.2.property).symm⟩

private theorem incident_edge {n : ℕ} (b : Legal n) (m : Incident b) :
    (deletionEdge n m.val).val = s(b, (incidentNeighbor b m).val) := by
  by_cases h : b = m.val.1
  · simp [deletionEdge, incidentNeighbor, h]
  · have hl : b = erase m.val.1 m.val.2.val := m.property.resolve_left h
    simp only [incidentNeighbor, dif_neg h, deletionEdge]
    exact (Sym2.eq_swap).trans (congrArg (fun v => s(v, m.val.1)) hl.symm)

private theorem incident_bijective {n : ℕ} (b : Legal n) :
    Function.Bijective (incidentNeighbor b) := by
  constructor
  · intro m k h
    apply Subtype.ext
    apply (deletionEdge_bijective n).1
    apply Subtype.ext
    rw [incident_edge, incident_edge, h]
  · intro z
    obtain ⟨m, hm⟩ := (deletionEdge_bijective n).2
      ⟨s(b, z.val), SimpleGraph.mem_edgeFinset.mpr z.property⟩
    have he : s(m.1, erase m.1 m.2.val) = s(b, z.val) := congrArg Subtype.val hm
    have hi : b = m.1 ∨ b = erase m.1 m.2.val := by
      have hb : b ∈ s(m.1, erase m.1 m.2.val) := by rw [he]; simp
      exact Sym2.mem_iff.mp hb
    refine ⟨⟨m, hi⟩, Subtype.ext ?_⟩
    apply Sym2.congr_right.mp
    rw [← incident_edge]
    exact congrArg Subtype.val hm

/-- The derivative's native neighbour square-share sum at a vertex. -/
noncomputable def gradient {n : ℕ} (p : Legal n → ℝ) (b : Legal n) : ℝ :=
  ∑ z : {z : Legal n // (legalWordGraph n).Adj b z}, (p z.val / (p b + p z.val)) ^ 2

private theorem gradient_incident {n : ℕ} (p : Legal n → ℝ) (b : Legal n) :
    gradient p b = ∑ m : Marked n,
      ((if b = erase m.1 m.2.val then 1 else 0) *
          (p m.1 / (p (erase m.1 m.2.val) + p m.1)) ^ 2 +
        (if b = m.1 then 1 else 0) *
          (p (erase m.1 m.2.val) / (p (erase m.1 m.2.val) + p m.1)) ^ 2) := by
  let f (m : Marked n) : ℝ :=
      ((if b = erase m.1 m.2.val then 1 else 0) *
          (p m.1 / (p (erase m.1 m.2.val) + p m.1)) ^ 2 +
        (if b = m.1 then 1 else 0) *
          (p (erase m.1 m.2.val) / (p (erase m.1 m.2.val) + p m.1)) ^ 2)
  have hi := Equiv.sum_comp (Equiv.ofBijective (incidentNeighbor b) (incident_bijective b))
    (fun z : {z : Legal n // (legalWordGraph n).Adj b z} => (p z.val / (p b + p z.val)) ^ 2)
  change gradient p b = ∑ m, f m
  calc
    gradient p b = ∑ m : Incident b,
        (p (incidentNeighbor b m).val / (p b + p (incidentNeighbor b m).val)) ^ 2 := hi.symm
    _ = ∑ m : Incident b, f m.val := by
      apply Finset.sum_congr rfl
      intro m _
      by_cases hu : b = m.val.1
      · have hl : b ≠ erase m.val.1 m.val.2.val := by
          exact fun h => upper_ne_lower m.val (hu.symm.trans h)
        simp only [f, incidentNeighbor, dif_pos hu, if_neg hl, if_pos hu]
        simp only [zero_mul, one_mul, zero_add]
        simpa only [add_comm] using congrArg (fun v =>
          (p (erase m.val.1 m.val.2.val) / (p v + p (erase m.val.1 m.val.2.val))) ^ 2) hu
      · have hl : b = erase m.val.1 m.val.2.val := m.property.resolve_left hu
        simp only [f, incidentNeighbor, dif_neg hu, if_pos hl, if_neg hu]
        simp only [one_mul, zero_mul, add_zero]
        simpa only [add_comm] using congrArg (fun v => (p m.val.1 /
          (p v + p m.val.1)) ^ 2) hl
    _ = ∑ m ∈ Finset.univ.filter (fun m : Marked n => b = m.1 ∨ b = erase m.1 m.2.val),
        f m := (Finset.sum_subtype _ (by simp) f).symm
    _ = ∑ m, f m := by
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro m _ hm
      have hne : b ≠ m.1 ∧ b ≠ erase m.1 m.2.val := by simpa using hm
      simp [f, hne.1, hne.2]

private theorem objective_transfer_hasDerivAt {n : ℕ} (p : Legal n → ℝ)
    (hp : ∀ b, 0 < p b) (donor receiver : Legal n) :
    HasDerivAt (fun u : ℝ => objective n (transfer p donor receiver u))
      (gradient p receiver - gradient p donor) 0 := by
  let d (b : Legal n) : ℝ :=
    (if b = receiver then 1 else 0) - (if b = donor then 1 else 0)
  have hs : HasDerivAt
      (fun u : ℝ => ∑ m : Marked n,
        harmonic (p (erase m.1 m.2.val) + u * d (erase m.1 m.2.val))
          (p m.1 + u * d m.1))
      (∑ m : Marked n,
        (d (erase m.1 m.2.val) *
            (p m.1 / (p (erase m.1 m.2.val) + p m.1)) ^ 2 +
          d m.1 * (p (erase m.1 m.2.val) / (p (erase m.1 m.2.val) + p m.1)) ^ 2)) 0 := by
    exact HasDerivAt.fun_sum (u := Finset.univ) (fun (m : Marked n) _ =>
      harmonic_hasDerivAt _ _ _ _ (hp _) (hp _))
  have he : (∑ m : Marked n,
        (d (erase m.1 m.2.val) *
            (p m.1 / (p (erase m.1 m.2.val) + p m.1)) ^ 2 +
          d m.1 * (p (erase m.1 m.2.val) / (p (erase m.1 m.2.val) + p m.1)) ^ 2)) =
      gradient p receiver - gradient p donor := by
    rw [gradient_incident, gradient_incident, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro m _
    simp only [d, eq_comm]
    ring
  rw [he] at hs
  simpa only [objective_unordered, transfer, d] using hs

private theorem positive_transfer_step {n : ℕ} (ε : ℝ) (p : Legal n → ℝ)
    (hε : 0 < ε) (hp : p ∈ epsilonSimplex n ε) (donor receiver : Legal n)
    (horder : p receiver < p donor) (hgrad : gradient p donor < gradient p receiver) :
    ∃ δ : ℝ, 0 < δ ∧ δ < p donor - ε ∧
      ∀ u : ℝ, 0 < u → u < δ →
        transfer p donor receiver u ∈ epsilonSimplex n ε ∧
        objective n p < objective n (transfer p donor receiver u) := by
  have hne : donor ≠ receiver := by intro h; subst donor; exact (lt_irrefl _ horder).elim
  have hslack : 0 < p donor - ε := by have := hp.1 receiver; linarith
  have hd := objective_transfer_hasDerivAt p (fun b => hε.trans_le (hp.1 b)) donor receiver
  have he : ∀ᶠ u in 𝓝[>] (0 : ℝ),
      0 < u⁻¹ * (objective n (transfer p donor receiver u) - objective n p) := by
    simpa only [zero_add, transfer_zero, smul_eq_mul] using
      hd.tendsto_slope_zero_right.eventually_const_lt (sub_pos.mpr hgrad)
  obtain ⟨η, hη, hηall⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp he
  refine ⟨min η ((p donor - ε) / 2), lt_min hη (half_pos hslack),
    lt_of_le_of_lt (min_le_right _ _) (half_lt_self hslack), ?_⟩
  intro u hu huδ
  refine ⟨transfer_feasible ε p hp donor receiver hne u hu.le ?_, ?_⟩
  · linarith [lt_of_lt_of_le huδ (min_le_right η ((p donor - ε) / 2))]
  · have hgain := hηall ⟨hu, lt_of_lt_of_le huδ (min_le_left _ _)⟩
    exact sub_pos.mp ((mul_pos_iff_of_pos_left (inv_pos.mpr hu)).mp hgain)

private theorem sum_excluding {α : Type} [Fintype α] [DecidableEq α]
    (P : α → Prop) [DecidablePred P] (f : α → ℝ) (a : α) (ha : P a) :
    (∑ x : {x // P x}, f x.val) =
      f a + ∑ x : {x // P x ∧ x ≠ a}, f x.val := by
  have he : Finset.univ.filter P =
      Insert.insert a (Finset.univ.filter (fun x => P x ∧ x ≠ a)) := by
    ext x
    by_cases hx : x = a
    · subst x; simp [ha]
    · simp [hx]
  rw [← Finset.sum_subtype (Finset.univ.filter P) (by simp) f,
    ← Finset.sum_subtype (Finset.univ.filter (fun x => P x ∧ x ≠ a)) (by simp) f,
    he, Finset.sum_insert (by simp)]

private theorem sum_partition {α : Type} [Fintype α] (P Q : α → Prop)
    [DecidablePred P] [DecidablePred Q] (f : α → ℝ) :
    (∑ x : {x // P x}, f x.val) =
      (∑ x : {x // P x ∧ Q x}, f x.val) +
        ∑ x : {x // P x ∧ ¬ Q x}, f x.val := by
  rw [← Finset.sum_subtype (Finset.univ.filter P) (by simp) f,
    ← Finset.sum_subtype (Finset.univ.filter (fun x => P x ∧ Q x)) (by simp) f,
    ← Finset.sum_subtype (Finset.univ.filter (fun x => P x ∧ ¬Q x)) (by simp) f]
  simpa only [Finset.filter_filter] using
    (Finset.sum_filter_add_sum_filter_not (Finset.univ.filter P) Q f).symm

private abbrev BlockedLower {n : ℕ} (e : Marked n) :=
  {w : Legal n // (legalWordGraph n).Adj (erase e.1 e.2.val) w ∧
    w ≠ e.1 ∧ ¬FlippableZero w.val e.2.val}

set_option maxHeartbeats 2000000 in
-- Transport of the sums elaborates several nested dependent finite carriers.
private theorem gradient_split {n : ℕ} (p : Legal n → ℝ) (e : Marked n) :
    gradient p e.1 =
      (p (erase e.1 e.2.val) / (p e.1 + p (erase e.1 e.2.val))) ^ 2 +
        ∑ w : PairedLower e,
          (p (insert w.val e.2.val w.property.2) /
            (p e.1 + p (insert w.val e.2.val w.property.2))) ^ 2 ∧
    gradient p (erase e.1 e.2.val) =
      (p e.1 / (p (erase e.1 e.2.val) + p e.1)) ^ 2 +
        (∑ w : PairedLower e,
          (p w.val / (p (erase e.1 e.2.val) + p w.val)) ^ 2) +
        ∑ w : BlockedLower e,
          (p w.val / (p (erase e.1 e.2.val) + p w.val)) ^ 2 := by
  constructor
  · unfold gradient
    rw [sum_excluding (fun z => (legalWordGraph n).Adj e.1 z)
      (fun z : Legal n => (p z / (p e.1 + p z)) ^ 2)
      (erase e.1 e.2.val) (erase_adj e.1 e.2.val e.2.property)]
    congr 1
    convert! (Equiv.sum_comp (neighborPairing e)
      (fun z : PairedUpper e => (p z.val / (p e.1 + p z.val)) ^ 2)).symm using 1
  · unfold gradient
    rw [sum_excluding (fun w => (legalWordGraph n).Adj (erase e.1 e.2.val) w)
      (fun w : Legal n => (p w / (p (erase e.1 e.2.val) + p w)) ^ 2)
      e.1 (erase_adj e.1 e.2.val e.2.property).symm]
    have hpart := sum_partition
      (fun w : Legal n => (legalWordGraph n).Adj (erase e.1 e.2.val) w ∧ w ≠ e.1)
      (fun w => FlippableZero w.val e.2.val)
      (fun w => (p w / (p (erase e.1 e.2.val) + p w)) ^ 2)
    have hpart' : (∑ w : {w : Legal n //
        (legalWordGraph n).Adj (erase e.1 e.2.val) w ∧ w ≠ e.1},
      (p w.val / (p (erase e.1 e.2.val) + p w.val)) ^ 2) = _ := hpart
    rw [hpart']
    let epair : {w : Legal n //
        ((legalWordGraph n).Adj (erase e.1 e.2.val) w ∧ w ≠ e.1) ∧
          FlippableZero w.val e.2.val} ≃ PairedLower e := {
      toFun := fun w => ⟨w.val, w.property.1.1, w.property.2⟩
      invFun := fun w => ⟨w.val, ⟨w.property.1, by
        intro h
        have hv := w.property.2.1
        simpa [h, e.2.property] using hv⟩, w.property.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
    let eblock : {w : Legal n //
        ((legalWordGraph n).Adj (erase e.1 e.2.val) w ∧ w ≠ e.1) ∧
          ¬FlippableZero w.val e.2.val} ≃ BlockedLower e := {
      toFun := fun w => ⟨w.val, w.property.1.1, w.property.1.2, w.property.2⟩
      invFun := fun w => ⟨w.val, ⟨w.property.1, w.property.2.1⟩, w.property.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
    have hpairEq := Equiv.sum_comp epair
      (fun w : PairedLower e => (p w.val / (p (erase e.1 e.2.val) + p w.val)) ^ 2)
    have hblockEq := Equiv.sum_comp eblock
      (fun w : BlockedLower e => (p w.val / (p (erase e.1 e.2.val) + p w.val)) ^ 2)
    change _ + ((∑ w, (p (epair w).val / (p (erase e.1 e.2.val) + p (epair w).val)) ^ 2) +
      ∑ w, (p (eblock w).val / (p (erase e.1 e.2.val) + p (eblock w).val)) ^ 2) = _
    rw [hpairEq, hblockEq, add_assoc]

private theorem blocked_position {n : ℕ} (e : Marked n) (w : BlockedLower e) :
    ∃ j : Fin n, Near e.2.val j ∧ ∃ h : FlippableZero (erase e.1 e.2.val).val j,
      w.val = insert (erase e.1 e.2.val) j h := by
  rcases lower_neighbor_partition e w.val w.property.1 with h | h | h
  · exact (w.property.2.1 h).elim
  · exact (w.property.2.2 h).elim
  · exact h

private noncomputable def blockedIndex {n : ℕ} (e : Marked n) (w : BlockedLower e) :
    {j : Fin n // Near e.2.val j} :=
  ⟨(blocked_position e w).choose, (blocked_position e w).choose_spec.1⟩

private theorem blockedIndex_injective {n : ℕ} (e : Marked n) :
    Function.Injective (blockedIndex e) := by
  intro w v he
  have hj := congrArg Subtype.val he
  obtain ⟨hw, hew⟩ := (blocked_position e w).choose_spec.2
  obtain ⟨hv, hev⟩ := (blocked_position e v).choose_spec.2
  apply Subtype.ext
  apply Subtype.ext
  change w.val.val = v.val.val
  rw [hew, hev]
  change Function.update (erase e.1 e.2.val).val ((blocked_position e w).choose) true =
    Function.update (erase e.1 e.2.val).val ((blocked_position e v).choose) true
  exact congrArg (fun j : Fin n => Function.update (erase e.1 e.2.val).val j true) hj

private theorem blocked_card {n : ℕ} (e : Marked n) :
    Fintype.card (BlockedLower e) ≤ positionDegree e.2.val := by
  have hc := Fintype.card_le_of_injective (blockedIndex e) (blockedIndex_injective e)
  simpa [positionDegree, Fintype.card_subtype] using hc

private theorem insertionLower_le_one {n : ℕ} (i : Fin n) : insertionLower i ≤ 1 := by
  unfold insertionLower
  apply (div_le_iff₀ (by positivity)).mpr
  have := Nat.cast_nonneg (α := ℝ) (positionDegree i)
  linarith

private theorem share_compare (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hc : 0 < c) (hd : 0 < d) (hcross : c * a ≤ d * b) :
    (c / (b + c)) ^ 2 ≤ (d / (a + d)) ^ 2 := by
  apply (sq_le_sq₀ (div_nonneg hc.le (add_pos hb hc).le)
    (div_nonneg hd.le (add_pos ha hd).le)).mpr
  apply (div_le_div_iff₀ (add_pos hb hc) (add_pos ha hd)).mpr
  nlinarith

private theorem edge_share_difference (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    (a / (b + a)) ^ 2 - (b / (a + b)) ^ 2 = (a - b) / (a + b) := by
  have hne : a + b ≠ 0 := ne_of_gt (add_pos ha hb)
  rw [add_comm b a]
  field_simp [hne]
  <;> ring

private theorem upper_extremal_gradient {n : ℕ} (p : Legal n → ℝ)
    (hp : ∀ b, 0 < p b) (e : Marked n)
    (hbad : p (erase e.1 e.2.val) < p e.1)
    (hmax : ∀ m : Marked n,
      p m.1 / p (erase m.1 m.2.val) ≤ p e.1 / p (erase e.1 e.2.val)) :
    gradient p e.1 < gradient p (erase e.1 e.2.val) := by
  have hs := gradient_split p e
  have hpair : (∑ w : PairedLower e,
      (p (insert w.val e.2.val w.property.2) /
        (p e.1 + p (insert w.val e.2.val w.property.2))) ^ 2) ≤
      ∑ w : PairedLower e, (p w.val / (p (erase e.1 e.2.val) + p w.val)) ^ 2 := by
    apply Finset.sum_le_sum
    intro w _
    let m : Marked n := ⟨insert w.val e.2.val w.property.2,
      ⟨e.2.val, insert_at _ _ _⟩⟩
    have hc := (div_le_div_iff₀ (hp (erase m.1 m.2.val))
      (hp (erase e.1 e.2.val))).mp (hmax m)
    have he : erase m.1 m.2.val = w.val := erase_insert w.val e.2.val w.property.2
    rw [he] at hc
    exact share_compare _ _ _ _ (hp _) (hp _) (hp _) (hp _) (by simpa only [m, mul_comm] using hc)
  have hblock : 0 ≤ ∑ w : BlockedLower e,
      (p w.val / (p (erase e.1 e.2.val) + p w.val)) ^ 2 :=
    Finset.sum_nonneg (fun w _ => sq_nonneg _)
  have hedge := edge_share_difference _ _ (hp (erase e.1 e.2.val)) (hp e.1)
  have hneg : (p (erase e.1 e.2.val) - p e.1) /
      (p (erase e.1 e.2.val) + p e.1) < 0 :=
    div_neg_of_neg_of_pos (sub_neg.mpr hbad) (add_pos (hp _) (hp _))
  linarith [hs.1, hs.2]

private theorem blocked_share_le_quarter {n : ℕ} (p : Legal n → ℝ)
    (hp : ∀ b, 0 < p b)
    (hupper : ∀ m : Marked n, p m.1 ≤ p (erase m.1 m.2.val))
    (e : Marked n) (w : BlockedLower e) :
    (p w.val / (p (erase e.1 e.2.val) + p w.val)) ^ 2 ≤ (1 / 4 : ℝ) := by
  obtain ⟨j, _, h, hw⟩ := blocked_position e w
  let m : Marked n := ⟨insert (erase e.1 e.2.val) j h, ⟨j, insert_at _ _ _⟩⟩
  have hm : p w.val ≤ p (erase e.1 e.2.val) := by
    have hh := hupper m
    change p (insert (erase e.1 e.2.val) j h) ≤
      p (erase (insert (erase e.1 e.2.val) j h) j) at hh
    rw [erase_insert, ← hw] at hh
    exact hh
  have hf : p w.val / (p (erase e.1 e.2.val) + p w.val) ≤ (1 / 2 : ℝ) := by
    apply (div_le_iff₀ (add_pos (hp _) (hp _))).mpr
    linarith
  have hn : 0 ≤ p w.val / (p (erase e.1 e.2.val) + p w.val) := div_nonneg (hp _).le (add_pos (hp _) (hp _)).le
  nlinarith

private theorem lower_extremal_gradient {n : ℕ} (p : Legal n → ℝ)
    (hp : ∀ b, 0 < p b)
    (hupper : ∀ m : Marked n, p m.1 ≤ p (erase m.1 m.2.val))
    (e : Marked n)
    (hbad : p e.1 < insertionLower e.2.val * p (erase e.1 e.2.val))
    (hmin : ∀ m : Marked n, m.2.val = e.2.val →
      p e.1 / p (erase e.1 e.2.val) ≤ p m.1 / p (erase m.1 m.2.val)) :
    gradient p (erase e.1 e.2.val) < gradient p e.1 := by
  have hs := gradient_split p e
  have hpair : (∑ w : PairedLower e,
      (p w.val / (p (erase e.1 e.2.val) + p w.val)) ^ 2) ≤
      ∑ w : PairedLower e,
        (p (insert w.val e.2.val w.property.2) /
          (p e.1 + p (insert w.val e.2.val w.property.2))) ^ 2 := by
    apply Finset.sum_le_sum
    intro w _
    let m : Marked n := ⟨insert w.val e.2.val w.property.2,
      ⟨e.2.val, insert_at _ _ _⟩⟩
    have hc := (div_le_div_iff₀ (hp (erase e.1 e.2.val))
      (hp (erase m.1 m.2.val))).mp (hmin m rfl)
    have he : erase m.1 m.2.val = w.val := erase_insert w.val e.2.val w.property.2
    rw [he] at hc
    exact share_compare _ _ _ _ (hp _) (hp _) (hp _) (hp _) (by simpa only [m, mul_comm] using hc)
  have hblock : (∑ w : BlockedLower e,
      (p w.val / (p (erase e.1 e.2.val) + p w.val)) ^ 2) ≤
      (positionDegree e.2.val : ℝ) / 4 := by
    calc
      _ ≤ ∑ _w : BlockedLower e, (1 / 4 : ℝ) :=
        Finset.sum_le_sum (fun w _ => blocked_share_le_quarter p hp hupper e w)
      _ = (Fintype.card (BlockedLower e) : ℝ) / 4 := by simp [div_eq_mul_inv]
      _ ≤ (positionDegree e.2.val : ℝ) / 4 := by
        exact div_le_div_of_nonneg_right (by exact_mod_cast blocked_card e) (by norm_num)
  have hedge := edge_share_difference _ _ (hp (erase e.1 e.2.val)) (hp e.1)
  have hpositive : (positionDegree e.2.val : ℝ) / 4 <
      (p (erase e.1 e.2.val) - p e.1) / (p (erase e.1 e.2.val) + p e.1) := by
    have hden : 0 < (4 + (positionDegree e.2.val : ℝ)) := by positivity
    have hbad' : (4 + (positionDegree e.2.val : ℝ)) * p e.1 <
        (4 - (positionDegree e.2.val : ℝ)) * p (erase e.1 e.2.val) := by
      unfold insertionLower at hbad
      have hh := (lt_div_iff₀ hden).mp
        (show p e.1 < (4 - (positionDegree e.2.val : ℝ)) *
          p (erase e.1 e.2.val) / (4 + (positionDegree e.2.val : ℝ)) by
          simpa only [div_mul_eq_mul_div] using hbad)
      nlinarith
    apply (lt_div_iff₀ (add_pos (hp _) (hp _))).mpr
    nlinarith
  linarith [hs.1, hs.2]

/-- A violating insertion forces an internally selected original-edge improving transfer. -/
theorem improving_transfer_of_bad_insertion (n : ℕ) (_hn : 1 ≤ n)
    (ε : ℝ) (hε : 0 < ε) (p : Legal n → ℝ) (hp : p ∈ epsilonSimplex n ε)
    (hbad : ¬InsertionBounds n p) :
    ∃ donor receiver : Legal n,
      (legalWordGraph n).Adj donor receiver ∧ p receiver < p donor ∧
      ∃ δ : ℝ, 0 < δ ∧ δ < p donor - ε ∧
        ∀ u : ℝ, 0 < u → u < δ →
          transfer p donor receiver u ∈ epsilonSimplex n ε ∧
          objective n p < objective n (transfer p donor receiver u) := by
  have hpos : ∀ b, 0 < p b := fun b => hε.trans_le (hp.1 b)
  by_cases hupper : ∀ m : Marked n, p m.1 ≤ p (erase m.1 m.2.val)
  · have hlow : ∃ e : Marked n,
        p e.1 < insertionLower e.2.val * p (erase e.1 e.2.val) := by
      by_contra h
      push_neg at h
      apply hbad
      exact fun e => ⟨h e, hupper e⟩
    obtain ⟨e0, hbad0⟩ := hlow
    let S := Finset.univ.filter (fun m : Marked n => m.2.val = e0.2.val)
    have hS : S.Nonempty := ⟨e0, by simp [S]⟩
    obtain ⟨e, he, hmin⟩ := S.exists_min_image
      (fun m => p m.1 / p (erase m.1 m.2.val)) hS
    have hi : e.2.val = e0.2.val := (Finset.mem_filter.mp he).2
    have hr0 : p e0.1 / p (erase e0.1 e0.2.val) < insertionLower e0.2.val :=
      (div_lt_iff₀ (hpos _)).mpr hbad0
    have hre : p e.1 / p (erase e.1 e.2.val) < insertionLower e.2.val := by
      exact ((hmin e0 (by simp [S])).trans_lt hr0).trans_eq
        (congrArg insertionLower hi.symm)
    have hebad : p e.1 < insertionLower e.2.val * p (erase e.1 e.2.val) :=
      (div_lt_iff₀ (hpos _)).mp hre
    have hg := lower_extremal_gradient p hpos hupper e hebad (fun m hm =>
      hmin m (by simp [S, hm, hi]))
    have ho : p e.1 < p (erase e.1 e.2.val) :=
      hebad.trans_le (by
        simpa only [one_mul] using (mul_le_mul_of_nonneg_right
          (insertionLower_le_one e.2.val) (hpos (erase e.1 e.2.val)).le))
    refine ⟨erase e.1 e.2.val, e.1,
      (erase_adj e.1 e.2.val e.2.property).symm, ho, ?_⟩
    exact positive_transfer_step ε p hε hp _ _ ho hg
  · push_neg at hupper
    obtain ⟨e0, hbad0⟩ := hupper
    obtain ⟨e, _, hmax⟩ := (Finset.univ : Finset (Marked n)).exists_max_image
      (fun m => p m.1 / p (erase m.1 m.2.val)) ⟨e0, Finset.mem_univ e0⟩
    have hr0 : 1 < p e0.1 / p (erase e0.1 e0.2.val) :=
      (one_lt_div (hpos _)).mpr hbad0
    have hre : 1 < p e.1 / p (erase e.1 e.2.val) :=
      hr0.trans_le (hmax e0 (Finset.mem_univ e0))
    have ho : p (erase e.1 e.2.val) < p e.1 := (one_lt_div (hpos _)).mp hre
    have hg := upper_extremal_gradient p hpos e ho (fun m => hmax m (Finset.mem_univ m))
    refine ⟨e.1, erase e.1 e.2.val, erase_adj e.1 e.2.val e.2.property, ho, ?_⟩
    exact positive_transfer_step ε p hε hp _ _ ho hg

/-- A maximum on the entire feasible simplex satisfies every original insertion bound. -/
theorem exists_constrained_optimizer_with_insertion_bounds (n : ℕ) (hn : 1 ≤ n)
    (ε : ℝ) (hε : 0 < ε) (hsmall : ε ≤ 1 / (Fintype.card (Legal n) : ℝ)) :
    ∃ p : Legal n → ℝ,
      p ∈ epsilonSimplex n ε ∧ IsMaxOn (objective n) (epsilonSimplex n ε) p ∧
      InsertionBounds n p := by
  obtain ⟨p, hp, hmax⟩ := exists_constrained_optimizer n ε hε hsmall
  refine ⟨p, hp, hmax, ?_⟩
  by_contra hbad
  obtain ⟨donor, receiver, _, _, δ, hδ, _, hall⟩ :=
    improving_transfer_of_bad_insertion n hn ε hε p hp hbad
  have hstep := hall (δ / 2) (half_pos hδ) (half_lt_self hδ)
  exact (not_lt_of_ge (hmax hstep.1) hstep.2)

#print axioms improving_transfer_of_bad_insertion
#print axioms exists_constrained_optimizer_with_insertion_bounds
#check improving_transfer_of_bad_insertion
#check exists_constrained_optimizer_with_insertion_bounds

end D5.S3.Combinatorics.Graph.LegalWords.ConstrainedHarmonicOptimizer
