/- GID: D5/S1/Words/RankOneMorphismIterationBound
   generality: G
   mirror-B: D5/B/S1/Words/RankOneMorphismIterationBound
   mirror-E: none(waiver:source-open-question-resolution)
   anchors: []
   utility: none
   digest: Effective 2^N bound and finite decision of arbitrary-preperiod abelian periodicity for primitive binary rank-one morphisms. -/
import D5.S1.Words.RankOneMorphismIterationBoundReduction
import D5.S1.Words.RankOneMorphismIterationBoundChecker

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Words.RankOneMorphismIterationBound
namespace Parameters
variable {f : Morphism} (p : Parameters f)

theorem uap_iff_original (hp : Prolongable f) :
    UltimatelyAbelianPeriodic p.fixedWord ↔
      ∃ K : ℕ, 1 ≤ K ∧ OriginalCyclicBlockWitness f K := by
  constructor
  · exact p.original_of_uap hp
  · rintro ⟨K,hK,h⟩; exact p.uap_of_original hp hK h

theorem uap_iff_bounded_original (hp : Prolongable f) :
    UltimatelyAbelianPeriodic p.fixedWord ↔
      ∃ K : ℕ, 1 ≤ K ∧ K ≤ iterationBound f ∧ OriginalCyclicBlockWitness f K := by
  rw [p.uap_iff_original hp,p.finite_witness_cutoff]

theorem uap_iff_bounded_normalized (hp : Prolongable f) :
    UltimatelyAbelianPeriodic p.fixedWord ↔
      ∃ t : ℕ, t+1 ≤ iterationBound f ∧ p.NormalizedWitness t := by
  rw [p.uap_iff_bounded_original hp]
  constructor
  · rintro ⟨K,hK,hbound,h⟩
    obtain ⟨t,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : K ≠ 0)
    exact ⟨t,hbound,p.samples_to_normalized ((p.original_iff_samples t).mp h)⟩
  · rintro ⟨t,hbound,h⟩
    exact ⟨t+1,by omega,hbound,p.normalized_original h⟩

private theorem normalized_block_lengths (t : ℕ) (w : Word)
    (h : Blocks w (fun b => p.lam^t*(if b = 0 then p.A else p.B))) :
    ∃ bs : List Word, bs.flatten = w ∧ bs ≠ [] ∧ ∀ b ∈ bs,
      b ≠ [] ∧ b.length = p.d*p.lam^t ∧
        parikh b = (fun c => p.lam^t*(if c = 0 then p.A else p.B)) := by
  obtain ⟨bs,hflat,hne,hb⟩ := h
  refine ⟨bs,hflat,hne,?_⟩
  intro b hmem
  obtain ⟨hne',hpar⟩ := hb b hmem
  refine ⟨hne',?_,hpar⟩
  have h0 := congrFun hpar 0
  have h1 := congrFun hpar 1
  simp only [ite_true,show (1 : Letter) ≠ 0 by decide,ite_false] at h0 h1
  rw [← parikh_binary_length b,h0,h1]
  dsimp [d]
  ring

/-- The stronger source witness states the real block lengths and vectors
    explicitly, as well as the normalized common cut. -/
theorem bounded_normalized_source_witness (hp : Prolongable f)
    (huap : UltimatelyAbelianPeriodic p.fixedWord) :
    ∃ t r : ℕ, t+1 ≤ iterationBound f ∧ r < p.d*p.lam^t ∧
      AbelianEq ((image f (t+1) 0).take r) ((image f (t+1) 1).take r) ∧
      ∀ c : Letter, ∃ bs : List Word,
        bs.flatten = (image f (t+1) c).drop r ++ (image f (t+1) c).take r ∧
        bs ≠ [] ∧ ∀ b ∈ bs, b ≠ [] ∧ b.length = p.d*p.lam^t ∧
          parikh b = (fun a => p.lam^t*(if a = 0 then p.A else p.B)) := by
  obtain ⟨t,ht,r,hr,hab,hblocks⟩ := (p.uap_iff_bounded_normalized hp).mp huap
  exact ⟨t,r,ht,hr,hab,fun c => p.normalized_block_lengths t _ (hblocks c)⟩

/-- The actual subset transition checker also decides the full source UAP
    property when the extracted rank-one parameters are supplied. -/
theorem subsetChecker_uap (hp : Prolongable f) :
    p.subsetChecker = true ↔ UltimatelyAbelianPeriodic p.fixedWord := by
  rw [p.subsetChecker_correct,p.uap_iff_original hp]
  constructor
  · rintro ⟨e,v,h⟩
    exact ⟨v.length+1,by omega,(p.original_iff_root v.length).mpr ⟨e,v,rfl,h⟩⟩
  · rintro ⟨K,hK,h⟩
    obtain ⟨t,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : K ≠ 0)
    obtain ⟨e,v,hv,ha⟩ := (p.original_iff_root t).mp h
    exact ⟨e,v,ha⟩

end Parameters

/-- The complete original source domain, the actual fixed word, arbitrary
    preperiods, the original four words, and the explicit total finite bound. -/
theorem effective_iteration_bound (f : Morphism)
    (hne : Nonerasing f) (hp : Prolongable f) (hprim : Primitive f) (hrank : RankOne f)
    (x : ℕ → Letter) (hx : IsFixedWord f x) :
    UltimatelyAbelianPeriodic x ↔
      ∃ K : ℕ, 1 ≤ K ∧ K ≤ 2^((f 0).length+(f 1).length) ∧
        OriginalCyclicBlockWitness f K := by
  obtain ⟨p⟩ := exists_parameters hne hp hprim hrank
  rw [p.fixedWord_unique hp hx]
  exact p.uap_iff_bounded_original hp

/-- Correctness of the actual finite-image executable checker for the complete
    source theorem. False certifies absence of UAP in precisely this domain. -/
theorem finiteChecker_uap (f : Morphism)
    (hne : Nonerasing f) (hp : Prolongable f) (hprim : Primitive f) (hrank : RankOne f)
    (x : ℕ → Letter) (hx : IsFixedWord f x) :
    finiteChecker f = true ↔ UltimatelyAbelianPeriodic x := by
  obtain ⟨p⟩ := exists_parameters hne hp hprim hrank
  rw [p.fixedWord_unique hp hx,p.uap_iff_original hp]
  exact p.finiteChecker_correct

end D5.S1.Words.RankOneMorphismIterationBound
