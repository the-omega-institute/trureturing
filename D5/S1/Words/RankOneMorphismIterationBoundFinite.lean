/- GID: D5/S1/Words/RankOneMorphismIterationBoundFinite
   generality: G
   mirror-B: D5/B/S1/Words/RankOneMorphismIterationBoundFinite
   mirror-E: none(waiver:source-witness-finite-bridge)
   anchors: []
   digest: Actual cyclic witness iff source subset roots, consuming the 2^N cutoff. -/
import D5.S1.Words.RankOneMorphismIterationBoundDigits
import D5.S1.Words.RankOneMorphismIterationBoundNormalization

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Words.RankOneMorphismIterationBound
namespace Parameters
variable {f : Morphism} (p : Parameters f)

theorem root_position_bound (e : Fin p.d) (c : Letter) (j : ℕ) (hj : j < p.mult c) :
    e.val+j*p.d < (f c).length := by
  rw [p.image_length]
  have he := e.isLt
  nlinarith

theorem forall_root_iff (e : Fin p.d) (F : State f → Prop) :
    (∀ q ∈ p.root e, F q) ↔ ∀ c j (hj : j < p.mult c),
      F ⟨c, ⟨e.val+j*p.d, p.root_position_bound e c j hj⟩⟩ := by
  constructor
  · intro h c j hj
    apply h
    fin_cases c
    · apply Finset.mem_union_left
      exact Finset.mem_image.mpr ⟨⟨j, by simpa [mult] using hj⟩, Finset.mem_univ _, rfl⟩
    · apply Finset.mem_union_right
      exact Finset.mem_image.mpr ⟨⟨j, by simpa [mult] using hj⟩, Finset.mem_univ _, rfl⟩
  · intro h q hq
    simp only [root, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and] at hq
    rcases hq with ⟨j,rfl⟩ | ⟨j,rfl⟩
    · exact h 0 j.val (by simpa [mult] using j.isLt)
    · exact h 1 j.val (by simpa [mult] using j.isLt)

theorem root_coding_iff (e : Fin p.d) (v : List (Fin p.lam)) :
    p.RootAccepts e v ↔ ∃ Z : ℤ, ∀ q ∈ p.root e,
      p.coding (p.heightMachine.toDFA.evalFrom q v) = Z := by
  rw [RootAccepts, p.subset_eval]
  obtain ⟨q0,hq0⟩ := p.root_nonempty e
  constructor
  · rintro ⟨hne,hconst⟩
    refine ⟨p.coding (p.heightMachine.toDFA.evalFrom q0 v), ?_⟩
    intro q hq
    exact hconst _ (Finset.mem_image.mpr ⟨q,hq,rfl⟩) _ (Finset.mem_image.mpr ⟨q0,hq0,rfl⟩)
  · rintro ⟨Z,h⟩
    refine ⟨⟨_, Finset.mem_image.mpr ⟨q0,hq0,rfl⟩⟩, ?_⟩
    intro q hq r hr
    obtain ⟨q',hq',rfl⟩ := Finset.mem_image.mp hq
    obtain ⟨r',hr',rfl⟩ := Finset.mem_image.mp hr
    exact (h q' hq').trans (h r' hr').symm

theorem root_samples (e : Fin p.d) (v : List (Fin p.lam)) :
    p.RootAccepts e v ↔ ∃ Z : ℤ, ∀ c j, j < p.mult c →
      p.charge ((image f (v.length+1) c).take
        (e.val*p.lam^v.length+p.digitValue v+j*(p.d*p.lam^v.length))) = Z := by
  rw [p.root_coding_iff]
  constructor
  · rintro ⟨Z,h⟩
    refine ⟨Z,?_⟩
    intro c j hj
    have hc := (p.forall_root_iff e _).mp h c j hj
    rw [← p.source_digit_height v c (e.val+j*p.d)] at hc
    convert hc using 1 <;> congr 2 <;> ring
  · rintro ⟨Z,h⟩
    refine ⟨Z,(p.forall_root_iff e _).mpr ?_⟩
    intro c j hj
    rw [← p.source_digit_height v c (e.val+j*p.d)]
    convert h c j hj using 1 <;> congr 2 <;> ring

theorem samples_iff_root (t : ℕ) :
    p.CutSamples t ↔ ∃ e : Fin p.d, ∃ v : List (Fin p.lam), v.length=t ∧ p.RootAccepts e v := by
  have hpow : 0 < p.lam^t := pow_pos (by have := p.lam_ge_two; omega) _
  constructor
  · rintro ⟨r,hr,Z,h⟩
    have he : r/p.lam^t < p.d := by
      apply (Nat.div_lt_iff_lt_mul hpow).mpr
      simpa [Nat.mul_comm] using hr
    obtain ⟨v,hv,hval⟩ := p.digits_exist t (r%p.lam^t) (Nat.mod_lt _ hpow)
    refine ⟨⟨r/p.lam^t,he⟩,v,hv,?_⟩
    rw [p.root_samples]
    refine ⟨Z,?_⟩
    intro c j hj
    rw [hv,hval]
    have hr' : r/p.lam^t*p.lam^t+r%p.lam^t = r := Nat.div_add_mod' _ _
    simpa only [hr'] using h c j hj
  · rintro ⟨e,v,hv,ha⟩
    obtain ⟨Z,h⟩ := (p.root_samples e v).mp ha
    rw [hv] at h
    refine ⟨e.val*p.lam^t+p.digitValue v,?_,Z,h⟩
    have he := e.isLt
    have hu := p.digitValue_lt v
    rw [hv] at hu
    nlinarith

/-- The first decisive equivalence for the actual original source witness. -/
theorem original_iff_root (t : ℕ) :
    OriginalCyclicBlockWitness f (t+1) ↔
      ∃ e : Fin p.d, ∃ v : List (Fin p.lam), v.length=t ∧ p.RootAccepts e v :=
  (p.original_iff_samples t).trans (p.samples_iff_root t)

include p in
/-- Any positive original source witness compresses to iteration at most 2^N. -/
theorem finite_witness_cutoff :
    (∃ K : ℕ, 1 ≤ K ∧ OriginalCyclicBlockWitness f K) ↔
    ∃ K : ℕ, 1 ≤ K ∧ K ≤ iterationBound f ∧ OriginalCyclicBlockWitness f K := by
  constructor
  · rintro ⟨K,hK,h⟩
    obtain ⟨t,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : K ≠ 0)
    obtain ⟨e,v,hv,ha⟩ := (p.original_iff_root t).mp h
    obtain ⟨e',v',hlen,hacc⟩ := p.root_cutoff.mp ⟨e,v,ha⟩
    refine ⟨v'.length+1,by omega,by omega,?_⟩
    exact (p.original_iff_root v'.length).mpr ⟨e',v',rfl,hacc⟩
  · rintro ⟨K,hK,hbound,h⟩; exact ⟨K,hK,h⟩

end Parameters
end D5.S1.Words.RankOneMorphismIterationBound
