/- GID: D5/S1/Words/RankOneMorphismIterationBoundSoundness
   generality: G
   mirror-B: D5/B/S1/Words/RankOneMorphismIterationBoundSoundness
   mirror-E: none(waiver:actual-source-soundness)
   anchors: []
   utility: none
   digest: Complete cyclic source witnesses imply UAP of the actual morphic fixed word. -/
import D5.S1.Words.RankOneMorphismIterationBoundNormalization
import D5.S1.Words.RankOneMorphismIterationBoundFixedWord

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Words.RankOneMorphismIterationBound
open AbelianBorders.AbelianBorderQuestionDefs (factor)
namespace Parameters
variable {f : Morphism} (p : Parameters f)

/-- Actual source supertiles carry the normalized phase across every concatenation. -/
theorem samples_substituted_word {t r : ℕ} {Z : ℤ} (hr : r < p.d*p.lam^t)
    (hs : ∀ c j, j < p.mult c →
      p.charge ((image f (t+1) c).take (r+j*(p.d*p.lam^t))) = Z)
    (w : Word) (j : ℕ)
    (hj : r+j*(p.d*p.lam^t) < (subst (image f (t+1)) w).length) :
    p.charge ((subst (image f (t+1)) w).take (r+j*(p.d*p.lam^t))) = Z := by
  let P := p.d*p.lam^t
  have hP : 0 < P := Nat.mul_pos p.d_pos (pow_pos (by have := p.lam_ge_two; omega) _)
  induction w generalizing j with
  | nil => simp at hj
  | cons c w ih =>
    rw [subst_cons]
    by_cases hlocal : j < p.mult c
    · rw [List.take_append_of_le_length (by rw [p.iterated_length]; nlinarith)]
      exact hs c j hlocal
    · have hge : p.mult c ≤ j := by omega
      have hd := Nat.sub_add_cancel hge
      have he : r+j*P = (image f (t+1) c).length+(r+(j-p.mult c)*P) := by
        rw [p.iterated_length]
        dsimp [P]
        dsimp [P] at hP
        nlinarith
      change p.charge (((image f (t+1) c) ++ subst (image f (t+1)) w).take (r+j*P)) = Z
      rw [he, List.take_append, List.take_of_length_le (by omega :
        (image f (t+1) c).length ≤ (image f (t+1) c).length+(r+(j-p.mult c)*P)),
        Nat.add_sub_cancel_left, p.charge_append]
      have hz : p.charge (image f (t+1) c) = 0 := by simp
      rw [hz, zero_add]
      apply ih (j-p.mult c)
      rw [subst_cons, he] at hj
      simp only [List.length_append] at hj
      dsimp [P] at hj
      omega

/-- The phase ray is proved for the actual growing source iterates. -/
theorem fixedWord_ray_of_samples (hp : Prolongable f) {t : ℕ} (h : p.CutSamples t) :
    ∃ r : ℕ, r < p.d*p.lam^t ∧
      ∀ j, p.height p.fixedWord (r+j*(p.d*p.lam^t)) = p.height p.fixedWord r := by
  obtain ⟨r,hr,Z,hs⟩ := h
  have hall (j : ℕ) : p.height p.fixedWord (r+j*(p.d*p.lam^t)) = Z := by
    let i := r+j*(p.d*p.lam^t)
    let K := t+1+(i+1)
    have hpre := image_prefix hp (show i+1 ≤ K by dsimp [K]; omega)
    have hi : i < (image f K 0).length := (p.image_growth i).trans_le hpre.length_le
    have hword : (image f K 0).take i = factor p.fixedWord 0 i := by
      rw [← p.fixedWord_prefix hp K, factor_take _ _ _ _ (by omega)]
    rw [height, ← hword]
    dsimp only [K]
    rw [image_add]
    apply p.samples_substituted_word hr hs
    simpa only [K, image_add] using hi
  refine ⟨r,hr,?_⟩
  intro j
  have hzero := hall 0
  simp only [zero_mul, add_zero] at hzero
  exact (hall j).trans hzero.symm

/-- Full infinite-word soundness, with its arbitrary one-sided preperiod. -/
theorem uap_of_original (hp : Prolongable f) {K : ℕ} (hK : 1 ≤ K)
    (h : OriginalCyclicBlockWitness f K) : UltimatelyAbelianPeriodic p.fixedWord := by
  obtain ⟨t,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : K ≠ 0)
  obtain ⟨r,hr,hray⟩ := p.fixedWord_ray_of_samples hp ((p.original_iff_samples t).mp h)
  apply p.uap_of_height_ray (P := p.d*p.lam^t)
  · exact Nat.mul_pos p.d_pos (pow_pos (by have := p.lam_ge_two; omega) _)
  · exact hray

end Parameters
end D5.S1.Words.RankOneMorphismIterationBound
