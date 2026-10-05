/- GID: D5/S1/Words/RankOneMorphismIterationBoundExtraction
   generality: G
   mirror-B: D5/B/S1/Words/RankOneMorphismIterationBoundExtraction
   mirror-E: none(waiver:actual-source-supertile-extraction)
   anchors: []
   digest: A normalized one-sided height ray yields actual source supertile witnesses. -/
import D5.S1.Words.RankOneMorphismIterationBoundSoundness
import D5.S1.Words.RankOneMorphismIterationBoundPeriod

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Words.RankOneMorphismIterationBound
open AbelianBorders.AbelianBorderQuestionDefs (factor)
namespace Parameters
variable {f : Morphism} (p : Parameters f)

theorem iterated_subst_length_multiple (t : ℕ) (w : Word) :
    p.d*p.lam^t ∣ (subst (image f (t+1)) w).length := by
  induction w with
  | nil => simp
  | cons c w ih =>
    rw [subst_cons, List.length_append, p.iterated_length]
    exact dvd_add (dvd_mul_left _ _) ih

theorem iterated_subst_charge (t : ℕ) (w : Word) :
    p.charge (subst (image f (t+1)) w) = 0 := by
  induction w with
  | nil => simp
  | cons c w ih => simp [ih]

include p in
/-- Each original letter really occurs in the actual first image. -/
theorem first_image_mem (c : Letter) : c ∈ f 0 := by
  apply List.count_pos_iff.mp
  change 0 < parikh (f 0) c
  fin_cases c
  · change 0 < parikh (f 0) 0
    rw [p.count_a]; simpa using Nat.mul_pos p.n_pos p.A_pos
  · change 0 < parikh (f 0) 1
    rw [p.count_b]; simpa using Nat.mul_pos p.n_pos p.B_pos

/-- An actual fixed-word phase ray at gcd length extracts the original finite
    image witnesses; no recurrence-phase assumption is inserted. -/
theorem samples_of_fixedWord_ray (hp : Prolongable f) (t r : ℕ)
    (hr : r < p.d*p.lam^t)
    (h : ∀ j, p.height p.fixedWord (r+j*(p.d*p.lam^t)) = p.height p.fixedWord r) :
    p.CutSamples t := by
  let P := p.d*p.lam^t
  refine ⟨r,hr,p.height p.fixedWord r,?_⟩
  intro c j hj
  obtain ⟨u,v,hc⟩ := List.mem_iff_append.mp (p.first_image_mem c)
  let U := image f (t+1) c
  let pre := subst (image f (t+1)) u
  let post := subst (image f (t+1)) v
  have hwhole : image f ((t+1)+1) 0 = pre ++ (U ++ post) := by
    rw [image_add, image_one, hc, subst_append, subst_cons]
  obtain ⟨k,hk⟩ := p.iterated_subst_length_multiple t u
  have hT : pre.length = k*P := by simpa only [pre, P, Nat.mul_comm] using hk
  have hpre0 : p.charge pre = 0 := p.iterated_subst_charge t u
  have hUlen : U.length = p.mult c*P := p.iterated_length t c
  have hoff : r+j*P < U.length := by
    have hP : 0 < P := Nat.mul_pos p.d_pos (pow_pos (by have := p.lam_ge_two; omega) _)
    have hrP : r < P := hr
    nlinarith
  have hwithin : pre.length+(r+j*P) ≤ (image f ((t+1)+1) 0).length := by
    rw [hwhole]
    simp only [List.length_append]
    omega
  have hfinite : p.height p.fixedWord (pre.length+(r+j*P)) =
      p.charge ((image f ((t+1)+1) 0).take (pre.length+(r+j*P))) := by
    rw [height, ← factor_take _ _ _ _ hwithin, p.fixedWord_prefix hp]
  have hray : p.height p.fixedWord (pre.length+(r+j*P)) = p.height p.fixedWord r := by
    rw [hT, show k*P+(r+j*P) = r+(k+j)*P by ring]
    exact h (k+j)
  rw [hwhole, List.take_append, List.take_of_length_le (by omega :
    pre.length ≤ pre.length+(r+j*P)), Nat.add_sub_cancel_left,
    List.take_append_of_le_length (by omega : r+j*P ≤ U.length),
    p.charge_append, hpre0, zero_add] at hfinite
  exact hfinite.symm.trans hray

end Parameters
end D5.S1.Words.RankOneMorphismIterationBound
