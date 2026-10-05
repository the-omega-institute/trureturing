/- GID: D5/S1/Words/RankOneMorphismIterationBoundInfinitePresentation
   generality: G
   mirror-B: D5/B/S1/Words/RankOneMorphismIterationBoundInfinitePresentation
   mirror-E: none(waiver:actual-indexed-fixed-word)
   anchors: []
   digest: Indexed uniform presentation tied to the actual original fixed word. -/
import D5.S1.Words.RankOneMorphismIterationBoundDigits
import D5.S1.Words.RankOneMorphismIterationBoundFixedWord

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Words.RankOneMorphismIterationBound
namespace Parameters
variable {f : Morphism} (p : Parameters f)

theorem expand_prefix {u v : Word} (h : u <+: v) :
    expand (f := f) u <+: expand (f := f) v := by
  obtain ⟨w,rfl⟩ := h
  rw [expand_append]
  exact List.prefix_append _ _

include p in
theorem expand_length_ge (w : Word) : w.length ≤ (expand (f := f) w).length := by
  induction w with
  | nil => simp
  | cons c w ih =>
    have hm : 0 < p.mult c := by fin_cases c <;> simp [mult, p.n_pos, p.m_pos]
    have hc : 0 < (f c).length := by rw [p.image_length]; exact Nat.mul_pos hm p.d_pos
    simp only [expand_cons, List.length_append, indexed_length, List.length_cons]
    omega

/-- Actual E(x): the unique limit of the expansions of the original source
    iterates. Every state retains its source letter and real image offset. -/
def indexedFixedWord (i : ℕ) : State f :=
  (expand (f := f) (image f (i+1) 0))[i]'((p.image_growth i).trans_le (p.expand_length_ge _))

theorem indexedFixedWord_eq_image (hp : Prolongable f) (k i : ℕ)
    (hi : i < (expand (f := f) (image f k 0)).length) :
    p.indexedFixedWord i = (expand (f := f) (image f k 0))[i] := by
  have hk := expand_prefix (f := f) (image_prefix hp (Nat.le_max_left k (i+1)))
  have hi' := expand_prefix (f := f) (image_prefix hp (Nat.le_max_right k (i+1)))
  exact (hi'.getElem ((p.image_growth i).trans_le (p.expand_length_ge _))).trans (hk.getElem hi).symm

theorem indexedFixedWord_prefix (hp : Prolongable f) (k : ℕ) :
    List.ofFn (fun i : Fin (expand (f := f) (image f k 0)).length => p.indexedFixedWord i.val) =
      expand (f := f) (image f k 0) := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp only [List.getElem_ofFn]
    exact p.indexedFixedWord_eq_image hp k i hj

/-- Actual charge coding, at every original one-sided position. -/
theorem indexedFixedWord_coding (hp : Prolongable f) (i : ℕ) :
    p.coding (p.indexedFixedWord i) = p.height p.fixedWord i := by
  have he : (expand (f := f) (image f (i+1) 0)).map p.coding =
      p.heights (image f (i+2) 0) := by
    rw [p.coding_expand]
    rfl
  have hiE : i < (expand (f := f) (image f (i+1) 0)).length :=
    (p.image_growth i).trans_le (p.expand_length_ge _)
  have hiF : i < (image f (i+2) 0).length :=
    (p.image_growth i).trans_le (image_prefix_succ hp (i+1)).length_le
  have hs := congrArg (fun w : List ℤ => w[i]?) he
  simp only [List.getElem?_map, List.getElem?_eq_getElem hiE, Option.map_some,
    heights, List.getElem?_map, List.getElem?_range hiF, Option.map_some,
    Option.some.injEq] at hs
  change p.coding (p.indexedFixedWord i) = p.charge (AbelianBorders.AbelianBorderQuestionDefs.factor p.fixedWord 0 i)
  dsimp only [indexedFixedWord]
  rw [hs]
  have hpref := p.fixedWord_prefix hp (i+2)
  rw [← hpref, factor_take _ _ _ _ (by omega)]

/-- Genuine one-sided uniform-copy semantics at every state occurrence. -/
theorem indexedFixedWord_copy (hp : Prolongable f) (i t j : ℕ) (hj : j < p.lam^t) :
    p.indexedFixedWord (p.lam^t*i+j) =
      (image p.uniform t (p.indexedFixedWord i))[j]'(by rw [p.uniform_iter_length]; exact hj) := by
  let k := i+1
  let w := expand (f := f) (image f k 0)
  have hi : i < w.length := (p.image_growth i).trans_le (p.expand_length_ge _)
  have hcomm : subst (image p.uniform t) w = expand (f := f) (image f (t+k) 0) := by
    rw [p.iterated_expand, ← image_add]
  have hlen : p.lam^t*i+j < (subst (image p.uniform t) w).length := by
    rw [uniform_subst_length (image p.uniform t) (p.lam^t) (p.uniform_iter_length t)]
    nlinarith
  have hout := p.indexedFixedWord_eq_image hp (t+k) (p.lam^t*i+j) (by rw [← hcomm]; exact hlen)
  have hget := uniform_subst_get (image p.uniform t) (p.lam^t) (p.uniform_iter_length t) w i j hi hj
  have hin := p.indexedFixedWord_eq_image hp k i hi
  have hin' : w[i] = p.indexedFixedWord i := hin.symm
  simp only [← hcomm] at hout
  simp only [hin'] at hget
  exact hout.trans hget

end Parameters
end D5.S1.Words.RankOneMorphismIterationBound
