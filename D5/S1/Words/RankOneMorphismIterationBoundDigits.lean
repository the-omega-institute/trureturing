/- GID: D5/S1/Words/RankOneMorphismIterationBoundDigits
   generality: G
   mirror-B: D5/B/S1/Words/RankOneMorphismIterationBoundDigits
   mirror-E: none(waiver:consumed-source-digit-semantics)
   anchors: []
   utility: none
   digest: Retained MSB digits and exact finite source-height evaluation. -/
import D5.S1.Words.RankOneMorphismIterationBoundAutomaton
import D5.S1.Words.RankOneMorphismIterationBoundCyclic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Words.RankOneMorphismIterationBound

theorem uniform_subst_length {α β : Type*} (g : α → List β) (P : ℕ)
    (hg : ∀ a, (g a).length = P) (w : List α) :
    (subst g w).length = P * w.length := by
  induction w with
  | nil => simp
  | cons a w ih => simp [hg, ih]; ring

/-- Uniform rectangular indexing is proved directly from the upstream append
    laws; the private GoldenSubstFixed declarations are not used or copied. -/
theorem uniform_subst_get {α β : Type*} (g : α → List β) (P : ℕ)
    (hg : ∀ a, (g a).length = P) (w : List α) (i j : ℕ)
    (hi : i < w.length) (hj : j < P) :
    (subst g w)[P*i+j]'(by rw [uniform_subst_length g P hg]; nlinarith) =
      (g (w[i]))[j]'(by rw [hg]; exact hj) := by
  induction w generalizing i with
  | nil => simp at hi
  | cons a w ih =>
    cases i with
    | zero =>
      simp only [mul_zero, zero_add, List.getElem_cons_zero, subst_cons]
      rw [List.getElem_append_left (by rw [hg]; exact hj)]
    | succ i =>
      simp only [List.getElem_cons_succ, subst_cons]
      rw [List.getElem_append_right (by rw [hg]; nlinarith)]
      simp only [hg]
      have he : P*(i+1)+j-P = P*i+j := by simp only [Nat.mul_add, mul_one]; omega
      simpa only [he] using ih i (by simp only [List.length_cons] at hi; omega)

namespace Parameters
variable {f : Morphism} (p : Parameters f)

/-- MSB first; the length is retained even when initial digits are zero. -/
def digitValue : List (Fin p.lam) → ℕ
  | [] => 0
  | j :: v => j.val * p.lam ^ v.length + digitValue v

theorem digitValue_lt (v : List (Fin p.lam)) : p.digitValue v < p.lam ^ v.length := by
  induction v with
  | nil => simp [digitValue]
  | cons j v ih =>
    simp only [digitValue, List.length_cons, pow_succ]
    have hj := j.isLt
    have hp : 0 < p.lam ^ v.length := pow_pos (by have := p.lam_ge_two; omega) _
    nlinarith

theorem digits_exist (t u : ℕ) (hu : u < p.lam ^ t) :
    ∃ v : List (Fin p.lam), v.length = t ∧ p.digitValue v = u := by
  induction t generalizing u with
  | zero =>
    have : u = 0 := by simpa using hu
    exact ⟨[], rfl, this.symm⟩
  | succ t ih =>
    have hpow : 0 < p.lam ^ t := pow_pos (by have := p.lam_ge_two; omega) _
    have hlead : u / p.lam ^ t < p.lam := by
      apply (Nat.div_lt_iff_lt_mul hpow).mpr
      simpa only [pow_succ, Nat.mul_comm] using hu
    obtain ⟨v, hv, hval⟩ := ih (u % p.lam ^ t) (Nat.mod_lt _ hpow)
    refine ⟨⟨u / p.lam ^ t, hlead⟩ :: v, by simp [hv], ?_⟩
    simp only [digitValue, hv, hval]
    exact Nat.div_add_mod' _ _

theorem uniform_iter_length (t : ℕ) (q : State f) :
    (image p.uniform t q).length = p.lam ^ t := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [image_succ, uniform_subst_length p.uniform p.lam p.uniform_length, ih]
    rw [pow_succ]; ring

/-- Exact MSB evaluation in the actual uniform iterate. -/
theorem uniform_iter_eval (v : List (Fin p.lam)) (q : State f) :
    (image p.uniform v.length q)[p.digitValue v]'(by rw [p.uniform_iter_length]; exact p.digitValue_lt v) =
      p.heightMachine.toDFA.evalFrom q v := by
  induction v generalizing q with
  | nil => simp [digitValue]
  | cons j v ih =>
    have he := image_add p.uniform v.length 1 q
    simp only [image_one] at he
    simp only [List.length_cons, digitValue, DFA.evalFrom_cons]
    simp only [he]
    have hget := uniform_subst_get (image p.uniform v.length) (p.lam^v.length)
      (p.uniform_iter_length v.length) (p.uniform q) j.val (p.digitValue v)
      (by simpa using j.isLt) (p.digitValue_lt v)
    simp only [Nat.mul_comm (p.lam^v.length) j.val] at hget
    rw [hget]
    simpa [heightMachine, uniform] using ih (p.transition q j)

/-- The decisive finite source samples are the actual Moore outputs, not a
    proxy word or an assumption about cofinal states. -/
theorem source_digit_height (v : List (Fin p.lam)) (c : Letter)
    (i : ℕ) (hi : i < (f c).length) :
    p.charge ((image f (v.length+1) c).take (p.lam^v.length*i + p.digitValue v)) =
      p.coding (p.heightMachine.toDFA.evalFrom ⟨c, ⟨i, hi⟩⟩ v) := by
  have hget := uniform_subst_get (image p.uniform v.length) (p.lam^v.length)
    (p.uniform_iter_length v.length) (indexed (f := f) c) i (p.digitValue v)
    (by simpa using hi) (p.digitValue_lt v)
  have hlen : p.lam ^ v.length * i + p.digitValue v < (image f (v.length+1) c).length := by
    rw [p.image_length] at hi
    rw [p.iterated_length]
    have hv := p.digitValue_lt v
    nlinarith
  have hs := congrArg (fun w : List ℤ => w[p.lam^v.length*i + p.digitValue v]?)
    (p.finite_height_identity v.length c)
  have hls : p.lam^v.length*i + p.digitValue v <
      (subst (image p.uniform v.length) (indexed (f := f) c)).length := by
    rw [uniform_subst_length (image p.uniform v.length) (p.lam^v.length)
      (p.uniform_iter_length v.length), indexed_length]
    nlinarith [p.digitValue_lt v]
  simp only [List.getElem?_map, List.getElem?_eq_getElem hls, Option.map_some,
    heights, List.getElem?_map, List.getElem?_range hlen, Option.map_some,
    Option.some.injEq] at hs
  rw [hget] at hs
  simp only [indexed, List.getElem_ofFn] at hs
  rw [p.uniform_iter_eval] at hs
  exact hs.symm

end Parameters
end D5.S1.Words.RankOneMorphismIterationBound
