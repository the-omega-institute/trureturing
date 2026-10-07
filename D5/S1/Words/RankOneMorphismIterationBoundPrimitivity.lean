/- GID: D5/S1/Words/RankOneMorphismIterationBoundPrimitivity
   generality: G
   mirror-B: D5/B/S1/Words/RankOneMorphismIterationBoundPrimitivity
   mirror-E: none(waiver:actual-uniform-primitivity)
   anchors: []
   utility: none
   digest: Primitivity proved for the actual indexed uniform morphism. -/
import D5.S1.Words.RankOneMorphismIterationBoundInfinitePresentation

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Words.RankOneMorphismIterationBound
namespace Parameters
variable {f : Morphism} (p : Parameters f)

/-- A long slice contains a complete source block. This is used only on
    the actual partition into E(f(c)) blocks below. -/
private theorem mem_long_slice {α : Type} (s : α) (M : ℕ)
    (bs : List (List α)) (hb : ∀ b ∈ bs, b.length ≤ M ∧ s ∈ b)
    (i L : ℕ) (hin : i+L ≤ bs.flatten.length) (hL : 2*M < L) :
    s ∈ (bs.flatten.drop i).take L := by
  induction bs generalizing i with
  | nil => simp at hin; omega
  | cons b bs ih =>
    obtain ⟨hbM,hbs⟩ := hb b (by simp)
    have htail : ∀ c ∈ bs, c.length ≤ M ∧ s ∈ c := by
      intro c hc; exact hb c (by simp [hc])
    simp only [List.flatten_cons, List.length_append] at hin ⊢
    by_cases hbi : b.length ≤ i
    · rw [List.drop_append, List.drop_of_length_le hbi, List.nil_append]
      apply ih htail (i-b.length)
      omega
    · have hi : i < b.length := by omega
      rw [List.drop_append_of_le_length (by omega), List.take_append]
      have hd : (b.drop i).length ≤ M := by simp only [List.length_drop]; omega
      cases bs with
      | nil => simp at hin; omega
      | cons c cs =>
        obtain ⟨hcM,hcs⟩ := htail c (by simp)
        simp only [List.flatten_cons]
        rw [List.take_append, List.take_of_length_le (by omega :
          c.length ≤ L-(b.drop i).length)]
        exact List.mem_append_right _ (List.mem_append_left _ hcs)

private theorem uniform_slice (k : ℕ) (γ : State f) :
    ((expand (f := f) (image f k γ.1)).drop (p.lam^k*γ.2.val)).take (p.lam^k) =
      image p.uniform k γ := by
  have he : expand (f := f) (image f k γ.1) =
      subst (image p.uniform k) (indexed (f := f) γ.1) := by
    simpa only [subst_cons, subst_nil, List.append_nil, expand_cons, expand_nil,
      List.append_nil] using (p.iterated_expand k [γ.1]).symm
  rw [he]
  have hγ : γ.2.val < (indexed (f := f) γ.1).length := by simpa using γ.2.isLt
  have hlen := uniform_subst_length (image p.uniform k) (p.lam^k)
    (p.uniform_iter_length k) (indexed (f := f) γ.1)
  apply List.ext_getElem
  · simp only [List.length_take, List.length_drop, hlen, p.uniform_iter_length]
    apply Nat.min_eq_left
    have hp : 0 < p.lam^k := pow_pos (by have := p.lam_ge_two; omega) _
    have hm : p.lam^k*γ.2.val+p.lam^k ≤ p.lam^k*(indexed (f := f) γ.1).length := by nlinarith
    omega
  · intro j hj hj'
    simp only [List.getElem_take, List.getElem_drop]
    have hg := uniform_subst_get (image p.uniform k) (p.lam^k)
      (p.uniform_iter_length k) (indexed (f := f) γ.1) γ.2.val j hγ
      (by simpa only [p.uniform_iter_length] using hj')
    simpa only [indexed, List.getElem_ofFn, Nat.add_comm] using hg

include p in
theorem source_letter_mem (c b : Letter) : b ∈ f c := by
  apply List.count_pos_iff.mp
  change 0 < parikh (f c) b
  have hm : 0 < p.mult c := by fin_cases c <;> simp [mult, p.n_pos, p.m_pos]
  fin_cases b
  · change 0 < parikh (f c) 0
    rw [p.count_a]; exact Nat.mul_pos hm p.A_pos
  · change 0 < parikh (f c) 1
    rw [p.count_b]; exact Nat.mul_pos hm p.B_pos

/-- Every state occurs in one effective common iterate of every state.
    No primitivity assumption about h is imported into this result. -/
theorem uniform_primitive : ∃ k : ℕ, 0 < k ∧
    ∀ γ δ : State f, δ ∈ image p.uniform k γ := by
  let M := p.lam * max (f 0).length (f 1).length
  let k := 2*M+1
  have hk : 0 < k := by dsimp [k]; omega
  have hlarge : 2*M < p.lam^k := by
    have hh := (Nat.lt_two_pow_self : k < 2^k).trans_le (Nat.pow_le_pow_left p.lam_ge_two k)
    exact (show 2*M < k by dsimp [k]; omega).trans hh
  refine ⟨k,hk,?_⟩
  intro γ δ
  let bs := (image f (k-1) γ.1).map (fun c => expand (f := f) (f c))
  have hflat : bs.flatten = expand (f := f) (image f k γ.1) := by
    dsimp [bs]
    rw [← List.flatMap_def]
    change subst (fun c => expand (f := f) (f c)) (image f (k-1) γ.1) = _
    have hh : ∀ w : Word, subst (fun c => expand (f := f) (f c)) w =
        expand (f := f) (subst f w) := by
      intro w; induction w with
      | nil => rfl
      | cons c w ih => simp [ih]
    rw [hh, ← image_succ, Nat.sub_add_cancel (by omega : 1 ≤ k)]
  have hb : ∀ b ∈ bs, b.length ≤ M ∧ δ ∈ b := by
    intro b hb
    obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hb
    constructor
    · rw [p.expand_image_length]
      apply Nat.mul_le_mul_left
      fin_cases c
      · exact Nat.le_max_left _ _
      · exact Nat.le_max_right _ _
    · exact List.mem_flatMap.mpr ⟨δ.1,p.source_letter_mem c δ.1,
        by simp [indexed, List.mem_ofFn]⟩
  have hin : p.lam^k*γ.2.val+p.lam^k ≤ bs.flatten.length := by
    rw [hflat]
    have he : expand (f := f) (image f k γ.1) = subst (image p.uniform k) (indexed (f := f) γ.1) := by
      simpa only [subst_cons,subst_nil,List.append_nil,expand_cons,expand_nil,List.append_nil] using (p.iterated_expand k [γ.1]).symm
    rw [he]
    simp only [expand_cons, expand_nil, List.append_nil, subst_cons, subst_nil,
      List.append_nil, uniform_subst_length (image p.uniform k) (p.lam^k)
        (p.uniform_iter_length k), indexed_length]
    have hi := γ.2.isLt
    nlinarith
  have hm := mem_long_slice δ M bs hb (p.lam^k*γ.2.val) (p.lam^k) hin hlarge
  rw [hflat, p.uniform_slice] at hm
  exact hm

end Parameters
end D5.S1.Words.RankOneMorphismIterationBound
