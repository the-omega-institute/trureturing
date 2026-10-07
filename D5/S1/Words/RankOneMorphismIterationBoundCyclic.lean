/- GID: D5/S1/Words/RankOneMorphismIterationBoundCyclic
   generality: G
   mirror-B: D5/B/S1/Words/RankOneMorphismIterationBoundCyclic
   mirror-E: none(waiver:consumed-cyclic-source-semantics)
   anchors: []
   utility: none
   digest: Exact complete block decompositions and cyclic source prefix heights. -/
import D5.S1.Words.RankOneMorphismIterationBoundArithmetic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Words.RankOneMorphismIterationBound
namespace Parameters
variable {f : Morphism} (p : Parameters f)

/-- Cut the complete finite word into the specified number of consecutive blocks. -/
def cutBlocks (P : ℕ) : ℕ → Word → List Word
  | 0, _ => []
  | n+1, w => w.take P :: cutBlocks P n (w.drop P)

theorem cutBlocks_length (P n : ℕ) (w : Word) : (cutBlocks P n w).length = n := by
  induction n generalizing w <;> simp [cutBlocks, *]

theorem cutBlocks_flatten (P n : ℕ) (w : Word) (hl : w.length = n * P) :
    (cutBlocks P n w).flatten = w := by
  induction n generalizing w with
  | zero => simp_all [cutBlocks]
  | succ n ih =>
    simp only [Nat.add_mul, one_mul] at hl
    simp only [cutBlocks, List.flatten_cons]
    rw [ih, List.take_append_drop]
    simp only [List.length_drop]
    omega

theorem cutBlocks_mem_length (P n : ℕ) (w : Word) (hl : w.length = n * P) :
    ∀ b ∈ cutBlocks P n w, b.length = P := by
  induction n generalizing w with
  | zero => simp [cutBlocks]
  | succ n ih =>
    simp only [Nat.add_mul, one_mul] at hl
    intro b hb
    have hp : P ≤ w.length := by omega
    simp only [cutBlocks, List.mem_cons] at hb
    rcases hb with rfl | hb
    · simp [List.length_take, Nat.min_eq_left hp]
    · exact ih (w.drop P) (by simp only [List.length_drop]; omega) b hb

theorem charge_take_add (w : Word) (r s : ℕ) :
    p.charge (w.take (r+s)) = p.charge (w.take r) + p.charge ((w.drop r).take s) := by
  rw [← p.charge_append, List.take_add]

theorem cutBlocks_zero (P n : ℕ) (w : Word)
    (h : ∀ j, j ≤ n → p.charge (w.take (j*P)) = 0) :
    ∀ b ∈ cutBlocks P n w, p.charge b = 0 := by
  induction n generalizing w with
  | zero => simp [cutBlocks]
  | succ n ih =>
    have hP : p.charge (w.take P) = 0 := by simpa using h 1 (by omega)
    have ht : ∀ j, j ≤ n → p.charge ((w.drop P).take (j*P)) = 0 := by
      intro j hj
      have hs := h (j+1) (by omega)
      rw [show (j+1)*P = P+j*P by ring, p.charge_take_add, hP, zero_add] at hs
      exact hs
    intro b hb
    simp only [cutBlocks, List.mem_cons] at hb
    rcases hb with rfl | hb
    · exact hP
    · exact ih (w.drop P) ht b hb

theorem parikh_flatten_constant (bs : List Word) (P : Letter → ℕ)
    (h : ∀ b ∈ bs, parikh b = P) (c : Letter) :
    parikh bs.flatten c = bs.length * P c := by
  induction bs with
  | nil => simp
  | cons b bs ih =>
    simp only [List.flatten_cons, parikh_append, List.length_cons]
    rw [h b (by simp), ih (by intro b hb; exact h b (by simp [hb]))]
    ring

theorem length_flatten_constant (bs : List Word) (P : Letter → ℕ)
    (h : ∀ b ∈ bs, parikh b = P) :
    bs.flatten.length = bs.length * (P 0 + P 1) := by
  rw [← parikh_binary_length, parikh_flatten_constant bs P h 0,
    parikh_flatten_constant bs P h 1]
  ring

theorem block_charge_zero {w : Word} {P : Letter → ℕ}
    (hw : p.charge w = 0) (hb : Blocks w P) :
    ∃ bs : List Word, bs.flatten = w ∧ bs ≠ [] ∧
      ∀ b ∈ bs, b ≠ [] ∧ b.length = P 0 + P 1 ∧ p.charge b = 0 := by
  obtain ⟨bs, hbs, hn, hp⟩ := hb
  have hc := parikh_flatten_constant bs P (fun b hb => (hp b hb).2)
  have hz : (bs.length : ℤ) * ((p.B : ℤ)*P 0 - (p.A : ℤ)*P 1) = 0 := by
    rw [← hbs] at hw
    dsimp [charge] at hw
    rw [hc 0, hc 1] at hw
    push_cast at hw
    nlinarith [hw]
  have hn' : (bs.length : ℤ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (List.length_pos_iff.mpr hn))
  have hc0 := (mul_eq_zero.mp hz).resolve_left hn'
  refine ⟨bs, hbs, hn, ?_⟩
  intro b hb
  have hv := (hp b hb).2
  refine ⟨(hp b hb).1, ?_, ?_⟩
  · rw [← parikh_binary_length, congrFun hv 0, congrFun hv 1]
  · dsimp [charge]; rw [congrFun hv 0, congrFun hv 1]; exact hc0

/-- Every complete block boundary has height zero, including the last boundary. -/
theorem zero_block_boundaries (bs : List Word) (P : ℕ)
    (h : ∀ b ∈ bs, b.length = P ∧ p.charge b = 0) :
    ∀ j, j ≤ bs.length → p.charge (bs.flatten.take (j*P)) = 0 := by
  induction bs with
  | nil =>
    intro j hj
    have : j = 0 := by simpa using hj
    simp [this]
  | cons b bs ih =>
    intro j hj
    have hb := h b (by simp)
    have htail : ∀ b ∈ bs, b.length = P ∧ p.charge b = 0 := by
      intro b hb; exact h b (by simp [hb])
    cases j with
    | zero => simp
    | succ j =>
      rw [List.flatten_cons, show (j+1)*P = b.length+j*P by rw [hb.1]; ring,
        List.take_append, List.take_of_length_le (by omega : b.length ≤ b.length+j*P),
        Nat.add_sub_cancel_left, charge_append, hb.2, zero_add]
      exact ih htail j (by simp only [List.length_cons] at hj; omega)

/-- Reconstruct the source-normalized exact block vector from all boundary heights. -/
theorem blocks_of_boundaries (t n : ℕ) (w : Word) (hn : 0 < n)
    (hl : w.length = n*(p.d*p.lam^t))
    (hz : ∀ j, j ≤ n → p.charge (w.take (j*(p.d*p.lam^t))) = 0) :
    Blocks w (fun c => p.lam^t*(if c = 0 then p.A else p.B)) := by
  refine ⟨cutBlocks (p.d*p.lam^t) n w, cutBlocks_flatten _ _ _ hl, ?_, ?_⟩
  · intro hnil
    have hlen := congrArg List.length hnil
    rw [cutBlocks_length] at hlen
    simp at hlen
    omega
  · intro b hb
    have hlen := cutBlocks_mem_length _ _ _ hl b hb
    have hpos : 0 < b.length := by
      rw [hlen]; exact Nat.mul_pos p.d_pos (pow_pos (by have := p.lam_ge_two; omega) _)
    refine ⟨List.length_pos_iff.mp hpos, ?_⟩
    exact (p.charge_zero_iff hlen).mp (p.cutBlocks_zero _ _ _ hz b hb)

/-- Exact finite sampled-height predicate at the gcd-length cut. -/
def CutSamples (t : ℕ) : Prop :=
  ∃ r : ℕ, r < p.d*p.lam^t ∧ ∃ Z : ℤ,
    ∀ c : Letter, ∀ j : ℕ, j < p.mult c →
      p.charge ((image f (t+1) c).take (r+j*(p.d*p.lam^t))) = Z

/-- The actual normalized four words, including both entire rotated words. -/
def NormalizedWitness (t : ℕ) : Prop :=
  ∃ r : ℕ, r < p.d*p.lam^t ∧
    AbelianEq ((image f (t+1) 0).take r) ((image f (t+1) 1).take r) ∧
    ∀ c : Letter, Blocks ((image f (t+1) c).drop r ++ (image f (t+1) c).take r)
      (fun b => p.lam^t*(if b = 0 then p.A else p.B))

theorem normalized_original {t : ℕ} (h : p.NormalizedWitness t) :
    OriginalCyclicBlockWitness f (t+1) := by
  obtain ⟨r, hr, hab, hblocks⟩ := h
  refine ⟨(image f (t+1) 0).take r, (image f (t+1) 0).drop r,
    (image f (t+1) 1).take r, (image f (t+1) 1).drop r,
    (List.take_append_drop r _).symm, (List.take_append_drop r _).symm, hab,
    _, hblocks 0, hblocks 1⟩

end Parameters
end D5.S1.Words.RankOneMorphismIterationBound
