/- GID: D5/S3/Combinatorics/Permutation/KaselDisplacementLadderLower
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Permutation/KaselDisplacementLadderLower
   mirror-E: none(waiver:lower-bound-component-of-open-problem-resolution)
   anchors: []
   utility: none
   digest: The order-gadget obstruction forces Kasel displacement at least m minus two. -/

import D5.S3.Combinatorics.Permutation.KaselDisplacementLadderDefs
import D5.S3.Combinatorics.ErdosGrahamOrderGadget

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Permutation.KaselDisplacementLadderLower

open D5.S3.Combinatorics.Permutation.KaselDisplacementLadderDefs

private noncomputable def orderRank (X : Finset ℕ) (R : ℕ → ℕ → Prop) (v : ℕ) : ℕ := by
  classical
  exact (X.filter (fun w => R w v)).card

/-- Counting predecessors embeds any strict total order on a finite set into the naturals. -/
private lemma block_three : block 3 = 2 := by norm_num [block, Nat.clog]

private lemma block_fifteen : block 15 = 4 := by norm_num [block, Nat.clog]

private lemma finite_rank_order (X : Finset ℕ) (R : ℕ → ℕ → Prop)
    (hirr : ∀ a ∈ X, ¬ R a a)
    (htrans : ∀ a ∈ X, ∀ b ∈ X, ∀ c ∈ X, R a b → R b c → R a c)
    (htotal : ∀ a ∈ X, ∀ b ∈ X, a ≠ b → R a b ∨ R b a) :
    (∀ a ∈ X, ∀ b ∈ X, R a b ↔ orderRank X R a < orderRank X R b) ∧
      Set.InjOn (orderRank X R) X := by
  classical
  have hstrict : ∀ a ∈ X, ∀ b ∈ X, R a b → orderRank X R a < orderRank X R b := by
    intro a ha b hb hab
    apply Finset.card_lt_card
    have hsub : X.filter (fun w => R w a) ⊆ X.filter (fun w => R w b) := by
      intro w hw
      obtain ⟨hwX, hwa⟩ := Finset.mem_filter.mp hw
      exact Finset.mem_filter.mpr ⟨hwX, htrans w hwX a ha b hb hwa hab⟩
    apply (Finset.ssubset_iff_of_subset hsub).mpr
    exact ⟨a, Finset.mem_filter.mpr ⟨ha, hab⟩,
      fun h => hirr a ha (Finset.mem_filter.mp h).2⟩
  constructor
  · intro a ha b hb
    constructor
    · exact hstrict a ha b hb
    · intro hlt
      have hne : a ≠ b := by intro h; subst b; exact (Nat.lt_irrefl _) hlt
      rcases htotal a ha b hb hne with hab | hba
      · exact hab
      · exact False.elim (Nat.lt_asymm hlt (hstrict b hb a ha hba))
  · intro a ha b hb heq
    by_contra hne
    rcases htotal a ha b hb hne with hab | hba
    · have hlt := hstrict a ha b hb hab
      omega
    · have hlt := hstrict b hb a ha hba
      omega

private lemma lex_rank_order {X : Finset ℕ} {s r : ℕ → ℕ} (hvalid : Valid X s r) :
    (∀ a ∈ X, ∀ b ∈ X,
      lexLess s r a b ↔ orderRank X (lexLess s r) a < orderRank X (lexLess s r) b) ∧
      Set.InjOn (orderRank X (lexLess s r)) X := by
  apply finite_rank_order
  · intro a _
    simp [lexLess]
  · intro a _ b _ c _ hab hbc
    unfold lexLess at *
    rcases hab with hab | ⟨hab, hrab⟩ <;> rcases hbc with hbc | ⟨hbc, hrbc⟩
    all_goals omega
  · intro a ha b hb hne
    have hpair : ¬ (s a = s b ∧ r a = r b) := by
      intro h
      exact hne (hvalid.1 a ha b hb h.1 h.2)
    unfold lexLess
    omega

private lemma scale_facts (m : ℕ) (hm : 3 ≤ m) :
    2 ^ (2 * m - 1) = 2 * 4 ^ (m - 1) ∧
    2 ^ (2 * m) = 2 * (2 * 4 ^ (m - 1)) ∧
    2 * (2 * 4 ^ (m - 1)) = 4 ^ m ∧ 32 ≤ 2 * 4 ^ (m - 1) := by
  have hpred : 2 * m - 1 = 2 * (m - 1) + 1 := by omega
  have hdouble : 2 * m = 2 * (m - 1) + 2 := by omega
  have hmadd : m = (m - 1) + 1 := by omega
  have hlo : 16 ≤ 4 ^ (m - 1) := by
    have h := Nat.pow_le_pow_right (by decide : 0 < 4) (show 2 ≤ m - 1 by omega)
    norm_num at h
    exact h
  constructor
  · rw [hpred, pow_add, pow_mul]
    norm_num
    ring
  constructor
  · rw [hdouble, pow_add, pow_mul]
    norm_num
    ring
  constructor
  · conv_rhs => rw [hmadd, pow_add]
    norm_num
    ring
  · omega

private lemma large_stage (m : ℕ) (hm : 3 ≤ m) (s r : ℕ → ℕ)
    (hvalid : Valid (SA m) s r) (hnorm : Normalized (SA m) s) :
    m ≤ s 15 ∨ m ≤ s 16 := by
  classical
  by_contra hstage
  have h15 : s 15 < m := by omega
  have h16 : s 16 < m := by omega
  let M := 2 * 4 ^ (m - 1)
  obtain ⟨hpred, hdouble, htop, hM⟩ := scale_facts m hm
  change 2 ^ (2 * m - 1) = M at hpred
  change 2 ^ (2 * m) = 2 * M at hdouble
  change 2 * M = 4 ^ m at htop
  change 32 ≤ M at hM
  have hblock : ∀ v ∈ ErdosGrahamOrderGadget.block M, block v = 2 * m := by
    intro v hv
    obtain ⟨hvlo, hvhi⟩ := Finset.mem_Icc.mp hv
    apply block_eq_of_pow_pred_lt_le_pow (by omega)
    · rw [hpred]
      omega
    · rw [hdouble]
      exact hvhi
  have hmem : ∀ v ∈ ErdosGrahamOrderGadget.block M, v ∈ SA m := by
    intro v hv
    obtain ⟨hvlo, hvhi⟩ := Finset.mem_Icc.mp hv
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, ?_⟩
    rw [hblock v hv]
    exact ⟨by omega, ⟨m, by omega⟩⟩
  have hhigh : ∀ v ∈ ErdosGrahamOrderGadget.block M, m ≤ s v := by
    intro v hv
    have h := hnorm v (hmem v hv)
    rw [hblock v hv] at h
    simpa using h
  let rank := orderRank (SA m) (lexLess s r)
  obtain ⟨horder, hinj⟩ := lex_rank_order hvalid
  have hfree : ErdosGrahamOrderGadget.APFree M rank := by
    intro a b c ha hb hc hab hbc hap
    have h := hvalid.2 a (hmem a ha) b (hmem b hb) c (hmem c hc) hab hbc hap
    constructor
    · intro hmono
      exact h.1 ⟨(horder a (hmem a ha) b (hmem b hb)).mpr hmono.1,
        (horder b (hmem b hb) c (hmem c hc)).mpr hmono.2⟩
    · intro hmono
      exact h.2 ⟨(horder c (hmem c hc) b (hmem b hb)).mpr hmono.1,
        (horder b (hmem b hb) a (hmem a ha)).mpr hmono.2⟩
  have hguards : ErdosGrahamOrderGadget.Guards M rank := by
    intro x hx j hjlo hjhi
    have hxlo : 15 ≤ x := by rcases hx with rfl | rfl <;> omega
    have hxhi : x ≤ 16 := by rcases hx with rfl | rfl <;> omega
    have hxstage : s x < m := by rcases hx with rfl | rfl <;> assumption
    have hxmem : x ∈ SA m := by
      apply distinguished_subset (by omega)
      rcases hx with rfl | rfl <;> simp [distinguished]
    have hymem : M + j ∈ ErdosGrahamOrderGadget.block M := by
      simp only [ErdosGrahamOrderGadget.block, Finset.mem_Icc]
      omega
    have hzmem : 2 * M + 2 * j - x ∈ ErdosGrahamOrderGadget.block M := by
      simp only [ErdosGrahamOrderGadget.block, Finset.mem_Icc]
      omega
    have hxy : x < M + j := by omega
    have hyz : M + j < 2 * M + 2 * j - x := by omega
    have hap : x + (2 * M + 2 * j - x) = 2 * (M + j) := by omega
    have hxylex : lexLess s r x (M + j) :=
      Or.inl (lt_of_lt_of_le hxstage (hhigh (M + j) hymem))
    have hnot := (hvalid.2 x hxmem (M + j) (hmem _ hymem)
      (2 * M + 2 * j - x) (hmem _ hzmem) hxy hyz hap).1
    have hyznot : ¬ lexLess s r (M + j) (2 * M + 2 * j - x) :=
      fun h => hnot ⟨hxylex, h⟩
    have hrne : rank (M + j) ≠ rank (2 * M + 2 * j - x) := by
      intro heq
      have heqv := hinj (hmem _ hymem) (hmem _ hzmem) heq
      omega
    have hrnot : ¬ rank (M + j) < rank (2 * M + 2 * j - x) :=
      fun h => hyznot ((horder _ (hmem _ hymem) _ (hmem _ hzmem)).mpr h)
    omega
  apply ErdosGrahamOrderGadget.result M (by omega)
  refine ⟨rank, ?_, hfree, hguards⟩
  intro a ha b hb heq
  exact hinj (hmem a ha) (hmem b hb) heq

/-- Every valid normalized scheme has a distinguished value with displacement at least m - 2. -/
theorem lower_bound (m : ℕ) (hm : 2 ≤ m) : ∀ s r : ℕ → ℕ, Valid (SA m) s r → Normalized (SA m) s →
    ∃ v ∈ distinguished, block v / 2 + (m - 2) ≤ s v := by
  intro s r hvalid hnorm
  by_cases hm2 : m = 2
  · subst m
    have hmem : 3 ∈ distinguished := by simp [distinguished]
    refine ⟨3, hmem, ?_⟩
    have h := hnorm 3 (distinguished_subset hm hmem)
    simpa [block_three] using h
  · have hm3 : 3 ≤ m := by omega
    rcases large_stage m hm3 s r hvalid hnorm with h15 | h16
    · refine ⟨15, by simp [distinguished], ?_⟩
      rw [block_fifteen]
      omega
    · refine ⟨16, by simp [distinguished], ?_⟩
      have hb16 : block 16 = 4 := by norm_num [block, Nat.clog]
      rw [hb16]
      omega

end D5.S3.Combinatorics.Permutation.KaselDisplacementLadderLower
