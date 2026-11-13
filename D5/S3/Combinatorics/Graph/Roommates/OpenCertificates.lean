/- GID: D5/S3/Combinatorics/Graph/Roommates/OpenCertificates
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/Roommates/OpenCertificates
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Data.Fintype.Perm]
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Combinatorics/Graph/Roommates/OpenCertificates.count_three_bound; premises=D5/S3/Combinatorics/Graph/Roommates/OpenCertificates.exclusive_triangle_not_certified
   digest: Interval certificates, paired-word lower bounds and exclusive-triangle profile counts. -/

import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic
import Mathlib.Data.Fin.Rev
import Mathlib.Data.Fintype.Card

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace D5.S3.Combinatorics.Graph.Roommates.OpenCertificates
abbrev Ranking := Equiv.Perm (Fin 4)
abbrev Word (m : ℕ) := Fin m → Ranking

/-- Rank of an assigned signed offset; zero is single and has rank four. -/
def offsetRank (r : Ranking) (d : ℤ) : ℕ :=
  if d = 1 then (r 0).val else if d = 2 then (r 1).val
  else if d = -1 then (r 2).val else if d = -2 then (r 3).val else 4

/-- Requests retain their actual ranks when the partner lies outside the interval.
Target injectivity includes those exterior integer targets. -/
structure Certificate {m : ℕ} (w : Word m) (d : Fin m → ℤ) : Prop where
  bounded : ∀ i, -2 ≤ d i ∧ d i ≤ 2
  reciprocal : ∀ i j, d i ≠ 0 → (i.val : ℤ) + d i = j.val → d j = -d i
  target_injective : ∀ i j, d i ≠ 0 → d j ≠ 0 →
    (i.val : ℤ) + d i = (j.val : ℤ) + d j → i = j
  nonblocking : ∀ i j, i.val < j.val → j.val ≤ i.val + 2 →
    d i = (j.val : ℤ) - i.val ∨
    offsetRank (w i) (d i) < offsetRank (w i) ((j.val : ℤ) - i.val) ∨
    offsetRank (w j) (d j) < offsetRank (w j) ((i.val : ℤ) - j.val)

/-- This subtype counts words, with an existential certificate, once per word. -/
def CertifiedWord (m : ℕ) := {w : Word m // ∃ d, Certificate w d}

instance (m : ℕ) : Fintype (CertifiedWord m) := by
  classical
  unfold CertifiedWord
  infer_instance

/-- Number of certified profiles, not the number of certificates. -/
def count (m : ℕ) : ℕ := Fintype.card (CertifiedWord m)

/-- Translate the interval beginning at s to zero-based local coordinates. -/
def intervalIndex {n m : ℕ} (s : ℕ) (h : s + m ≤ n) (i : Fin m) : Fin n :=
  ⟨s + i.val, by omega⟩

/-- Restriction preserves exterior targets as well as internal matching and stability. -/
theorem certificate_restrict {n m : ℕ} {w : Word n} {d : Fin n → ℤ}
    (hc : Certificate w d) (s : ℕ) (h : s + m ≤ n) :
    Certificate (fun i => w (intervalIndex s h i)) (fun i => d (intervalIndex s h i)) := by
  constructor
  · intro i
    exact hc.bounded _
  · intro i j hdi he
    apply hc.reciprocal (intervalIndex s h i) (intervalIndex s h j) hdi
    change ((s + i.val : ℕ) : ℤ) + d (intervalIndex s h i) = (s + j.val : ℕ)
    simp only [Nat.cast_add]
    omega
  · intro i j hdi hdj he
    have ht : (↑(intervalIndex s h i).val : ℤ) + d (intervalIndex s h i) =
        ↑(intervalIndex s h j).val + d (intervalIndex s h j) := by
      change ((s + i.val : ℕ) : ℤ) + d (intervalIndex s h i) =
        ((s + j.val : ℕ) : ℤ) + d (intervalIndex s h j)
      simp only [Nat.cast_add]
      omega
    have hi := congrArg Fin.val (hc.target_injective _ _ hdi hdj ht)
    apply Fin.ext
    simp only [intervalIndex, Fin.val_mk] at hi
    omega
  · intro i j hij hdist
    have hi : (intervalIndex s h i).val < (intervalIndex s h j).val := by
      simp only [intervalIndex, Fin.val_mk]
      omega
    have hj : (intervalIndex s h j).val ≤ (intervalIndex s h i).val + 2 := by
      simp only [intervalIndex, Fin.val_mk]
      omega
    have hh := hc.nonblocking _ _ hi hj
    have he₁ : ((intervalIndex s h j).val : ℤ) - (intervalIndex s h i).val =
        (j.val : ℤ) - i.val := by simp [intervalIndex]
    have he₂ : ((intervalIndex s h i).val : ℤ) - (intervalIndex s h j).val =
        (i.val : ℤ) - j.val := by simp [intervalIndex]
    simpa only [he₁, he₂] using hh

/-- Word restriction does not choose or count matching witnesses. -/
def restrict {n m : ℕ} (s : ℕ) (h : s + m ≤ n) (w : CertifiedWord n) : CertifiedWord m := by
  refine ⟨fun i => w.val (intervalIndex s h i), ?_⟩
  obtain ⟨d, hd⟩ := w.property
  exact ⟨fun i => d (intervalIndex s h i), certificate_restrict hd s h⟩

def split (m k : ℕ) (w : CertifiedWord (m + k)) : CertifiedWord m × CertifiedWord k :=
  (restrict 0 (by omega) w, restrict m (by omega) w)

private theorem split_injective (m k : ℕ) : Function.Injective (split m k) := by
  intro x y h
  apply Subtype.ext
  funext i
  by_cases hi : i.val < m
  · have he := congrArg (fun p : CertifiedWord m × CertifiedWord k => p.1.val ⟨i.val, hi⟩) h
    simpa only [split, restrict, intervalIndex, Nat.zero_add] using he
  · have he := congrArg (fun p : CertifiedWord m × CertifiedWord k =>
      p.2.val ⟨i.val - m, by omega⟩) h
    simpa only [split, restrict, intervalIndex, Nat.add_sub_of_le (by omega : m ≤ i.val)] using he

/-- Submultiplicativity is an injection on distinct preference profiles. -/
theorem count_submultiplicative (m k : ℕ) : count (m + k) ≤ count m * count k := by
  have h := Fintype.card_le_of_injective (split m k) (split_injective m k)
  simpa only [count, Fintype.card_prod] using h


private def pairedOffset {m : ℕ} (i : Fin m) : ℤ :=
  if i.val % 2 = 0 then 1 else -1

private theorem paired_reciprocal {m : ℕ} (i j : Fin m)
    (h : (i.val : ℤ) + pairedOffset i = j.val) : pairedOffset j = -pairedOffset i := by
  by_cases hi : i.val % 2 = 0 <;> by_cases hj : j.val % 2 = 0 <;>
    simp only [pairedOffset, hi, hj, ite_true, ite_false] at h ⊢ <;> omega

private theorem paired_injective {m : ℕ} (i j : Fin m)
    (h : (i.val : ℤ) + pairedOffset i = (j.val : ℤ) + pairedOffset j) : i = j := by
  apply Fin.ext
  by_cases hi : i.val % 2 = 0 <;> by_cases hj : j.val % 2 = 0 <;>
    simp only [pairedOffset, hi, hj, ite_true, ite_false] at h ⊢ <;> omega

theorem rank_injective (r : Ranking) {a b : ℤ}
    (ha : -2 ≤ a ∧ a ≤ 2) (hb : -2 ≤ b ∧ b ≤ 2)
    (ha0 : a ≠ 0) (hb0 : b ≠ 0) (h : offsetRank r a = offsetRank r b) : a = b := by
  rcases ha with ⟨haL, haU⟩
  rcases hb with ⟨hbL, hbU⟩
  interval_cases a <;> interval_cases b <;> simp_all [offsetRank] <;>
    have he := r.injective (Fin.ext h) <;> norm_num at he

private theorem paired_certificate {m : ℕ} (w : Word m)
    (htop : ∀ i, offsetRank (w i) (pairedOffset i) = 0) : Certificate w pairedOffset := by
  constructor
  · intro i
    unfold pairedOffset
    split <;> omega
  · intro i j _ h
    exact paired_reciprocal i j h
  · intro i j _ _ h
    exact paired_injective i j h
  · intro i j hij hdist
    by_cases he : pairedOffset i = (j.val : ℤ) - i.val
    · exact Or.inl he
    · right
      left
      rw [htop]
      apply Nat.pos_of_ne_zero
      intro hz
      apply he
      apply rank_injective (w i) (by unfold pairedOffset; split <;> omega)
        (by omega) (by unfold pairedOffset; split <;> omega) (by omega)
      exact (htop i).trans hz.symm

private def topRanking (s : Fin 4) (e : Equiv.Perm (Fin 3)) : Ranking :=
  (Equiv.Perm.decomposeFin.symm (s, e)).symm

private theorem topRanking_zero (s : Fin 4) (e : Equiv.Perm (Fin 3)) :
    topRanking s e s = 0 := by
  apply (Equiv.Perm.decomposeFin.symm (s, e)).injective
  simp [topRanking]

private theorem topRanking_injective (s : Fin 4) : Function.Injective (topRanking s) := by
  intro e f h
  have hh := congrArg (fun r : Ranking => Equiv.Perm.decomposeFin r.symm) h
  have hh' := congrArg Prod.snd hh
  simpa [topRanking] using hh'

private def topWord {m : ℕ} (e : Fin m → Equiv.Perm (Fin 3)) : CertifiedWord m := by
  let w : Word m := fun i => topRanking (if i.val % 2 = 0 then 0 else 2) (e i)
  refine ⟨w, pairedOffset, paired_certificate w ?_⟩
  intro i
  dsimp [w]
  by_cases hi : i.val % 2 = 0 <;>
    simp [pairedOffset, offsetRank, hi, topRanking_zero]

private theorem topWord_injective (m : ℕ) : Function.Injective (@topWord m) := by
  intro e f h
  funext i
  exact topRanking_injective _ (congrArg (fun w : CertifiedWord m => w.val i) h)

/-- Six independent orders remain after placing each prescribed partner first.
The possible final odd vertex requests the exterior target m, so both parities are covered. -/
theorem count_lower (m : ℕ) : 6 ^ m ≤ count m := by
  have h := Fintype.card_le_of_injective (@topWord m) (topWord_injective m)
  simpa [count, Fintype.card_pi_const, Fintype.card_perm, Nat.factorial] using h

/-- A directed three-cycle whose two triangle neighbors precede all exterior partners. -/
def ExclusiveTriangle (w : Word 3) : Prop :=
  offsetRank (w 0) 1 < offsetRank (w 0) 2 ∧
  offsetRank (w 1) 1 < offsetRank (w 1) (-1) ∧
  offsetRank (w 2) (-2) < offsetRank (w 2) (-1) ∧
  (∀ a : ℤ, -2 ≤ a → a ≤ 2 → a ≠ 1 → a ≠ 2 →
    offsetRank (w 0) 2 < offsetRank (w 0) a) ∧
  (∀ b : ℤ, -2 ≤ b → b ≤ 2 → b ≠ -1 → b ≠ 1 →
    offsetRank (w 1) (-1) < offsetRank (w 1) b) ∧
  (∀ c : ℤ, -2 ≤ c → c ≤ 2 → c ≠ -2 → c ≠ -1 →
    offsetRank (w 2) (-1) < offsetRank (w 2) c)

/-- Exterior requests and singles do not evade the exclusive-triangle obstruction. -/
theorem exclusive_triangle_not_certified {w : Word 3} (ht : ExclusiveTriangle w) :
    ¬ ∃ d, Certificate w d := by
  rintro ⟨d, hc⟩
  rcases ht with ⟨h0, h1, h2, he0, he1, he2⟩
  have hb0 := hc.bounded 0
  have hb1 := hc.bounded 1
  have hb2 := hc.bounded 2
  have h01 : d 0 = 1 ↔ d 1 = -1 := by
    constructor
    · intro h
      have hh := hc.reciprocal 0 1 (by omega) (by simp [h])
      omega
    · intro h
      have hh := hc.reciprocal 1 0 (by omega) (by simp [h])
      omega
  have h02 : d 0 = 2 ↔ d 2 = -2 := by
    constructor
    · intro h
      have hh := hc.reciprocal 0 2 (by omega) (by simp [h])
      omega
    · intro h
      have hh := hc.reciprocal 2 0 (by omega) (by simp [h])
      omega
  have h12 : d 1 = 1 ↔ d 2 = -1 := by
    constructor
    · intro h
      have hh := hc.reciprocal 1 2 (by omega) (by simp [h])
      omega
    · intro h
      have hh := hc.reciprocal 2 1 (by omega) (by simp [h])
      omega
  have hn01 := hc.nonblocking 0 1 (by decide) (by decide)
  have hn02 := hc.nonblocking 0 2 (by decide) (by decide)
  have hn12 := hc.nonblocking 1 2 (by decide) (by decide)
  norm_num at hn01 hn02 hn12
  by_cases ha1 : d 0 = 1
  · have hb : d 1 = -1 := h01.mp ha1
    have hc1 : d 2 ≠ -1 := by intro h; have := h12.mpr h; omega
    have hc2 : d 2 ≠ -2 := by intro h; have := h02.mpr h; omega
    have hce := he2 (d 2) hb2.1 hb2.2 hc2 hc1
    rw [hb] at hn12
    omega
  by_cases ha2 : d 0 = 2
  · have hc2 : d 2 = -2 := h02.mp ha2
    have hb1 : d 1 ≠ 1 := by intro h; have := h12.mp h; omega
    have hb2 : d 1 ≠ -1 := by intro h; exact ha1 (h01.mpr h)
    have hbe := he1 (d 1) (hc.bounded 1).1 (hc.bounded 1).2 hb2 hb1
    rw [ha2] at hn01
    omega
  have hae := he0 (d 0) hb0.1 hb0.2 ha1 ha2
  by_cases hb : d 1 = 1
  · have hc2 : d 2 = -1 := h12.mp hb
    rw [hc2] at hn02
    omega
  · have hb2 : d 1 ≠ -1 := by intro h; exact ha1 (h01.mpr h)
    have hbe := he1 (d 1) hb1.1 hb1.2 hb2 hb
    omega

#print axioms count_lower
#print axioms exclusive_triangle_not_certified
#print axioms certificate_restrict
#print axioms count_submultiplicative

private def negOffset : Ranking := Equiv.ofBijective ![2, 3, 0, 1] (by decide)

/-- Reflection reverses the interval and negates signed offsets. -/
def reflectWord (w : Word 3) : Word 3 := fun i => negOffset.trans (w i.rev)

private theorem reflect_rank (r : Ranking) (a : ℤ) :
    offsetRank (negOffset.trans r) a = offsetRank r (-a) := by
  by_cases h1 : a = 1
  · subst a; simp [offsetRank, negOffset]
  by_cases h2 : a = 2
  · subst a; simp [offsetRank, negOffset]
  by_cases h3 : a = -1
  · subst a; simp [offsetRank, negOffset]
  by_cases h4 : a = -2
  · subst a; simp [offsetRank, negOffset]
  simp [offsetRank, h1, h2, h3, h4, show -a ≠ 1 by omega,
    show -a ≠ 2 by omega, show -a ≠ -1 by omega, show -a ≠ -2 by omega]

private theorem reflect_certificate {w : Word 3} {d : Fin 3 → ℤ}
    (hc : Certificate w d) : Certificate (reflectWord w) (fun i => -d i.rev) := by
  have hv (i : Fin 3) : (i.rev.val : ℤ) = 2 - (i.val : ℤ) := by
    simp only [Fin.val_rev]
    omega
  constructor
  · intro i; have := hc.bounded i.rev; omega
  · intro i j hi he
    have hh := hc.reciprocal i.rev j.rev (by omega) (by rw [hv, hv]; omega)
    omega
  · intro i j hi hj he
    apply Fin.rev_injective
    apply hc.target_injective i.rev j.rev (by omega) (by omega)
    rw [hv, hv]
    omega
  · intro i j hij hdist
    have h := hc.nonblocking j.rev i.rev (by simp only [Fin.val_rev]; omega)
      (by simp only [Fin.val_rev]; omega)
    have he : (i.rev.val : ℤ) - j.rev.val = (j.val : ℤ) - i.val := by
      rw [hv, hv]; ring
    have hf : (j.rev.val : ℤ) - i.rev.val = (i.val : ℤ) - j.val := by
      rw [hv, hv]; ring
    rw [he, hf] at h
    change -d i.rev = (j.val : ℤ) - i.val ∨ _ ∨ _
    simp only [reflectWord, reflect_rank, neg_neg]
    rcases h with h | h | h
    · left
      have hh := hc.reciprocal j.rev i.rev (by omega) (by rw [hv, hv]; omega)
      omega
    · right; right; simpa only [neg_sub] using h
    · right; left; simpa only [neg_sub] using h

private def rankingValues (i : Fin 3) (flip : Bool) : Fin 4 → Fin 4 :=
  if i = 0 then (if flip then ![0, 1, 3, 2] else ![0, 1, 2, 3])
  else if i = 1 then (if flip then ![0, 3, 1, 2] else ![0, 2, 1, 3])
  else (if flip then ![3, 2, 1, 0] else ![2, 3, 1, 0])

private def forwardRanking (i : Fin 3) (flip : Bool) : Ranking :=
  Equiv.ofBijective (rankingValues i flip) (by fin_cases i <;> cases flip <;> decide)

private def forwardWord (b : Fin 3 → Bool) : Word 3 := fun i => forwardRanking i (b i)

/-- One orientation bit and three independent orders of the two exterior offsets. -/
def forbiddenWord (s : Bool × (Fin 3 → Bool)) : Word 3 :=
  if s.1 then reflectWord (forwardWord s.2) else forwardWord s.2

private theorem forward_exclusive (b : Fin 3 → Bool) : ExclusiveTriangle (forwardWord b) := by
  unfold ExclusiveTriangle
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · cases h : b 0 <;> decide +revert
  · cases h : b 1 <;> decide +revert
  · cases h : b 2 <;> decide +revert
  · intro a ha hb h1 h2
    interval_cases a <;> cases h : b 0 <;> simp_all [forwardWord, forwardRanking, rankingValues, offsetRank]
  · intro a ha hb h1 h2
    interval_cases a <;> cases h : b 1 <;> simp_all [forwardWord, forwardRanking, rankingValues, offsetRank]
  · intro a ha hb h1 h2
    interval_cases a <;> cases h : b 2 <;> simp_all [forwardWord, forwardRanking, rankingValues, offsetRank]

/-- Every listed word is impossible, with external requests and singles still allowed. -/
theorem forbidden_not_certified (s : Bool × (Fin 3 → Bool)) :
    ¬ ∃ d, Certificate (forbiddenWord s) d := by
  rcases s with ⟨o, b⟩
  cases o
  · exact exclusive_triangle_not_certified (forward_exclusive b)
  · rintro ⟨d, hd⟩
    have hh := reflect_certificate hd
    have he : reflectWord (forbiddenWord (true, b)) = forwardWord b := by
      funext i
      apply Equiv.ext
      intro k
      fin_cases k <;> simp [reflectWord, forbiddenWord, negOffset]
    rw [he] at hh
    exact exclusive_triangle_not_certified (forward_exclusive b) ⟨_, hh⟩

private theorem reflect_reflect (w : Word 3) : reflectWord (reflectWord w) = w := by
  funext i
  apply Equiv.ext
  intro k
  fin_cases k <;> simp [reflectWord, negOffset]

private theorem forward_ranking_injective (i : Fin 3) :
    Function.Injective (forwardRanking i) := by
  intro b c h
  fin_cases i
  · have hh := congrArg (fun r : Ranking => r 2) h
    cases b <;> cases c <;> simp [forwardRanking, rankingValues] at hh ⊢
  · have hh := congrArg (fun r : Ranking => r 1) h
    cases b <;> cases c <;> simp [forwardRanking, rankingValues] at hh ⊢
  · have hh := congrArg (fun r : Ranking => r 0) h
    cases b <;> cases c <;> simp [forwardRanking, rankingValues] at hh ⊢

private theorem forbidden_injective : Function.Injective forbiddenWord := by
  rintro ⟨o, b⟩ ⟨p, c⟩ h
  have ho : o = p := by
    have hm := congrArg (fun w : Word 3 => w 1 0) h
    cases o <;> cases p <;> cases hb : b 1 <;> cases hc : c 1 <;>
      simp_all [forbiddenWord, reflectWord, forwardWord, forwardRanking, rankingValues,
        negOffset]
  subst p
  have hf : forwardWord b = forwardWord c := by
    cases o
    · simpa [forbiddenWord] using h
    · have hh := congrArg reflectWord h
      simpa only [forbiddenWord, ite_true, reflect_reflect] using hh
  congr 1
  funext i
  exact forward_ranking_injective i (congrFun hf i)

/-- The removed objects are distinct ranking profiles, never matching witnesses. -/
def forbiddenProfiles : Finset (Word 3) := Finset.univ.image forbiddenWord

/-- There are exactly sixteen distinct removed ranking words. -/
theorem forbidden_card : forbiddenProfiles.card = 16 := by
  rw [forbiddenProfiles, Finset.card_image_of_injective _ forbidden_injective]
  norm_num [Fintype.card_prod, Fintype.card_pi_const]

/-- Exact finite-cardinal removal bound for the existentially certified word subtype. -/
theorem count_three_bound : count 3 ≤ 13808 := by
  let f : CertifiedWord 3 → {w : Word 3 // w ∉ forbiddenProfiles} := fun w =>
    ⟨w.val, by
      intro h
      obtain ⟨s, _, hs⟩ := Finset.mem_image.mp h
      apply forbidden_not_certified s
      rw [hs]
      exact w.property⟩
  have hi : Function.Injective f := by
    intro x y h
    have he := congrArg (fun z : {w : Word 3 // w ∉ forbiddenProfiles} => z.val) h
    exact Subtype.ext he
  have hc := Fintype.card_le_of_injective f hi
  have hn : Fintype.card {w : Word 3 // w ∉ forbiddenProfiles} =
      Fintype.card (Word 3) - forbiddenProfiles.card := by
    simpa using Fintype.card_subtype_compl (fun w : Word 3 => w ∈ forbiddenProfiles)
  rw [hn, forbidden_card] at hc
  simpa [count, Word, Ranking, Fintype.card_pi_const, Fintype.card_perm, Nat.factorial] using hc

#print axioms forbidden_not_certified
#print axioms forbidden_card
#print axioms count_three_bound

end D5.S3.Combinatorics.Graph.Roommates.OpenCertificates
