/- GID: D5/S3/Combinatorics/Graph/Roommates/TriangleCount
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/Roommates/TriangleCount
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [D5/S3/Combinatorics/Graph/Roommates/OpenCertificates.exclusive_triangle_not_certified]
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Combinatorics/Graph/Roommates/TriangleCount.count_three_bound; premises=D5/S3/Combinatorics/Graph/Roommates/OpenCertificates.exclusive_triangle_not_certified
   digest: Sixteen exclusive directed triangle ranking words are removed from the profile count. -/

import D5.S3.Combinatorics.Graph.Roommates.OpenCertificates
import Mathlib.Data.Fin.Rev
import Mathlib.Data.Fintype.Card

set_option autoImplicit false
noncomputable section
open scoped Classical
open D5.S3.Combinatorics.Graph.Roommates.OpenCertificates

namespace D5.S3.Combinatorics.Graph.Roommates.TriangleCount

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

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
private theorem forbidden_injective : Function.Injective forbiddenWord := by
  decide +kernel

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
    exact Subtype.ext (congrArg Subtype.val h)
  have hc := Fintype.card_le_of_injective f hi
  have hn : Fintype.card {w : Word 3 // w ∉ forbiddenProfiles} =
      Fintype.card (Word 3) - forbiddenProfiles.card := by
    simpa using Fintype.card_subtype_compl (fun w : Word 3 => w ∈ forbiddenProfiles)
  rw [hn, forbidden_card] at hc
  simpa [count, Word, Ranking, Fintype.card_pi_const, Fintype.card_perm, Nat.factorial] using hc

#print axioms forbidden_not_certified
#print axioms forbidden_card
#print axioms count_three_bound

end D5.S3.Combinatorics.Graph.Roommates.TriangleCount
