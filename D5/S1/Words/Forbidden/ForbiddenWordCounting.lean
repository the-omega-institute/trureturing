/- GID: D5/S1/Words/Forbidden/ForbiddenWordCounting
   generality: G
   mirror-B: D5/B/S1/Words/Forbidden/ForbiddenWordCounting
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   utility: none
   digest: First-hit decompositions give the forbidden binary-word counting identity. -/
/-
proof_shape: mem_words: bind-only; consumer: mem_omega
proof_shape: mem_omega: bind-only; consumer: avoidCoeff_zero
proof_shape: self_border: bind-only; consumer: balanced_tail
proof_shape: firstHit_append_one_iff: bind-only; consumer: extensions_partition
proof_shape: firstHit_suffix: bind-only; consumer: firstHit_overlap
proof_shape: firstHit_prefix_unique: bind-only; consumer: overlapPair_injective
proof_shape: exists_firstHit_prefix: content
proof_shape: mem_firstHits: bind-only; consumer: hitCoeff_zero
proof_shape: weight_append: bind-only; consumer: overlap_weighted_count
proof_shape: avoidCoeff_zero: bind-only; consumer: firstHit_letters_equation
proof_shape: hitCoeff_zero: bind-only; consumer: firstHit_letters_equation
proof_shape: snoc_injective: bind-only; consumer: avoidCoeff_succ_add_hitCoeff
proof_shape: exists_snoc_of_length_succ: bind-only; consumer: extensions_partition
proof_shape: mem_extensions: bind-only; consumer: extensions_partition
proof_shape: extensions_partition: bind-only; consumer: avoidCoeff_succ_add_hitCoeff
proof_shape: avoid_hit_disjoint: bind-only; consumer: avoidCoeff_succ_add_hitCoeff
proof_shape: avoidCoeff_succ_add_hitCoeff: content
proof_shape: firstHit_letters_equation: content
proof_shape: firstHits_short: bind-only; consumer: hitCoeff_short
proof_shape: hitCoeff_short: bind-only; consumer: firstHit_overlap_equation
proof_shape: coeff_mul_monomial: bind-only; consumer: firstHit_overlap_equation
proof_shape: countingIdentity_of_firstHit_equations: bind-only; consumer: forbidden_word_counting_identity
proof_shape: mem_overlapPairs: bind-only; consumer: overlapPair_splice
proof_shape: mem_borderLengths: bind-only; consumer: firstHit_overlap
proof_shape: firstHit_overlap: content
proof_shape: firstHit_splice: content
proof_shape: overlapPair_splice: bind-only; consumer: overlapPair_injective
proof_shape: overlapPair_injective: content
proof_shape: overlapPair_surjective: content
proof_shape: overlap_weighted_count: content
proof_shape: firstHit_overlap_equation: content
proof_shape: forbidden_word_counting_identity: content
proof_shape: full_mem_borderLengths: bind-only; consumer: corrEval_ge_full
proof_shape: borderLengths_iff_border: bind-only; consumer: balanced_iff_imbalance_zero
proof_shape: omega_nonempty: content
escape_witness: forbidden_word_counting_identity on result's live proof path.
admission_basis: escape-witness
Direct frozen dependencies: none on the protected baseline.
Information-escape registration is paused under CLAUDE.md §3.9.
-/

import Mathlib.Data.Real.Basic
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.Derivative

open Filter Finset
open scoped Topology

namespace D5.S1.Words.Forbidden.ForbiddenWordCounting

def words (m : ℕ) : Finset (List Bool) :=
  (Finset.univ : Finset (Fin m → Bool)).image List.ofFn

theorem mem_words {m : ℕ} {u : List Bool} : u ∈ words m ↔ u.length = m := by
  constructor
  · rintro hu
    obtain ⟨f, _, rfl⟩ := Finset.mem_image.mp hu
    exact List.length_ofFn
  · intro hu
    subst m
    exact Finset.mem_image.mpr ⟨u.get, Finset.mem_univ _, List.ofFn_get u⟩

def omega (w : List Bool) (m : ℕ) : Finset (List Bool) :=
  (words m).filter fun u => ¬ w <:+: u

theorem mem_omega {w u : List Bool} {m : ℕ} :
    u ∈ omega w m ↔ u.length = m ∧ ¬ w <:+: u := by
  simp [omega, mem_words]

noncomputable def rho (w : List Bool) (m : ℕ) : ℝ :=
  (∑ u ∈ omega w m, (u.count true : ℝ)) / ((m : ℝ) * (omega w m).card)

def IsBorder (w b : List Bool) : Prop :=
  b ≠ [] ∧ b <+: w ∧ b <:+ w

def BalancedBorders (w : List Bool) : Prop :=
  ∀ b, IsBorder w b → 2 * b.count true = b.length

theorem self_border {w : List Bool} (hw : w ≠ []) : IsBorder w w :=
  ⟨hw, List.prefix_rfl, List.suffix_rfl⟩


private def FirstHit (w u : List Bool) : Prop :=
  w <:+: u ∧ ∀ v, v <+: u → v.length < u.length → ¬ w <:+: v

private theorem firstHit_append_one_iff {w u : List Bool} {b : Bool} :
    FirstHit w (u ++ [b]) ↔ ¬ w <:+: u ∧ w <:+: u ++ [b] := by
  constructor
  · rintro ⟨hit, hf⟩
    exact ⟨hf u (List.prefix_append _ _) (by simp), hit⟩
  · rintro ⟨hu, hit⟩
    refine ⟨hit, ?_⟩
    intro v hv hlen hvhit
    have hvl : v.length ≤ u.length := by
      simp only [List.length_append, List.length_singleton] at hlen
      omega
    have hvpre : v <+: u := by
      rw [List.prefix_iff_eq_take] at hv
      rw [List.take_append_of_le_length hvl] at hv
      rw [hv]
      exact List.take_prefix _ _
    exact hu (hvhit.trans hvpre.isInfix)

private theorem firstHit_suffix {w u : List Bool} (hw : w ≠ []) (h : FirstHit w u) : w <:+ u := by
  obtain ⟨s, t, heq⟩ := h.1
  by_cases ht : t = []
  · subst t
    exact ⟨s, by simpa using heq⟩
  · have hp : s ++ w <+: u := ⟨t, heq⟩
    have hlt : (s ++ w).length < u.length := by
      have hlen := congrArg List.length heq
      have := List.length_pos_iff.mpr ht
      simp only [List.length_append] at hlen ⊢
      omega
    exact False.elim (h.2 (s ++ w) hp hlt (List.infix_append_right))

private theorem firstHit_prefix_unique {w u f g : List Bool}
    (hf : FirstHit w f) (hg : FirstHit w g) (hfu : f <+: u) (hgu : g <+: u) : f = g := by
  rcases le_total f.length g.length with hle | hle
  · have hfg : f <+: g := by
      exact List.prefix_of_prefix_length_le hfu hgu hle
    rcases lt_or_eq_of_le hle with hlt | heq
    · exact False.elim (hg.2 f hfg hlt hf.1)
    · exact hfg.eq_of_length heq
  · have hgf : g <+: f := by
      exact List.prefix_of_prefix_length_le hgu hfu hle
    rcases lt_or_eq_of_le hle with hlt | heq
    · exact False.elim (hf.2 g hgf hlt hg.1)
    · exact (hgf.eq_of_length heq).symm

private theorem exists_firstHit_prefix {w u : List Bool} (hit : w <:+: u) :
    ∃ f, f <+: u ∧ FirstHit w f := by
  have hex : ∃ t : ℕ, w <:+: u.take t := ⟨u.length, by simpa using hit⟩
  let t := Nat.find hex
  have ht : t ≤ u.length := Nat.find_min' hex (by simpa using hit)
  refine ⟨u.take t, List.take_prefix _ _, Nat.find_spec hex, ?_⟩
  intro v hv hvl hvhit
  have hvu : v <+: u := hv.trans (List.take_prefix _ _)
  have hvt : v.length < t := by simpa [List.length_take_of_le ht] using hvl
  have hvhit' : w <:+: u.take v.length := by
    simpa [← List.prefix_iff_eq_take.mp hvu] using hvhit
  exact Nat.find_min hex hvt hvhit'

private noncomputable def firstHits (w : List Bool) (m : ℕ) : Finset (List Bool) := by
  classical
  exact (words m).filter (FirstHit w)

noncomputable def avoidCoeff (w : List Bool) (m : ℕ) : Polynomial ℚ :=
  ∑ u ∈ omega w m, Polynomial.X ^ u.count true

private noncomputable def hitCoeff (w : List Bool) (m : ℕ) : Polynomial ℚ :=
  ∑ u ∈ firstHits w m, Polynomial.X ^ u.count true

noncomputable def avoidSeries (w : List Bool) : PowerSeries (Polynomial ℚ) :=
  PowerSeries.mk (avoidCoeff w)

private noncomputable def hitSeries (w : List Bool) : PowerSeries (Polynomial ℚ) :=
  PowerSeries.mk (hitCoeff w)

noncomputable def wordMonomial (w : List Bool) : PowerSeries (Polynomial ℚ) :=
  PowerSeries.monomial w.length (Polynomial.X ^ w.count true)

noncomputable def letterSeries : PowerSeries (Polynomial ℚ) :=
  PowerSeries.X * PowerSeries.C (1 + Polynomial.X)


private theorem mem_firstHits {w u : List Bool} {m : ℕ} :
    u ∈ firstHits w m ↔ u.length = m ∧ FirstHit w u := by
  classical
  simp [firstHits, mem_words]

private theorem weight_append (u v : List Bool) :
    (Polynomial.X ^ (u ++ v).count true : Polynomial ℚ) =
      Polynomial.X ^ u.count true * Polynomial.X ^ v.count true := by
  rw [List.count_append, pow_add]

theorem avoidCoeff_zero {w : List Bool} (hw : w ≠ []) : avoidCoeff w 0 = 1 := by
  have hz : omega w 0 = {[]} := by
    ext u
    rw [mem_omega, mem_singleton]
    constructor
    · intro h
      exact List.length_eq_zero_iff.mp h.1
    · intro hu
      subst u
      exact ⟨rfl, by simpa using hw⟩
  simp [avoidCoeff, hz]

private theorem hitCoeff_zero {w : List Bool} (hw : w ≠ []) : hitCoeff w 0 = 0 := by
  have hz : firstHits w 0 = ∅ := by
    ext u
    rw [mem_firstHits]
    simp only [Finset.notMem_empty, iff_false, not_and]
    intro hl hh
    have hu : u = [] := List.length_eq_zero_iff.mp hl
    subst u
    exact hw (by simpa using hh.1)
  simp [hitCoeff, hz]

private theorem snoc_injective : Function.Injective (fun p : List Bool × Bool => p.1 ++ [p.2]) := by
  rintro ⟨u, b⟩ ⟨v, c⟩ h
  have hh := congrArg List.reverse h
  simp only [List.reverse_append, List.reverse_singleton, List.singleton_append,
    List.cons.injEq, List.reverse_inj] at hh
  exact Prod.ext hh.2 hh.1

private theorem exists_snoc_of_length_succ {u : List Bool} {m : ℕ} (h : u.length = m + 1) :
    ∃ v b, v.length = m ∧ u = v ++ [b] := by
  cases u using List.reverseRecOn with
  | nil => simp at h
  | append_singleton v b _ => exact ⟨v, b, by simpa using h, rfl⟩

private noncomputable def extensions (w : List Bool) (m : ℕ) : Finset (List Bool) :=
  ((omega w m) ×ˢ (univ : Finset Bool)).image fun p => p.1 ++ [p.2]

private theorem mem_extensions {w u : List Bool} {m : ℕ} :
    u ∈ extensions w m ↔ ∃ v b, v ∈ omega w m ∧ u = v ++ [b] := by
  classical
  simp only [extensions, mem_image, mem_product, mem_univ, and_true]
  constructor
  · rintro ⟨⟨v,b⟩, hv, rfl⟩
    exact ⟨v,b,hv,rfl⟩
  · rintro ⟨v,b,hv,rfl⟩
    exact ⟨(v,b),hv,rfl⟩

private theorem extensions_partition (w : List Bool) (m : ℕ) :
    extensions w m = omega w (m + 1) ∪ firstHits w (m + 1) := by
  classical
  ext u
  rw [mem_extensions, mem_union, mem_omega, mem_firstHits]
  constructor
  · rintro ⟨v,b,hv,rfl⟩
    obtain ⟨hvlen,hva⟩ := mem_omega.mp hv
    have hlen : (v ++ [b]).length = m+1 := by simp [hvlen]
    by_cases hh : w <:+: v ++ [b]
    · exact Or.inr ⟨hlen, firstHit_append_one_iff.mpr ⟨hva,hh⟩⟩
    · exact Or.inl ⟨hlen,hh⟩
  · intro hu
    have hlen := hu.elim And.left And.left
    obtain ⟨v,b,hvlen,rfl⟩ := exists_snoc_of_length_succ hlen
    refine ⟨v,b,mem_omega.mpr ⟨hvlen,?_⟩,rfl⟩
    rcases hu with ⟨_,ha⟩ | ⟨_,hf⟩
    · intro hit
      exact ha (hit.trans (List.prefix_append _ _).isInfix)
    · exact (firstHit_append_one_iff.mp hf).1

private theorem avoid_hit_disjoint (w : List Bool) (m : ℕ) :
    Disjoint (omega w m) (firstHits w m) := by
  classical
  rw [disjoint_left]
  intro u hu hf
  exact (mem_omega.mp hu).2 (mem_firstHits.mp hf).2.1

private theorem avoidCoeff_succ_add_hitCoeff (w : List Bool) (m : ℕ) :
    avoidCoeff w (m + 1) + hitCoeff w (m + 1) = avoidCoeff w m * (1 + Polynomial.X) := by
  classical
  calc
    _ = ∑ u ∈ extensions w m, (Polynomial.X ^ u.count true : Polynomial ℚ) := by
      rw [extensions_partition, sum_union (avoid_hit_disjoint w (m+1))]
      rfl
    _ = ∑ p ∈ ((omega w m) ×ˢ (univ : Finset Bool)),
        (Polynomial.X ^ (p.1 ++ [p.2]).count true : Polynomial ℚ) := by
      exact sum_image (fun a _ b _ h => snoc_injective h)
    _ = ∑ u ∈ omega w m, ∑ b : Bool,
        (Polynomial.X ^ (u ++ [b]).count true : Polynomial ℚ) := by rw [sum_product]
    _ = ∑ u ∈ omega w m, Polynomial.X ^ u.count true * (1 + Polynomial.X) := by
      apply sum_congr rfl
      intro u _
      simp [weight_append, Fintype.sum_bool]
      ring
    _ = _ := by rw [← sum_mul]; rfl

private theorem firstHit_letters_equation {w : List Bool} (hw : w ≠ []) :
    avoidSeries w * (1 - letterSeries) + hitSeries w = 1 := by
  apply PowerSeries.ext
  intro n
  rw [mul_sub, mul_one, map_add, map_sub]
  cases n with
  | zero =>
    simp [avoidSeries, hitSeries, PowerSeries.coeff_mk, avoidCoeff_zero hw,
      hitCoeff_zero hw, letterSeries, mul_assoc]
  | succ m =>
    have hc : PowerSeries.coeff (m+1) (avoidSeries w * letterSeries) =
        avoidCoeff w m * (1 + Polynomial.X) := by
      unfold letterSeries
      rw [← mul_assoc, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X]
      simp [avoidSeries]
    rw [hc]
    simp only [avoidSeries, hitSeries, PowerSeries.coeff_mk, PowerSeries.coeff_one,
      Nat.succ_ne_zero, ite_false]
    have hs := avoidCoeff_succ_add_hitCoeff w m
    linear_combination hs

private theorem firstHits_short {w : List Bool} {k : ℕ} (hk : k < w.length) :
    firstHits w k = ∅ := by
  classical
  ext u
  rw [mem_firstHits]
  simp only [Finset.notMem_empty, iff_false]
  rintro ⟨hl,hf⟩
  have hle := hf.1.length_le
  omega

private theorem hitCoeff_short {w : List Bool} {k : ℕ} (hk : k < w.length) :
    hitCoeff w k = 0 := by
  simp [hitCoeff,firstHits_short hk]

private theorem coeff_mul_monomial (f : PowerSeries (Polynomial ℚ)) (k n : ℕ) (a : Polynomial ℚ) :
    PowerSeries.coeff k (f * PowerSeries.monomial n a) =
      if n ≤ k then PowerSeries.coeff (k-n) f * a else 0 := by
  simpa [PowerSeries.coeff, PowerSeries.monomial] using
    MvPowerSeries.coeff_mul_monomial (Finsupp.single () k) (Finsupp.single () n) f a

def borderLengths (w : List Bool) : Finset ℕ :=
  (range (w.length + 1)).filter fun j => 0 < j ∧ w.take j <:+ w

noncomputable def overlapSeries (w : List Bool) : PowerSeries (Polynomial ℚ) :=
  ∑ j ∈ borderLengths w, PowerSeries.monomial (w.length - j)
    (Polynomial.X ^ ((w.drop j).count true))

def countingIdentity (w : List Bool) : Prop :=
  avoidSeries w * ((1 - letterSeries) * overlapSeries w + wordMonomial w) =
    overlapSeries w

private theorem countingIdentity_of_firstHit_equations {w : List Bool}
    (hletters : avoidSeries w * (1 - letterSeries) + hitSeries w = 1)
    (hoverlap : avoidSeries w * wordMonomial w = hitSeries w * overlapSeries w) :
    countingIdentity w := by
  unfold countingIdentity
  calc
    avoidSeries w * ((1 - letterSeries) * overlapSeries w + wordMonomial w) =
        (avoidSeries w * (1 - letterSeries) + hitSeries w) * overlapSeries w := by
      rw [mul_add, ← mul_assoc, hoverlap, add_mul]
    _ = overlapSeries w := by rw [hletters, one_mul]

private noncomputable def overlapPairs (w : List Bool) (m : ℕ) : Finset (Σ _j : ℕ, List Bool) :=
  (borderLengths w).sigma fun j => firstHits w (m + j)

private theorem mem_overlapPairs {w f : List Bool} {m j : ℕ} :
    (⟨j,f⟩ : Σ _j : ℕ, List Bool) ∈ overlapPairs w m ↔
      j ∈ borderLengths w ∧ f.length = m+j ∧ FirstHit w f := by
  simp [overlapPairs, mem_firstHits]

def imbalance (w : List Bool) (j : ℕ) : ℤ :=
  2 * (w.take j).count true - (w.take j).length

theorem mem_borderLengths {w : List Bool} {j : ℕ} :
    j ∈ borderLengths w ↔ 0 < j ∧ j ≤ w.length ∧ w.take j <:+ w := by
  simp only [borderLengths, mem_filter, mem_range]
  constructor
  · rintro ⟨hlen, hj, hs⟩
    exact ⟨hj, by omega, hs⟩
  · rintro ⟨hj, hlen, hs⟩
    exact ⟨by omega, hj, hs⟩

private theorem firstHit_overlap {w u f : List Bool} (hu : ¬ w <:+: u)
    (hf : FirstHit w f) (hp : f <+: u ++ w) :
    ∃ j ∈ borderLengths w, f = u ++ w.take j ∧ f ++ w.drop j = u ++ w := by
  have huf : u.length < f.length := by
    by_contra! hle
    have hfu : f <+: u := List.prefix_of_prefix_length_le hp (List.prefix_append _ _) hle
    exact hu (hf.1.trans hfu.isInfix)
  let j := f.length - u.length
  have hj : 0 < j := by dsimp [j]; omega
  have hjn : j ≤ w.length := by
    have hl := hp.length_le
    simp only [List.length_append] at hl
    dsimp [j]
    omega
  have he : f = u ++ w.take j := by
    rw [List.prefix_iff_eq_take.mp hp, List.take_append]
    rw [List.take_of_length_le huf.le]
  have hw : w ≠ [] := by
    intro hn
    subst w
    simp at hjn
    omega
  have hws : w <:+ f := firstHit_suffix hw hf
  have hbs : w.take j <:+ f := by
    rw [he]
    exact List.suffix_append _ _
  have hb : w.take j <:+ w :=
    List.suffix_of_suffix_length_le hbs hws (by simp)
  refine ⟨j, mem_borderLengths.mpr ⟨hj, hjn, hb⟩, he, ?_⟩
  rw [he, List.append_assoc, List.take_append_drop]

private theorem firstHit_splice {w f : List Bool} {j : ℕ}
    (hj : j ∈ borderLengths w) (hf : FirstHit w f) :
    f ++ w.drop j = f.take (f.length - j) ++ w ∧
      ¬ w <:+: f.take (f.length - j) := by
  obtain ⟨hj0, hjn, hborder⟩ := mem_borderLengths.mp hj
  have hw : w ≠ [] := by intro hn; simp [hn] at hjn; omega
  have hfw : w <:+ f := firstHit_suffix hw hf
  obtain ⟨s, hsp⟩ := hfw
  have hlength : f.length = s.length + w.length := by rw [← hsp]; simp
  have hfl : w.length ≤ f.length := by omega
  have hl : f.length - j = s.length + (w.length - j) := by omega
  have hb : w.take j = w.drop (w.length - j) := by
    have hb := List.suffix_iff_eq_drop.mp hborder
    simpa [List.length_take_of_le hjn] using hb
  have hew : w.take (w.length - j) ++ w.take j = w := by
    rw [hb, List.take_append_drop]
  have htake : f.take (f.length - j) = s ++ w.take (w.length - j) := by
    rw [hl, ← hsp, List.take_length_add_append]
  constructor
  · rw [htake, ← hsp]
    calc
      (s ++ w) ++ w.drop j = (s ++ (w.take (w.length - j) ++ w.take j)) ++ w.drop j := by
        rw [hew]
      _ = (s ++ w.take (w.length - j)) ++ w := by
        simp only [List.append_assoc, List.take_append_drop]
  · apply hf.2 _ (List.take_prefix _ _)
    rw [List.length_take]
    omega

private theorem overlapPair_splice {w : List Bool} {m : ℕ} {p : Σ _j : ℕ, List Bool}
    (hp : p ∈ overlapPairs w m) :
    p.2.take m ∈ omega w m ∧ p.2 ++ w.drop p.1 = p.2.take m ++ w := by
  obtain ⟨hj,hlen,hf⟩ := mem_overlapPairs.mp hp
  have hsub : p.2.length - p.1 = m := by omega
  have hs := firstHit_splice hj hf
  rw [hsub] at hs
  refine ⟨mem_omega.mpr ⟨?_,hs.2⟩,hs.1⟩
  exact List.length_take_of_le (by omega)

private theorem overlapPair_injective {w : List Bool} {m : ℕ}
    {p q : Σ _j : ℕ, List Bool} (hp : p ∈ overlapPairs w m)
    (hq : q ∈ overlapPairs w m) (he : p.2.take m = q.2.take m) : p=q := by
  obtain ⟨hj,hlen,hf⟩ := mem_overlapPairs.mp hp
  obtain ⟨hk,glen,hg⟩ := mem_overlapPairs.mp hq
  have hs := (overlapPair_splice hp).2
  have ht := (overlapPair_splice hq).2
  rw [← he] at ht
  have hpf : p.2 <+: p.2.take m ++ w := by rw [← hs]; exact List.prefix_append _ _
  have hqf : q.2 <+: p.2.take m ++ w := by rw [← ht]; exact List.prefix_append _ _
  have hfg := firstHit_prefix_unique hf hg hpf hqf
  have hjk : p.1=q.1 := by have hl := congrArg List.length hfg; omega
  cases p with
  | mk j f =>
    cases q with
    | mk k g =>
      dsimp only at hjk hfg
      subst k
      subst g
      rfl

private theorem overlapPair_surjective {w u : List Bool} {m : ℕ} (hu : u ∈ omega w m) :
    ∃ p ∈ overlapPairs w m, p.2.take m = u := by
  obtain ⟨hlen,ha⟩ := mem_omega.mp hu
  have hit : w <:+: u++w := List.infix_append_right
  obtain ⟨f,hpre,hf⟩ := exists_firstHit_prefix hit
  obtain ⟨j,hj,hfexpr,_⟩ := firstHit_overlap ha hf hpre
  have hjn := (mem_borderLengths.mp hj).2.1
  have hflen : f.length=m+j := by rw [hfexpr]; simp [hlen,List.length_take_of_le hjn]
  refine ⟨⟨j,f⟩,mem_overlapPairs.mpr ⟨hj,hflen,hf⟩,?_⟩
  rw [hfexpr, ← hlen, List.take_left]

private theorem overlap_weighted_count (w : List Bool) (m : ℕ) :
    (∑ j ∈ borderLengths w, hitCoeff w (m+j) * Polynomial.X ^ ((w.drop j).count true)) =
      avoidCoeff w m * Polynomial.X ^ w.count true := by
  classical
  have hsum : (∑ p ∈ overlapPairs w m,
      (Polynomial.X ^ p.2.count true * Polynomial.X ^ ((w.drop p.1).count true) : Polynomial ℚ)) =
      ∑ u ∈ omega w m, Polynomial.X ^ u.count true * Polynomial.X ^ w.count true := by
    apply sum_bij (fun p _ => p.2.take m)
    · intro p hp
      exact (overlapPair_splice hp).1
    · intro p hp q hq he
      exact overlapPair_injective hp hq he
    · intro u hu
      obtain ⟨p,hp,he⟩ := overlapPair_surjective hu
      exact ⟨p,hp,he⟩
    · intro p hp
      rw [← weight_append, ← weight_append, (overlapPair_splice hp).2]
  rw [overlapPairs, sum_sigma] at hsum
  simp only [hitCoeff, avoidCoeff, sum_mul] at hsum ⊢
  exact hsum

private theorem firstHit_overlap_equation (w : List Bool) :
    avoidSeries w * wordMonomial w = hitSeries w * overlapSeries w := by
  classical
  apply PowerSeries.ext
  intro k
  unfold wordMonomial overlapSeries
  rw [coeff_mul_monomial,mul_sum,map_sum]
  by_cases hk : w.length ≤ k
  · let m := k-w.length
    have hkm : k=m+w.length := by dsimp [m]; omega
    rw [hkm]
    simp only [show w.length ≤ m+w.length by omega,ite_true,
      Nat.add_sub_cancel_right,avoidSeries,PowerSeries.coeff_mk]
    calc
      _ = ∑ j ∈ borderLengths w, hitCoeff w (m+j) * Polynomial.X^((w.drop j).count true) :=
        (overlap_weighted_count w m).symm
      _ = _ := by
        apply sum_congr rfl
        intro j hj
        have hjn := (mem_borderLengths.mp hj).2.1
        rw [coeff_mul_monomial,if_pos (by omega)]
        have he : m+w.length-(w.length-j)=m+j := by omega
        rw [he]
        simp [hitSeries,PowerSeries.coeff_mk]
  · rw [if_neg hk]
    symm
    apply sum_eq_zero
    intro j hj
    rw [coeff_mul_monomial]
    split_ifs with hjk
    · have hlt : k-(w.length-j)<w.length := by omega
      simp [hitSeries,PowerSeries.coeff_mk,hitCoeff_short hlt]
    · rfl

theorem forbidden_word_counting_identity {w : List Bool} (hw : w ≠ []) :
    countingIdentity w :=
  countingIdentity_of_firstHit_equations (firstHit_letters_equation hw) (firstHit_overlap_equation w)

theorem full_mem_borderLengths {w : List Bool} (hw : w ≠ []) :
    w.length ∈ borderLengths w := by
  rw [mem_borderLengths]
  exact ⟨List.length_pos_iff.mpr hw, le_rfl, by simp⟩

theorem borderLengths_iff_border {w b : List Bool} :
    IsBorder w b ↔ ∃ j ∈ borderLengths w, b = w.take j := by
  constructor
  · rintro ⟨hb, hp, hs⟩
    refine ⟨b.length, mem_borderLengths.mpr ⟨List.length_pos_iff.mpr hb, hp.length_le, ?_⟩,
      List.prefix_iff_eq_take.mp hp⟩
    simpa [← List.prefix_iff_eq_take.mp hp] using hs
  · rintro ⟨j, hj, rfl⟩
    obtain ⟨hj0, hjn, hs⟩ := mem_borderLengths.mp hj
    refine ⟨?_, List.take_prefix _ _, hs⟩
    have : (w.take j).length = j := List.length_take_of_le hjn
    intro hn
    simp [hn] at this
    omega

theorem omega_nonempty {w : List Bool} (hw : w ≠ []) (m : ℕ) :
    (omega w m).Nonempty := by
  obtain ⟨b, hb⟩ : ∃ b, b ∈ w := List.exists_mem_of_ne_nil w hw
  refine ⟨List.replicate m (!b), mem_omega.mpr ⟨by simp, ?_⟩⟩
  intro h
  have ht := List.eq_of_mem_replicate (h.sublist.subset hb)
  cases b <;> simp at ht

end D5.S1.Words.Forbidden.ForbiddenWordCounting
