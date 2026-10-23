/- GID: D5/S1/Words/MBonacciMinimumParikhDescent
   generality: G
   mirror-B: D5/B/S1/Words/MBonacciMinimumParikhDescent
   mirror-E: none(waiver:pure-word-combinatorics)
   anchors: []
   utility: none
   digest: Minimum complete Parikh cardinality forces an actual sentinel length. -/
import D5.S1.Words.MBonacciReversedPrefixFRS
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Words.MBonacciMinimumParikhDescent

open D5.S1.Words.MBonacciSentinelDesubstitution
open D5.S1.Words.MBonacciReversedPrefixFRS
open D5.S1.Words.RankOneMorphismIterationBound (subst)
open D5.S1.Words.AbelianBorders.AbelianBorderQuestionDefs (factor letterCount)

variable {m : ℕ} (hm : 2 ≤ m)

/-- The complete Parikh image, including every natural occurrence start. -/
def parikhImage (n : ℕ) : Set (Fin m → ℕ) :=
  Set.range (fun q : ℕ => fun a : Fin m => letterCount (factor (word hm) q n) a)

private def psi (s : List (Fin m)) (a : Fin m) : ℤ := letterCount s a
private def delta (a i : Fin m) : ℤ := if i = a then 1 else 0
private def terminal : Fin m := ⟨m - 1, by omega⟩

private def Defect (r : List (Fin m)) : Prop :=
  ∃ (v : List (Fin m)) (q : ℕ) (a b c : Fin m),
    Occ hm v q ∧ v.length = r.length + 1 ∧ a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
    ∀ i, psi v i - psi r i = delta a i + delta b i - delta c i

private lemma parikhImage_finite (n : ℕ) : (parikhImage hm n).Finite := by
  let f : (Fin m → Fin (n + 1)) → (Fin m → ℕ) := fun v i => (v i).val
  apply (Set.finite_range f).subset
  rintro v ⟨q, rfl⟩
  refine ⟨fun i => ⟨letterCount (factor (word hm) q n) i, ?_⟩, rfl⟩
  have h : (factor (word hm) q n).count i ≤ (factor (word hm) q n).length :=
    List.count_le_length
  simpa [letterCount, factor] using Nat.lt_succ_of_le h

private lemma rot_equiv (a : Fin m) : rot hm a = finRotate m a := by
  cases m with
  | zero => omega
  | succ p =>
    by_cases h : a.val < p
    · have h' : a.val + 1 < p + 1 := by omega
      simpa [rot, h'] using (finRotate_of_lt h).symm
    · have ha : a = Fin.last p := Fin.ext (by have := a.isLt; simp; omega)
      subst a
      simp [rot, zero]

private lemma rot_terminal : rot hm (terminal hm) = zero hm := by
  simp [rot, terminal, zero, show ¬ m - 1 + 1 < m by omega]

private lemma delta_rot (a i : Fin m) :
    delta (rot hm a) (rot hm i) = delta a i := by
  simp [delta, rot_equiv]

private lemma psi_append (s t : List (Fin m)) (i : Fin m) :
    psi (s ++ t) i = psi s i + psi t i := by
  simp [psi, letterCount, List.count_append]

private lemma psi_cons (a : Fin m) (s : List (Fin m)) (i : Fin m) :
    psi (a :: s) i = delta a i + psi s i := by
  by_cases h : i = a
  · simp [psi, letterCount, delta, h, add_comm]
  · simp [psi, letterCount, delta, h, Ne.symm h]

private lemma image_counts (s : List (Fin m)) (i : Fin m) :
    psi (subst (phi hm) s) (rot hm i) =
      if i = terminal hm then (s.length : ℤ) else psi s i := by
  induction s with
  | nil => simp [subst, psi, letterCount]
  | cons a s ih =>
    rw [D5.S1.Words.RankOneMorphismIterationBound.subst_cons, psi_append, ih]
    have hi : rot hm i = zero hm ↔ i = terminal hm := by
      rw [← rot_terminal hm, rot_equiv, rot_equiv]
      exact (finRotate m).injective.eq_iff
    have hai : rot hm i = rot hm a ↔ i = a := by
      rw [rot_equiv, rot_equiv]
      exact (finRotate m).injective.eq_iff
    by_cases h : i = terminal hm
    · have hp : psi (phi hm a) (zero hm) = 1 := by
        unfold phi
        split <;> simp [psi, letterCount, zero, Fin.ext_iff]
      rw [if_pos h, if_pos h, hi.mpr h, hp]
      simp [add_comm]
    · have h0 : rot hm i ≠ zero hm := fun hh => h (hi.mp hh)
      have hp : psi (phi hm a) (rot hm i) = delta a i := by
        by_cases hn : a.val + 1 < m
        · have he : (⟨a.val + 1, hn⟩ : Fin m) = rot hm a := by simp [rot, hn]
          have har : rot hm a = rot hm i ↔ i = a := by rw [eq_comm, hai]
          simp [phi, hn, psi, letterCount, List.count_cons, delta, he,
            Ne.symm h0, har]
        · have ha : a = terminal hm := Fin.ext (by have := a.isLt; simp [terminal]; omega)
          rw [phi, dif_neg hn]
          simp [psi, letterCount, delta, Ne.symm h0, ha, h]
      rw [if_neg h, if_neg h, psi_cons, hp]

private lemma image_length (s : List (Fin m)) :
    ((subst (phi hm) s).length : ℤ) = 2 * s.length - psi s (terminal hm) := by
  induction s with
  | nil => simp [subst, psi, letterCount]
  | cons a s ih =>
    rw [D5.S1.Words.RankOneMorphismIterationBound.subst_cons,
      List.length_append, Nat.cast_add, ih, List.length_cons, Nat.cast_add,
      Nat.cast_one, psi_cons]
    by_cases h : a = terminal hm
    · have hn : ¬ a.val + 1 < m := by rw [h]; simp [terminal]; omega
      rw [phi, dif_neg hn]
      simp [delta, h]; ring
    · have hn : a.val + 1 < m := by
        have := a.isLt
        have hv : a.val ≠ m - 1 := fun h' => h (Fin.ext h')
        omega
      simp [phi, hn, delta, Ne.symm h]; ring

private lemma nonzero_head_defect (h3 : 3 ≤ m) (a : Fin m) (z : List (Fin m))
    (ha : a ≠ zero hm) (hf : FRS hm (a :: z)) : Defect hm (a :: z) := by
  let b : Fin m := if a.val = 1 then ⟨2, by omega⟩ else ⟨1, by omega⟩
  have hb0 : b ≠ zero hm := by
    intro h
    have hv := congrArg Fin.val h
    change b.val = 0 at hv
    dsimp [b] at hv
    split_ifs at hv
  have hba : b ≠ a := by
    intro h
    have hv := congrArg Fin.val h
    dsimp [b] at hv
    split_ifs at hv <;> simp_all [MBonacciSentinelDesubstitution.zero]
  obtain ⟨q, hq⟩ := hf b
  have hb : word hm (q + (z.length + 1)) = b := by
    have h := congrArg (fun u : List (Fin m) => u[z.length + 1]?) hq
    simpa [Occ, factor] using h
  have hn := (actual_word_laws hm).2.2.2.2.2.1 (q + (z.length + 1))
    (by simpa [hb] using hb0)
  have hs : factor (word hm) (q + 1) (z.length + 1) = z ++ [b] := by
    have h := congrArg List.tail hq
    simpa [Occ, factor, List.range_succ_eq_map, List.map_map,
      Function.comp_def, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h
  have hv : Occ hm (z ++ [b, zero hm]) (q + 1) := by
    have he : q + 1 + (z.length + 1) = q + (z.length + 1) + 1 := by omega
    unfold Occ
    simp only [List.length_append, List.length_cons, List.length_nil]
    change factor (word hm) (q + 1) (z.length + 1 + 1) = _
    unfold factor
    rw [List.range_succ]
    simp only [List.map_append, List.map_singleton]
    change factor (word hm) (q + 1) (z.length + 1) ++
      [word hm (q + 1 + (z.length + 1))] = _
    rw [hs, he, hn]
    simp
  refine ⟨z ++ [b, zero hm], q + 1, b, zero hm, a, hv, by simp,
    hb0, hba, Ne.symm ha, ?_⟩
  intro i
  rw [psi_append, psi_cons, psi_cons, psi_cons]
  simp only [psi, letterCount, List.count_nil, Nat.cast_zero, add_zero]
  ring

private lemma defect_lift (s v : List (Fin m)) (a b c : Fin m)
    (hlen : v.length = s.length + 1) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hd : ∀ i, psi v i - psi s i = delta a i + delta b i - delta c i)
    (w : List (Fin m)) (p : ℕ) (hw : Occ hm w p)
    (hl : (w.length : ℤ) = (subst (phi hm) v).length +
      (psi v (terminal hm) - psi s (terminal hm)))
    (hp : ∀ i, psi w i = psi (subst (phi hm) v) i +
      (psi v (terminal hm) - psi s (terminal hm)) * delta (zero hm) i) :
    Defect hm (T hm s) := by
  have hi : ∀ i : Fin m, rot hm i = zero hm ↔ i = terminal hm := by
    intro i
    rw [← rot_terminal hm, rot_equiv, rot_equiv]
    exact (finRotate m).injective.eq_iff
  refine ⟨w, p, rot hm a, rot hm b, rot hm c, hw, ?_, ?_, ?_, ?_, ?_⟩
  · have hv := image_length hm v
    have hs := image_length hm s
    simp only [T, List.length_append, List.length_singleton]
    omega
  · simpa [rot_equiv] using hab
  · simpa [rot_equiv] using hac
  · simpa [rot_equiv] using hbc
  · intro j
    let i := (finRotate m).symm j
    have he : rot hm i = j := by
      rw [rot_equiv hm]
      exact (finRotate m).apply_symm_apply j
    rw [← he]
    rw [hp, T, psi_append, image_counts, image_counts,
      delta_rot, delta_rot, delta_rot]
    have hz : psi [zero hm] (rot hm i) = delta (zero hm) (rot hm i) := by
      rw [psi_cons]; simp [psi, letterCount]
    rw [hz]
    by_cases ht : i = terminal hm
    · simp only [ht, rot_terminal, delta]
      have ht' := hd (terminal hm)
      rw [hlen]
      push_cast
      simp only [delta] at ht'
      linarith
    · simp only [ht, if_false]
      have hzero : delta (zero hm) (rot hm i) = 0 := by simp [delta, hi, ht]
      rw [hzero]
      simpa using hd i

private lemma defect_transport (s : List (Fin m)) : Defect hm s → Defect hm (T hm s) := by
  rintro ⟨v, q, a, b, c, hv, hlen, hab, hac, hbc, hd⟩
  let d := psi v (terminal hm) - psi s (terminal hm)
  have hdv : d = -1 ∨ d = 0 ∨ d = 1 := by
    have h := hd (terminal hm)
    by_cases ha : terminal hm = a <;> by_cases hb : terminal hm = b <;>
      by_cases hc : terminal hm = c <;> simp_all [delta, d]
  have hne : v ≠ [] := by intro h; simp [h] at hlen
  obtain ⟨hwhole, hsentinel, htail⟩ := occurrence_transport hm v q hv
  rcases hdv with hdneg | hd0 | hd1
  · apply defect_lift hm s v a b c hlen hab hac hbc hd
      (subst (phi hm) v).tail (boundary hm q + 1) (htail hne)
    · have hpos : 0 < (subst (phi hm) v).length := by
        cases v with
        | nil => contradiction
        | cons x u => simp [subst, phi]; split <;> simp
      simp only [List.length_tail]
      change _ = _ + d
      rw [hdneg]
      omega
    · intro i
      change _ = _ + d * _
      rw [hdneg]
      cases v with
      | nil => contradiction
      | cons x u =>
        simp only [subst, List.flatMap_cons]
        unfold phi
        split <;> simp [psi_cons]
  · apply defect_lift hm s v a b c hlen hab hac hbc hd
      (subst (phi hm) v) (boundary hm q) hwhole
    · change _ = _ + d
      simp [hd0]
    · intro i
      change _ = _ + d * _
      simp [hd0]
  · apply defect_lift hm s v a b c hlen hab hac hbc hd
      (T hm v) (boundary hm q) hsentinel
    · change _ = _ + d
      simp [T, hd1]
    · intro i
      change _ = _ + d * _
      rw [hd1]
      rw [T, psi_append, psi_cons]
      simp [psi, letterCount]

private lemma defect_free_frs (h3 : 3 ≤ m) (r : List (Fin m))
    (hf : FRS hm r) (hd : ¬ Defect hm r) :
    ∃ k : ℕ, r = ((T hm)^[k]) [] := by
  generalize he : r.length = n
  induction n using Nat.strong_induction_on generalizing r with
  | h n ih =>
    cases r with
    | nil => exact ⟨0, rfl⟩
    | cons a z =>
      have ha : a = zero hm := by
        by_contra h
        exact hd (nonzero_head_defect hm h3 a z h hf)
      obtain ⟨s, hs, _⟩ := fully_right_special_descent hm (a :: z)
        (by simp) (by simp [ha]) hf
      have hds : ¬ Defect hm s := by
        intro h
        exact hd (hs.1.symm ▸ defect_transport hm s h)
      obtain ⟨k, hk⟩ := ih s.length (by omega) s hs.2.2.1 hds rfl
      refine ⟨k + 1, ?_⟩
      rw [hs.1, hk, Function.iterate_succ_apply']

def star (r : List (Fin m)) (a : Fin m) : Fin m → ℕ :=
  fun i => letterCount r i + if i = a then 1 else 0

lemma star_injective (r : List (Fin m)) : Function.Injective (star r) := by
  intro a b h
  by_contra hab
  have hi := congrFun h a
  simp [star, hab] at hi

lemma star_subset (r : List (Fin m)) (hf : FRS hm r) :
    Set.range (star r) ⊆ parikhImage hm (r.length + 1) := by
  rintro x ⟨a, rfl⟩
  obtain ⟨q, hq⟩ := hf a
  refine ⟨q, ?_⟩
  have he : r.length + 1 = (r ++ [a]).length := by simp
  dsimp only
  rw [he, show factor (word hm) q (r ++ [a]).length = r ++ [a] from hq]
  funext i
  by_cases h : i = a
  · simp [star, letterCount, h, List.count_append]
  · simp [star, letterCount, h, Ne.symm h, List.count_append]

private lemma minimum_no_defect (r : List (Fin m)) (hf : FRS hm r)
    (hc : (parikhImage hm (r.length + 1)).ncard = m) : ¬ Defect hm r := by
  have he : Set.range (star r) = parikhImage hm (r.length + 1) := by
    refine Set.eq_of_subset_of_ncard_le (star_subset hm r hf) ?_
      (parikhImage_finite hm _)
    · rw [hc, Set.ncard_range_of_injective (star_injective r)]
      simp
  rintro ⟨v, q, a, b, c, hv, hlen, _, hac, hbc, hd⟩
  have hmemb : (fun i => letterCount v i) ∈ parikhImage hm (r.length + 1) := by
    refine ⟨q, ?_⟩
    dsimp only
    rw [← hlen, show factor (word hm) q v.length = v from hv]
  rw [← he] at hmemb
  obtain ⟨x, hx⟩ := hmemb
  have hs := congrFun hx c
  have hn : psi v c - psi r c = -1 := by
    simpa [delta, Ne.symm hac, Ne.symm hbc] using hd c
  dsimp [star] at hs
  have hle : letterCount r c ≤ letterCount v c := by omega
  have hz : psi r c ≤ psi v c := by
    dsimp [psi]
    exact_mod_cast hle
  omega

/-- Minimum complete Parikh cardinality forces a sentinel-iterate length. -/
theorem minimal_abelian_complexity_length (h3 : 3 ≤ m) (n : ℕ) (hn : 1 ≤ n)
    (hc : (parikhImage hm n).ncard = m) :
    ∃ k : ℕ, n = (((T hm)^[k]) ([] : List (Fin m))).length + 1 := by
  let r := (factor (word hm) 0 (n - 1)).reverse
  obtain ⟨hlen, _, hf⟩ := reversed_prefix_fully_right_special hm (n - 1)
  have he : n = r.length + 1 := by dsimp [r]; omega
  have hd : ¬ Defect hm r := minimum_no_defect hm r hf (by simpa [← he] using hc)
  obtain ⟨k, hk⟩ := defect_free_frs hm h3 r hf hd
  exact ⟨k, by rw [he, hk]⟩

end D5.S1.Words.MBonacciMinimumParikhDescent
