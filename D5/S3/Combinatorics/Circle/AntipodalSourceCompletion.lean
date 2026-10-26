/- GID: D5/S3/Combinatorics/Circle/AntipodalSourceCompletion
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/AntipodalSourceCompletion
   mirror-E: none(waiver:audit-open-22063)
   anchors: [mathlib/module/Mathlib.Logic.Equiv.Fin.Rotate, mathlib/module/Mathlib.Data.List.Perm.Basic]
   utility: none
   digest: One actual opposite-value pair forces a complete physical source ordering at the conjectured capacity. -/
module
public import D5.S3.Combinatorics.Circle.TwoOppositeLargeExchange

/-! # Opposite actual source values give full completion

This is full completion for a source subdomain, not a conditional exchange:
the only additional source condition is one actual opposite-value pair,
including the all-zero row. In particular there is no value-injectivity, coprimality,
least-period, involutive-rotation, or externally supplied matching premise.

Odd-modulus centered doubling commutes with negation. The source_cycle seam
propagates one opposite pair along the physical successor cycle. Translation
by j-i is consequently a sign-reversing permutation of ALL physical labels.
Its restriction from positive labels onto negative labels is bijective even
when the translation has cycles longer than two. We enumerate ONLY positive
labels as pair heads, rather than incorrectly making a pair for every label.

Capacity is exactly TwoOppositeLargeExchange.C = ExpandingSourcePath.half,
never SourceWidth.capacity. All natural prefixes are included. The main
theorem also returns endpoint zero, actual Legal, Nodup, and exhaustive univ.

Full C3.1 outside this source subdomain remains open.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
namespace D5.S3.Combinatorics.Circle.AntipodalSourceCompletion

open SourceWidth ExpandingSourcePath MixedSuffixEnergy TwoOppositeLargeExchange

/-- An actual opposite relation propagates to the whole physical rotation.
The hypothesis need not assert injectivity of the numerical source, and the
rotation is not asserted to have order two. Consumed by full completion. -/
theorem opposite_rotation {k : ℕ} (hk : 3 ≤ k) (t : ℕ) (i j : Fin k)
    (hop : s k t j = -s k t i) :
    ∀ h : Fin k, s k t (finCycle (j - i) h) = -s k t h := by
  letI : NeZero k := ⟨by omega⟩
  -- source_cycle already proves the actual successor relation at the seam.
  have hcycle := (ZeroSumSubsets.source_cycle (by omega : 0 < k) t).2.2
  have hstep (q : Fin k) :
      s k t (finRotate k q) = doubleStep (N k) (s k t q) := by
    have he := hcycle q
    change 2 * s k t q - s k t (finRotate k q) = N k *
      (if N k < 4 * s k t q then 1 else if 4 * s k t q < -N k then -1 else 0) at he
    unfold doubleStep
    split_ifs at he ⊢ <;> omega
  have hN : 0 ≤ N k := le_of_lt (source_geometry hk).2.2.2.1
  have hprop (m : ℕ) : s k t (hit k m j) = -s k t (hit k m i) := by
    induction m with
    | zero => simpa only [hit_zero] using hop
    | succ m ih =>
      change s k t (((finRotate k : Fin k → Fin k)^[m + 1]) j) =
        -s k t (((finRotate k : Fin k → Fin k)^[m + 1]) i)
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      change s k t (finRotate k (hit k m j)) =
        -s k t (finRotate k (hit k m i))
      rw [hstep, hstep, ih, doubleStep_neg hN]
  have hhit (q a : Fin k) : hit k a.val q = q + a := by
    simpa only [hit, finCycle_apply] using
      (congrFun (finCycle_eq_finRotate_iterate (k := a)) q).symm
  intro h
  have he := hprop (h - i).val
  rw [hhit, hhit] at he
  have hi : i + (h - i) = h := by abel
  have hj : j + (h - i) = h + (j - i) := by abel
  simpa only [hi, hj, finCycle_apply] using he

/-- Each actual positive/negative pair is a zero-total strip block.
This helper carries labels throughout; no set of numerical values is formed. -/
private theorem pair_blocks {α : Type*} (f : α → ℤ) (R : α → α)
    (B : ℤ) (hB : 0 ≤ B) (hR : ∀ p, f (R p) = -f p)
    (P : List α) (hb : ∀ p ∈ P, 0 ≤ f p ∧ f p ≤ B) :
    mass f (P.flatMap (fun p => [p, R p])) = 0 ∧
      InStrip f B 0 (P.flatMap (fun p => [p, R p])) := by
  revert hb
  induction P with
  | nil =>
    intro _
    exact ⟨rfl, le_refl _, hB⟩
  | cons p P ih =>
    intro hb
    have hp := hb p (by simp)
    obtain ⟨hm, hs⟩ := ih (fun q hq => hb q (by simp [hq]))
    constructor
    · change f p + (f (R p) + mass f (P.flatMap (fun q => [q, R q]))) = 0
      rw [hR p, hm]
      omega
    · change 0 ≤ (0 : ℤ) ∧ 0 ≤ B ∧
        0 ≤ 0 + f p ∧ 0 + f p ≤ B ∧
        InStrip f B (0 + f p + f (R p)) (P.flatMap (fun q => [q, R q]))
      exact ⟨le_refl _, hB, by omega, by omega, by simpa [hR p] using hs⟩

/-- The sign-reversing permutation gives a genuine positive-to-negative
physical matching. Zero labels are enumerated separately, once each. -/
private theorem complete_from_sign_reversal {k : ℕ} (f : Fin k → ℤ)
    (R : Equiv.Perm (Fin k)) (B : ℤ) (hB : 0 ≤ B)
    (hb : ∀ q, f q ≤ B) (hR : ∀ q, f (R q) = -f q) :
    ∃ L : List (Fin k), L.Perm (List.ofFn (fun q : Fin k => q)) ∧
      InStrip f B 0 L ∧ mass f L = 0 := by
  classical
  let P : List (Fin k) := (Finset.univ.filter (fun q => 0 < f q)).toList
  let Z : List (Fin k) := (Finset.univ.filter (fun q => f q = 0)).toList
  have hP (q : Fin k) : q ∈ P ↔ 0 < f q := by simp [P]
  have hZ (q : Fin k) : q ∈ Z ↔ f q = 0 := by simp [Z]
  have hM (q : Fin k) : q ∈ P.map R ↔ f q < 0 := by
    constructor
    · intro hq
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hq
      have hp0 := (hP p).mp hp
      rw [hR p]
      omega
    · intro hq
      have he : f q = -f (R.symm q) := by
        simpa only [R.apply_symm_apply] using hR (R.symm q)
      exact List.mem_map.mpr ⟨R.symm q, (hP _).mpr (by omega), R.apply_symm_apply q⟩
  have hPnd : P.Nodup := Finset.nodup_toList _
  have hZnd : Z.Nodup := Finset.nodup_toList _
  have hPMdis : List.Disjoint P (P.map R) := by
    apply List.disjoint_left.mpr
    intro q hqP hqM
    have hp := (hP q).mp hqP
    have hn := (hM q).mp hqM
    omega
  have hPMnd : (P ++ P.map R).Nodup :=
    hPnd.append (hPnd.map R.injective) hPMdis
  have hdisZ : List.Disjoint (P ++ P.map R) Z := by
    apply List.disjoint_left.mpr
    intro q hq hqZ
    have hz := (hZ q).mp hqZ
    rcases List.mem_append.mp hq with hqP | hqM
    · have hp := (hP q).mp hqP
      omega
    · have hn := (hM q).mp hqM
      omega
  have hfullnd : ((P ++ P.map R) ++ Z).Nodup := hPMnd.append hZnd hdisZ
  have hfullperm : ((P ++ P.map R) ++ Z).Perm
      (List.ofFn (fun q : Fin k => q)) := by
    apply (List.perm_ext_iff_of_nodup hfullnd
      (List.nodup_ofFn_ofInjective (f := fun q : Fin k => q) (fun _ _ he => he))).mpr
    intro q
    constructor
    · intro _
      exact List.mem_ofFn.mpr ⟨q, rfl⟩
    · intro _
      simp only [List.mem_append, hP, hM, hZ]
      omega
  let pairs : List (Fin k) := P.flatMap (fun p => [p, R p])
  -- Mathlib supplies the interleaving permutation, avoiding a new list scheduler.
  have hpairs : pairs.Perm (P ++ P.map R) := by
    simpa [pairs, ← List.map_eq_flatMap] using
      (List.flatMap_append_perm P (fun p => [p]) (fun p => [R p])).symm
  obtain ⟨hm, hs⟩ := pair_blocks f R B hB hR P
    (fun p hp => ⟨le_of_lt ((hP p).mp hp), hb p⟩)
  change mass f pairs = 0 at hm
  change InStrip f B 0 pairs at hs
  have hmZ : mass f Z = 0 := by
    unfold mass
    apply List.sum_eq_zero
    intro z hz
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hz
    exact (hZ q).mp hq
  have hsZ : InStrip f B 0 Z := by
    apply inStrip_nonpos (fun q hq => le_of_eq ((hZ q).mp hq)) hB
    change 0 ≤ 0 + mass f Z
    simpa only [hmZ, zero_add] using (le_refl (0 : ℤ))
  refine ⟨pairs ++ Z, (hpairs.append_right Z).trans hfullperm, ?_, ?_⟩
  · apply inStrip_append hs
    change InStrip f B (0 + mass f pairs) Z
    simpa only [hm, zero_add] using hsZ
  · simp only [mass, List.map_append, List.sum_append] at hm hmZ ⊢
    omega

/-- Full actual-source completion from one actual opposite-value pair.
All source labels, including repeated-valued physical occurrences, are used.
The pair may have value zero, so the all-zero row is included.
The conclusion is at C k and contains every natural zero-start prefix bound,
endpoint zero, and the existing native Legal predicate. -/
theorem actualSource_opposite_full_completion
    {k : ℕ} (hk : 3 ≤ k) (t : ℕ)
    (hopposite : ∃ i j : Fin k, s k t j = -s k t i) :
    ∃ L : List (Fin k),
      L.Perm (List.ofFn (fun q : Fin k => q)) ∧
      L.Nodup ∧ L.toFinset = Finset.univ ∧
      InStrip (s k t) (C k) 0 L ∧
      (∀ n : ℕ, 0 ≤ mass (s k t) (L.take n) ∧
        mass (s k t) (L.take n) ≤ C k) ∧
      mass (s k t) L = 0 ∧ Legal k t L := by
  classical
  obtain ⟨i, j, hij⟩ := hopposite
  obtain ⟨hQ, _hN, hC, hN0, hodd⟩ := source_geometry hk
  have hC0 : 0 ≤ C k := by change 0 ≤ half k; omega
  have hb (q : Fin k) : s k t q ≤ C k :=
    (centered_bounds hN0 hodd ((2 : ℤ) ^ q.val * (t : ℤ))).2
  obtain ⟨L, hp, hs, hm⟩ := complete_from_sign_reversal (s k t)
    (finCycle (j - i)) (C k) hC0 hb (opposite_rotation hk t i j hij)
  have hn : L.Nodup := hp.nodup_iff.mpr
    (List.nodup_ofFn_ofInjective (f := fun q : Fin k => q) (fun _ _ he => he))
  have hu : L.toFinset = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro q
    exact List.mem_toFinset.mpr (hp.mem_iff.mpr (List.mem_ofFn.mpr ⟨q, rfl⟩))
  have hlegal : Legal k t L := legal_of_strip hn hs
  exact ⟨L, hp, hn, hu, hs, hlegal.2, hm, hlegal⟩

end D5.S3.Combinatorics.Circle.AntipodalSourceCompletion
