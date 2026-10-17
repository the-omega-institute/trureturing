/- GID: D5/S3/Combinatorics/FiniteDifferences/GilbreathExtension
   generality: G
   mirror-B: D5/B/S3/Combinatorics/FiniteDifferences/GilbreathExtension
   mirror-E: none(waiver:noncomputational)
   anchors: []
   utility: none
   digest: The sharp all-length component maximum for unrestricted integer Gilbreath extensions. -/

import Mathlib.Data.Int.Basic
import Mathlib.Data.List.Pairwise
import Mathlib.Data.Set.Card
import Mathlib.Data.Int.Interval
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.FiniteDifferences.GilbreathExtension

/-- One row of adjacent absolute differences, in the original order. -/
def difference (s : List ℤ) : List ℤ :=
  List.zipWith (fun x y => |y - x|) s s.tail

/-- Row zero is the input; each positive row applies `difference` once. -/
def row (s : List ℤ) : ℕ → List ℤ
  | 0 => s
  | r + 1 => difference (row s r)

/-- Every nonempty positive row has leftmost entry one. -/
def isGilbreath (s : List ℤ) : Prop :=
  ∀ r : ℕ, 0 < r → r < s.length → (row s r).head? = some 1

/-- The source family of length `n`, without any restriction on future extensions. -/
def admissible (n : ℕ) (s : List ℤ) : Prop :=
  s.length = n ∧ s.Pairwise (fun x y => x < y) ∧
    (∃ tail : List ℤ, s = 2 :: 3 :: tail) ∧ isGilbreath s

/-- All integer extensions preserving the left edge; no monotonicity test is applied. -/
def validExtensions (s : List ℤ) : Set ℤ :=
  {k | isGilbreath (s ++ [k])}

/-- Endpoints of nonempty maximal runs in the step-two lattice. -/
def maximalStepTwoRuns (X : Set ℤ) : Set (ℤ × ℤ) :=
  {ab | ab.1 ≤ ab.2 ∧ (ab.2 - ab.1) % 2 = 0 ∧
    (∀ z : ℤ, ab.1 ≤ z → z ≤ ab.2 → (z - ab.1) % 2 = 0 → z ∈ X) ∧
    ab.1 - 2 ∉ X ∧ ab.2 + 2 ∉ X}

/-- A single residue class modulo two, allowing either integer parity. -/
def oneParity (X : Set ℤ) : Prop :=
  ∃ p : ℤ, ∀ x ∈ X, x % 2 = p % 2

/-- Explicit finiteness guards for both the extension set and its literal runs. -/
def extensionGeometry (s : List ℤ) : Prop :=
  (validExtensions s).Finite ∧ oneParity (validExtensions s) ∧
    (maximalStepTwoRuns (validExtensions s)).Finite

/-- Cardinality of the endpoint pairs; meaningful as a run count under the finite guard. -/
noncomputable def stepTwoRunCount (X : Set ℤ) : ℕ :=
  (maximalStepTwoRuns X).ncard

/-- Muney Section 16(4), expanded into universal upper bound and eligible attainment.
The finite guards are conclusions, so infinite-set cardinality conventions cannot prove it. -/
def componentMaximum : Prop :=
  ∀ n : ℕ, 5 ≤ n →
    (∀ s : List ℤ, admissible n s →
      extensionGeometry s ∧ stepTwoRunCount (validExtensions s) ≤ 2 ^ (n - 4)) ∧
    (∃ s : List ℤ, admissible n s ∧ extensionGeometry s ∧
      stepTwoRunCount (validExtensions s) = 2 ^ (n - 4))


private theorem difference_cons (a b : ℤ) (s : List ℤ) :
    difference (a :: b :: s) = |b - a| :: difference (b :: s) := rfl

private theorem difference_length (s : List ℤ) :
    (difference s).length = s.length - 1 := by
  simp [difference, List.length_zipWith, List.length_tail]

/-- Each row has exactly the source triangle length. -/
private theorem row_length (s : List ℤ) (r : ℕ) : (row s r).length = s.length - r := by
  induction r with
  | zero => rfl
  | succ r ih => simp only [row, difference_length, ih]; omega


/-- The source recurrence with zero-based column indices; only valid indices are used. -/
def sourceTriangle (s : List ℤ) : ℕ → ℕ → ℤ
  | 0, i => s[i]?.getD 0
  | r+1, i => |sourceTriangle s r (i+1)-sourceTriangle s r i|

private theorem difference_entry (s : List ℤ) (i : ℕ) (hi : i + 1 < s.length) :
    (difference s)[i]'(by rw [difference_length]; omega) =
      |s[i+1]-s[i]| := by
  simp only [difference,List.getElem_zipWith,List.getElem_tail]

private theorem row_source_triangle (s : List ℤ) (r i : ℕ) (hi : i + r < s.length) :
    (row s r)[i]'(by rw [row_length]; omega) = sourceTriangle s r i := by
  induction r generalizing i with
  | zero =>
    simp only [Nat.add_zero] at hi
    change s[i] = s[i]?.getD 0
    rw [List.getElem?_eq_getElem hi]
    rfl
  | succ r ih =>
    change (difference (row s r))[i]'(by rw [difference_length,row_length]; omega) =
      |sourceTriangle s r (i+1)-sourceTriangle s r i|
    rw [difference_entry _ i (by rw [row_length]; omega)]
    rw [ih (i+1) (by omega),ih i (by omega)]

private theorem row_difference (s : List ℤ) (r : ℕ) :
    row (difference s) r = row s (r + 1) := by
  induction r with
  | zero => rfl
  | succ r ih => simpa only [row] using congrArg difference ih

private theorem gilbreath_difference {s : List ℤ} (h : isGilbreath s) :
    isGilbreath (difference s) := by
  intro r hr hrl
  rw [row_difference]
  apply h (r + 1) (by omega)
  rw [difference_length] at hrl
  omega

private theorem gilbreath_iff (s : List ℤ) (h : 2 ≤ s.length) :
    isGilbreath s ↔ (difference s).head? = some 1 ∧ isGilbreath (difference s) := by
  constructor
  · intro hs
    exact ⟨hs 1 (by omega) (by omega), gilbreath_difference hs⟩
  · rintro ⟨hh, hd⟩ r hr hrl
    cases r with
    | zero => omega
    | succ r =>
      cases r with
      | zero => exact hh
      | succ r =>
        rw [← row_difference]
        apply hd (r + 1) (by omega)
        rw [difference_length]
        omega

private theorem difference_append (s : List ℤ) (a k : ℤ) :
    difference (s ++ [a,k]) = difference (s ++ [a]) ++ [|k-a|] := by
  induction s with
  | nil => rfl
  | cons b s ih =>
    cases s with
    | nil => rfl
    | cons c s => simpa only [List.cons_append, difference_cons] using congrArg (List.cons |c-b|) ih

private theorem difference_append_last (s : List ℤ) (hs : s ≠ []) (k : ℤ) :
    difference (s ++ [k]) = difference s ++ [|k-s.getLast hs|] := by
  have he := difference_append s.dropLast (s.getLast hs) k
  have hl : s.dropLast ++ [s.getLast hs, k] = s ++ [k] := by
    calc
      _ = (s.dropLast ++ [s.getLast hs]) ++ [k] :=
        (List.append_assoc s.dropLast [s.getLast hs] [k]).symm
      _ = _ := by rw [List.dropLast_append_getLast hs]
  rw [hl, List.dropLast_append_getLast hs] at he
  exact he

private theorem difference_head_append (s : List ℤ) (h : 2 ≤ s.length) (k : ℤ) :
    (difference (s ++ [k])).head? = (difference s).head? := by
  cases s with
  | nil => simp at h
  | cons a s =>
    cases s with
    | nil => simp at h
    | cons b s => rfl

/-- The unrestricted extension fiber is the actual absolute-difference preimage. -/
private theorem extension_recursion (s : List ℤ) (h : 2 ≤ s.length) (hs : isGilbreath s)
    (k : ℤ) :
    k ∈ validExtensions s ↔ |k-s.getLast (by intro e; simp [e] at h)| ∈
      validExtensions (difference s) := by
  unfold validExtensions
  simp only [Set.mem_ofPred_eq]
  rw [gilbreath_iff _ (by simp; omega), difference_head_append s h]
  have hh := (gilbreath_iff s h).mp hs
  rw [difference_append_last s (by intro e; simp [e] at h)]
  exact and_iff_right hh.1

private theorem singleton_extensions (a : ℤ) :
    validExtensions [a] = {a-1,a+1} := by
  ext k
  simp only [validExtensions, Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  rw [gilbreath_iff _ (by simp)]
  change (some |k-a| = some (1 : ℤ) ∧ isGilbreath [|k-a|]) ↔ _
  simp only [Option.some.injEq]
  have hg : isGilbreath [|k-a|] := by
    intro r hr hrl
    simp only [List.length_singleton] at hrl
    omega
  simp only [and_iff_left hg]
  constructor
  · intro hk
    rcases le_total a k with h | h
    · rw [abs_of_nonneg (by omega)] at hk; right; omega
    · rw [abs_of_nonpos (by omega)] at hk; left; omega
  · rintro (rfl | rfl) <;> norm_num

private theorem abs_preimage_finite (a : ℤ) {X : Set ℤ} (hX : X.Finite) :
    {k : ℤ | |k-a| ∈ X}.Finite := by
  apply ((hX.image (fun d => a+d)).union (hX.image (fun d => a-d))).subset
  intro k hk
  rcases le_total a k with h | h
  · left; refine ⟨k-a, ?_, by dsimp; omega⟩
    simpa [abs_of_nonneg (by omega : 0 ≤ k-a)] using hk
  · right; refine ⟨a-k, ?_, by dsimp; omega⟩
    simpa [abs_of_nonpos (by omega : k-a ≤ 0)] using hk

private theorem abs_preimage_parity (a : ℤ) {X : Set ℤ} (hX : oneParity X) :
    oneParity {k : ℤ | |k-a| ∈ X} := by
  obtain ⟨p,hp⟩ := hX
  refine ⟨a+p, ?_⟩
  intro k hk
  have he := hp |k-a| hk
  rcases le_total a k with h | h
  · rw [abs_of_nonneg (by omega)] at he
    omega
  · rw [abs_of_nonpos (by omega)] at he
    omega

private theorem finite_extensions (s : List ℤ) (hne : s ≠ []) (hs : isGilbreath s) :
    (validExtensions s).Finite ∧ oneParity (validExtensions s) := by
  induction hn : s.length using Nat.strong_induction_on generalizing s with
  | h n ih =>
    cases s with
    | nil => exact False.elim (hne rfl)
    | cons a s =>
      cases s with
      | nil =>
        rw [singleton_extensions]
        refine ⟨Set.toFinite _, a-1, ?_⟩
        intro x hx
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
        rcases hx with rfl | rfl <;> omega
      | cons b s =>
        have hlen : 2 ≤ (a::b::s).length := by simp
        have hdne : difference (a::b::s) ≠ [] := by simp [difference_cons]
        obtain ⟨hf,hp⟩ := ih (difference (a::b::s)).length
          (by rw [difference_length]; simp at hn ⊢; omega) _ hdne
          (gilbreath_difference hs) rfl
        have he : validExtensions (a::b::s) =
            {k | |k-(a::b::s).getLast (by simp)| ∈ validExtensions (difference (a::b::s))} := by
          ext k; exact extension_recursion _ hlen hs k
        rw [he]
        exact ⟨abs_preimage_finite _ hf, abs_preimage_parity _ hp⟩


private theorem run_literal_iff (X : Set ℤ) (a b : ℤ) :
    (a, b) ∈ maximalStepTwoRuns X ↔
      ∃ m : ℕ, b = a+2*(m:ℤ) ∧
        (∀ i : ℕ, i ≤ m → a+2*(i:ℤ) ∈ X) ∧ a-2 ∉ X ∧ b+2 ∉ X := by
  constructor
  · rintro ⟨hab,hpar,hs,hl,hr⟩
    let m := ((b-a)/2).toNat
    have hm : (m:ℤ) = (b-a)/2 := by
      simp only [m,Int.toNat_of_nonneg (by omega : 0 ≤ (b-a)/2)]
    refine ⟨m,by omega,?_,hl,hr⟩
    intro i hi
    exact hs (a+2*(i:ℤ)) (by omega) (by omega) (by omega)
  · rintro ⟨m,he,hs,hl,hr⟩
    refine ⟨by dsimp; omega,by dsimp; omega,?_,hl,hr⟩
    intro z hz hzb hzp
    let i := ((z-a)/2).toNat
    have hi : (i:ℤ) = (z-a)/2 := by
      simp only [i,Int.toNat_of_nonneg (by omega : 0 ≤ (z-a)/2)]
    have him : i ≤ m := by dsimp at *; omega
    have hzi : z = a+2*(i:ℤ) := by dsimp at *; omega
    rw [hzi]
    exact hs i him

private theorem run_endpoints_mem {X : Set ℤ} {a b : ℤ}
    (h : (a, b) ∈ maximalStepTwoRuns X) : a ∈ X ∧ b ∈ X := by
  obtain ⟨m,he,hs,_,_⟩ := (run_literal_iff X a b).mp h
  constructor
  · simpa using hs 0 (by omega)
  · rw [he]
    exact hs m (le_refl _)

/-- Finite input sets have finitely many literal maximal endpoint runs. -/
private theorem maximal_runs_finite {X : Set ℤ} (hX : X.Finite) :
    (maximalStepTwoRuns X).Finite := by
  apply (hX.prod hX).subset
  intro ab hab
  exact run_endpoints_mem hab

/-- Eligible prefixes have genuinely finite, single-parity full extension geometry. -/
private theorem admissible_extension_geometry {n : ℕ} {s : List ℤ} (hs : admissible n s) :
    extensionGeometry s := by
  obtain ⟨_,_,⟨t,ht⟩,hg⟩ := hs
  have hne : s ≠ [] := by rw [ht]; simp
  obtain ⟨hf,hp⟩ := finite_extensions s hne hg
  exact ⟨hf,hp,maximal_runs_finite hf⟩


/-- A closed interval in one of the two integer parity lattices. -/
def parityInterval (a b : ℤ) : Set ℤ :=
  {x | a ≤ x ∧ x ≤ b ∧ (x-a) % 2 = 0}

private def intervalCover (X : Set ℤ) (C : List (ℤ × ℤ)) : Prop :=
  ∀ x, x ∈ X ↔ ∃ ab ∈ C, x ∈ parityInterval ab.1 ab.2

private theorem run_left_injective (X : Set ℤ) :
    Set.InjOn Prod.fst (maximalStepTwoRuns X) := by
  intro ab hab cd hcd he
  rcases ab with ⟨a,b⟩
  rcases cd with ⟨c,d⟩
  dsimp at he
  subst c
  simp only [maximalStepTwoRuns, Set.mem_ofPred_eq] at hab hcd
  have hbd : b = d := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · have hmem := hcd.2.2.1 (b+2) (by omega) (by omega) (by omega)
      exact hab.2.2.2.2 hmem
    · have hmem := hab.2.2.1 (d+2) (by omega) (by omega) (by omega)
      exact hcd.2.2.2.2 hmem
  subst d
  rfl

private theorem cover_run_count {X : Set ℤ} {C : List (ℤ × ℤ)}
    (hc : intervalCover X C) : stepTwoRunCount X ≤ C.length := by
  classical
  have hm : ∀ ab ∈ maximalStepTwoRuns X, ab.1 ∈ (C.map Prod.fst).toFinset := by
    intro ab hab
    obtain ⟨cd,hcd,ha⟩ := (hc ab.1).mp (run_endpoints_mem hab).1
    change cd.1 ≤ ab.1 ∧ ab.1 ≤ cd.2 ∧ (ab.1-cd.1)%2 = 0 at ha
    have he : ab.1 = cd.1 := by
      by_contra hne
      have hp : ab.1-2 ∈ parityInterval cd.1 cd.2 := by
        refine ⟨by omega, by omega, by omega⟩
      have hx := (hc (ab.1-2)).mpr ⟨cd,hcd,hp⟩
      exact hab.2.2.2.1 hx
    simp only [List.mem_toFinset, List.mem_map]
    exact ⟨cd,hcd,he.symm⟩
  have ht : ((↑(C.map Prod.fst).toFinset : Set ℤ)).Finite := Finset.finite_toSet _
  have h := Set.ncard_le_ncard_of_injOn Prod.fst hm (run_left_injective X) ht
  unfold stepTwoRunCount
  rw [Set.ncard_coe_finset] at h
  exact h.trans (by simpa only [List.length_map] using List.toFinset_card_le (C.map Prod.fst))

private def pullInterval (e : ℤ) (ab : ℤ × ℤ) : List (ℤ × ℤ) :=
  let c := max ab.1 (ab.1 % 2)
  let d := ab.2 - (ab.2-ab.1)%2
  if c ≤ d then [(e-d,e-c),(e+c,e+d)] else []

private theorem pullInterval_length (e : ℤ) (ab : ℤ × ℤ) :
    (pullInterval e ab).length ≤ 2 := by
  unfold pullInterval
  dsimp only
  split_ifs <;> simp

private theorem pullInterval_exact (e : ℤ) (ab : ℤ × ℤ) (x : ℤ) :
    |x-e| ∈ parityInterval ab.1 ab.2 ↔
      ∃ cd ∈ pullInterval e ab, x ∈ parityInterval cd.1 cd.2 := by
  rcases ab with ⟨a,b⟩
  unfold pullInterval parityInterval
  dsimp
  have hp : 0 ≤ a % 2 ∧ a % 2 < 2 := ⟨Int.emod_nonneg _ (by omega), Int.emod_lt_of_pos _ (by omega)⟩
  have hq : 0 ≤ (b - a) % 2 ∧ (b - a) % 2 < 2 :=
    ⟨Int.emod_nonneg _ (by omega), Int.emod_lt_of_pos _ (by omega)⟩
  by_cases h : max a (a%2) ≤ b-(b - a) % 2
  · rw [if_pos h]
    simp only [List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp,
      exists_eq_left]
    rcases le_total e x with hx | hx
    · rw [abs_of_nonneg (by omega)]
      rcases le_total a (a%2) with ha | ha
      · rw [max_eq_right ha]; omega
      · rw [max_eq_left ha]; omega
    · rw [abs_of_nonpos (by omega)]
      rcases le_total a (a%2) with ha | ha
      · rw [max_eq_right ha]; omega
      · rw [max_eq_left ha]; omega
  · rw [if_neg h]
    simp only [List.not_mem_nil, false_and, exists_false, iff_false]
    have ha : 0 ≤ |x-e| := abs_nonneg _
    rcases le_total a (a%2) with h' | h'
    · rw [max_eq_right h'] at h; omega
    · rw [max_eq_left h'] at h; omega

private theorem cover_pullback {X : Set ℤ} {C : List (ℤ × ℤ)}
    (hc : intervalCover X C) (e : ℤ) :
    intervalCover {x | |x-e| ∈ X} (C.flatMap (pullInterval e)) := by
  intro x
  change |x-e| ∈ X ↔ _
  rw [hc |x-e|]
  simp only [List.mem_flatMap]
  constructor
  · rintro ⟨ab,hab,hx⟩
    obtain ⟨cd,hcd,hxc⟩ := (pullInterval_exact e ab x).mp hx
    exact ⟨cd,⟨ab,hab,hcd⟩,hxc⟩
  · rintro ⟨cd,⟨ab,hab,hcd⟩,hx⟩
    exact ⟨ab,hab,(pullInterval_exact e ab x).mpr ⟨cd,hcd,hx⟩⟩

private theorem cover_pullback_length (C : List (ℤ × ℤ)) (e : ℤ) :
    (C.flatMap (pullInterval e)).length ≤ 2*C.length := by
  induction C with
  | nil => simp
  | cons ab C ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    have h := pullInterval_length e ab
    omega


private theorem four_fold_seed (t y z : ℤ) (ht : 0 ≤ t)
    (hyz : (y = 0 ∧ z = 0) ∨ (y = 2 ∧ z = 2) ∨
      (y = 2 ∧ z = 0) ∨ (y = 0 ∧ z = 2) ∨ (y = 4 ∧ z = 2)) :
    (abs (abs (t-y)-z) = 0 ∨ abs (abs (t-y)-z) = 2) ↔ t ≤ y+z+2 ∧ t%2 = 0 := by
  rcases hyz with h | h | h | h | h <;> rcases h with ⟨rfl,rfl⟩ <;>
    simp only [abs_eq_max_neg] <;> omega

private theorem four_entry_cover (s : List ℤ) (hl : s.length = 4) (hs : isGilbreath s) :
    ∃ C : List (ℤ × ℤ), intervalCover (validExtensions s) C ∧ C.length = 1 := by
  obtain ⟨a,b,c,d,rfl⟩ : ∃ a b c d : ℤ, s = [a,b,c,d] := by
    rcases s with _ | ⟨a,s⟩ <;> simp only [List.length_nil,List.length_cons] at hl
    · omega
    rcases s with _ | ⟨b,s⟩ <;> simp only [List.length_nil,List.length_cons] at hl
    · omega
    rcases s with _ | ⟨c,s⟩ <;> simp only [List.length_nil,List.length_cons] at hl
    · omega
    rcases s with _ | ⟨d,s⟩ <;> simp only [List.length_nil,List.length_cons] at hl
    · omega
    have hnil : s = [] := by cases s <;> simp_all
    subst s
    exact ⟨a,b,c,d,rfl⟩
  let y : ℤ := |d-c|
  let z : ℤ := abs (y-abs (c-b))
  have h1 := hs 1 (by omega) (by simp)
  have h2 := hs 2 (by omega) (by simp)
  have h3 := hs 3 (by omega) (by simp)
  change some |b-a| = some 1 at h1
  have he1 : |b-a| = 1 := by
    have hh : (row [a,b,c,d] 1)[0]'(by norm_num [row,difference]) = 1 :=
      Option.some.inj h1
    rw [row_source_triangle _ 1 0 (by simp)] at hh
    simpa [sourceTriangle] using hh
  change some (abs (abs (c-b)-abs (b-a))) = some 1 at h2
  rw [he1] at h2
  have he2 : abs (abs (c-b)-1) = 1 := Option.some.inj h2
  change some (abs (abs (abs (d-c)-abs (c-b))-abs (abs (c-b)-abs (b-a)))) = some 1 at h3
  rw [he1,he2] at h3
  have he3 : |z-1| = 1 := Option.some.inj h3
  have htri : (y = 0 ∧ z = 0) ∨ (y = 2 ∧ z = 2) ∨
      (y = 2 ∧ z = 0) ∨ (y = 0 ∧ z = 2) ∨ (y = 4 ∧ z = 2) := by
    have hx : 0 ≤ |c-b| := abs_nonneg _
    have hy : 0 ≤ y := abs_nonneg _
    have hz : 0 ≤ z := abs_nonneg _
    dsimp [z] at he3 hz ⊢
    simp only [abs_eq_max_neg] at he2 he3 ⊢
    dsimp [y] at *
    omega
  refine ⟨[(d-(y+z+2),d+(y+z+2))], ?_, rfl⟩
  intro k
  have hrec := extension_recursion [a,b,c,d] (by simp) hs k
  have hd := gilbreath_difference hs
  have hrec2 := extension_recursion (difference [a,b,c,d]) (by simp [difference]) hd |k-d|
  have hdd := gilbreath_difference hd
  have hrec3 := extension_recursion (difference (difference [a,b,c,d]))
    (by simp [difference]) hdd (abs (abs (k-d)-y))
  have hlast : difference (difference (difference [a,b,c,d])) = [1] := by
    change [abs (abs (abs (d-c)-abs (c-b))-abs (abs (c-b)-abs (b-a)))] = [1]
    rw [he1,he2]
    exact congrArg (fun x : ℤ => [x]) he3
  change k ∈ validExtensions [a,b,c,d] ↔ _
  rw [hrec]
  change |k-d| ∈ validExtensions (difference [a,b,c,d]) ↔ _
  rw [hrec2]
  change abs (abs (k-d)-y) ∈ validExtensions (difference (difference [a,b,c,d])) ↔ _
  rw [hrec3,hlast,singleton_extensions]
  change (abs (abs (abs (k-d)-y)-z) ∈ ({(1:ℤ)-1,1+1} : Set ℤ)) ↔ _
  norm_num only [sub_self, one_add_one_eq_two, Set.mem_insert_iff, Set.mem_singleton_iff]
  rw [four_fold_seed |k-d| y z (abs_nonneg _) htri]
  simp only [List.mem_singleton, exists_eq_left, parityInterval, Set.mem_ofPred_eq]
  have hz : 0 ≤ y+z+2 := by
    have := abs_nonneg (y-|c-b|)
    have := abs_nonneg (d-c)
    dsimp [y,z] at *
    omega
  have hp : (y+z+2)%2 = 0 := by rcases htri with h | h | h | h | h <;> omega
  simp only [abs_eq_max_neg]
  omega

private theorem extension_cover (s : List ℤ) (hl : 4 ≤ s.length) (hs : isGilbreath s) :
    ∃ C : List (ℤ × ℤ), intervalCover (validExtensions s) C ∧
      C.length ≤ 2^(s.length-4) := by
  induction hn : s.length using Nat.strong_induction_on generalizing s with
  | h n ih =>
    by_cases he : s.length = 4
    · obtain ⟨C,hc,hCl⟩ := four_entry_cover s he hs
      exact ⟨C,hc,by rw [← hn,hCl,he]; norm_num⟩
    · have hdlen : 4 ≤ (difference s).length := by rw [difference_length]; omega
      obtain ⟨C,hc,hCl⟩ := ih (difference s).length (by rw [difference_length]; omega)
        _ hdlen (gilbreath_difference hs) rfl
      let e := s.getLast (by intro h; simp [h] at hl)
      refine ⟨C.flatMap (pullInterval e), ?_, ?_⟩
      · have hp := cover_pullback hc e
        intro k
        exact (extension_recursion s (by omega) hs k).trans (hp k)
      · have hp := cover_pullback_length C e
        have he : s.length-4 = ((difference s).length-4)+1 := by rw [difference_length]; omega
        rw [← hn,he,pow_succ]
        omega

/-- The component upper bound holds for every Gilbreath list of length at least four. -/
private theorem universal_component_bound {s : List ℤ} (hl : 4 ≤ s.length) (hs : isGilbreath s) :
    stepTwoRunCount (validExtensions s) ≤ 2^(s.length-4) := by
  obtain ⟨C,hc,hCl⟩ := extension_cover s hl hs
  exact (cover_run_count hc).trans hCl

private theorem difference_shift (s : List ℤ) (c : ℤ) :
    difference (s.map (fun x => x+c)) = difference s := by
  induction s with
  | nil => rfl
  | cons a s ih =>
    cases s with
    | nil => rfl
    | cons b s =>
      simp only [List.map_cons, difference_cons]
      rw [show b+c-(a+c) = b-a by ring]
      simpa only [List.map_cons] using congrArg (List.cons |b-a|) ih

private theorem row_shift (s : List ℤ) (c : ℤ) (r : ℕ) :
    row (s.map (fun x => x+c)) (r+1) = row s (r+1) := by
  induction r with
  | zero => exact difference_shift s c
  | succ r ih => simpa only [row] using congrArg difference ih

private theorem gilbreath_shift (s : List ℤ) (c : ℤ) :
    isGilbreath (s.map (fun x => x+c)) ↔ isGilbreath s := by
  constructor <;> intro hs r hr hrl
  · cases r with
    | zero => omega
    | succ r =>
      rw [← row_shift s c r]
      exact hs (r+1) hr (by simpa using hrl)
  · cases r with
    | zero => omega
    | succ r =>
      rw [row_shift]
      exact hs (r+1) hr (by simpa using hrl)

private theorem extensions_shift (s : List ℤ) (c k : ℤ) :
    k ∈ validExtensions (s.map (fun x => x+c)) ↔ k-c ∈ validExtensions s := by
  have he : s.map (fun x => x+c) ++ [k] = (s++[k-c]).map (fun x => x+c) := by
    simp
  change isGilbreath (s.map (fun x => x+c) ++ [k]) ↔ _
  rw [he,gilbreath_shift]
  rfl

private def u : ℕ → List ℤ
  | 0 => [2]
  | m+1 => u m ++ [(2:ℤ)^(m+1)+1]

/-- Muney's attaining family, indexed by length minus four. -/
def attainingPrefix (m : ℕ) : List ℤ := u (m+2) ++ [(2:ℤ)^(m+3)-1]

private theorem u_length (m : ℕ) : (u m).length = m+1 := by
  induction m with
  | zero => rfl
  | succ m ih => simp [u,ih]

private theorem u_nonempty (m : ℕ) : u m ≠ [] := by
  intro h
  have := u_length m
  simp [h] at this

private theorem u_last (m : ℕ) : (u (m+1)).getLast (u_nonempty _) = (2:ℤ)^(m+1)+1 := by
  simp [u]

private theorem u_bounds (m : ℕ) (x : ℤ) (hx : x ∈ u m) :
    2 ≤ x ∧ x ≤ (2:ℤ)^m+1 := by
  induction m with
  | zero =>
    simp only [u,List.mem_singleton] at hx
    subst x
    norm_num
  | succ m ih =>
    simp only [u,List.mem_append,List.mem_singleton] at hx
    have hp : 1 ≤ (2:ℤ)^m := one_le_pow₀ (by norm_num)
    rw [pow_succ]
    rcases hx with hx | rfl
    · obtain ⟨ha,hb⟩ := ih hx
      constructor <;> nlinarith
    · rw [pow_succ]
      constructor <;> nlinarith

private theorem u_increasing (m : ℕ) : (u m).Pairwise (fun x y => x < y) := by
  induction m with
  | zero => simp [u]
  | succ m ih =>
    rw [u,List.pairwise_append]
    refine ⟨ih, by simp, ?_⟩
    intro x hx y hy
    simp only [List.mem_singleton] at hy
    subst y
    have hb := (u_bounds m x hx).2
    have hp : 0 < (2:ℤ)^m := pow_pos (by norm_num) _
    rw [pow_succ]
    nlinarith

private theorem u_starts (m : ℕ) : ∃ t, u (m+1) = 2::3::t := by
  induction m with
  | zero => exact ⟨[],by norm_num [u]⟩
  | succ m ih =>
    obtain ⟨t,ht⟩ := ih
    refine ⟨t++[(2:ℤ)^(m+2)+1], ?_⟩
    change u (m+1) ++ [_] = _
    rw [ht]
    rfl

private theorem u_difference (m : ℕ) :
    difference (u (m+1)) = (u m).map (fun x => x-1) := by
  induction m with
  | zero => norm_num [u,difference]
  | succ m ih =>
    rw [u,difference_append_last _ (u_nonempty _),ih,u_last]
    rw [u,List.map_append]
    have hp : 0 < (2:ℤ)^(m+1) := pow_pos (by norm_num) _
    have he : (2:ℤ)^(m+1+1)+1-((2:ℤ)^(m+1)+1) = (2:ℤ)^(m+1) := by
      rw [pow_succ]; ring
    rw [he,abs_of_pos hp]
    simp

private theorem attaining_length (m : ℕ) : (attainingPrefix m).length = m+4 := by
  simp [attainingPrefix,u_length]

private theorem attaining_last (m : ℕ) :
    (attainingPrefix m).getLast (by simp [attainingPrefix]) = (2:ℤ)^(m+3)-1 := by
  simp [attainingPrefix]

private theorem attaining_starts (m : ℕ) : ∃ t, attainingPrefix m = 2::3::t := by
  obtain ⟨t,ht⟩ := u_starts (m+1)
  exact ⟨t++[(2:ℤ)^(m+3)-1],by simp only [attainingPrefix,ht,List.cons_append]⟩

private theorem attaining_difference (m : ℕ) :
    difference (attainingPrefix (m+1)) = (attainingPrefix m).map (fun x => x-1) := by
  unfold attainingPrefix
  rw [difference_append_last _ (u_nonempty _),u_difference,u_last]
  rw [List.map_append]
  have hp : 1 ≤ (2:ℤ)^m := one_le_pow₀ (by norm_num)
  have he : (2:ℤ)^(m+1+3)-1-((2:ℤ)^(m+2+1)+1) = (2:ℤ)^(m+3)-2 := by
    simp only [show m+1+3 = m+3+1 by omega,show m+2+1 = m+3 by omega,pow_succ]
    ring
  rw [he,abs_of_nonneg (by rw [show m+3=m+0+3 by omega,pow_add]; norm_num; nlinarith)]
  simp only [List.map_singleton]
  congr 2
  ring

private theorem attaining_increasing (m : ℕ) :
    (attainingPrefix m).Pairwise (fun x y => x < y) := by
  rw [attainingPrefix,List.pairwise_append]
  refine ⟨u_increasing _,by simp,?_⟩
  intro x hx y hy
  simp only [List.mem_singleton] at hy
  subst y
  have hb := (u_bounds (m+2) x hx).2
  have hp : 1 ≤ (2:ℤ)^m := one_le_pow₀ (by norm_num)
  rw [show m+2=m+0+2 by omega,pow_add] at hb
  rw [show m+3=m+0+3 by omega,pow_add]
  norm_num at hb ⊢
  nlinarith

private theorem attaining_gilbreath (m : ℕ) : isGilbreath (attainingPrefix m) := by
  induction m with
  | zero =>
    intro r hr hrl
    rw [attaining_length] at hrl
    interval_cases r <;> norm_num [row,difference,attainingPrefix,u]
  | succ m ih =>
    apply (gilbreath_iff _ (by rw [attaining_length]; omega)).mpr
    rw [attaining_difference]
    constructor
    · obtain ⟨t,ht⟩ := attaining_starts m
      rw [ht]
      rfl
    · simpa only [sub_eq_add_neg] using (gilbreath_shift (attainingPrefix m) (-1)).mpr ih

private theorem attaining_admissible (m : ℕ) : admissible (m+4) (attainingPrefix m) :=
  ⟨attaining_length m,attaining_increasing m,attaining_starts m,attaining_gilbreath m⟩

private theorem translate_run_iff (X : Set ℤ) (e a b : ℤ) :
    (a, b) ∈ maximalStepTwoRuns {x | x-e ∈ X} ↔
      (a-e,b-e) ∈ maximalStepTwoRuns X := by
  simp only [maximalStepTwoRuns, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hab,hp,hs,hl,hr⟩
    refine ⟨by omega,by omega,?_,?_,?_⟩
    · intro z hz hzb hzp
      have hm := hs (e+z) (by omega) (by omega) (by omega)
      simpa using hm
    · intro hm
      apply hl
      convert hm using 1
      ring
    · intro hm
      apply hr
      convert hm using 1
      ring
  · rintro ⟨hab,hp,hs,hl,hr⟩
    refine ⟨by omega,by omega,?_,?_,?_⟩
    · intro z hz hzb hzp
      exact hs (z-e) (by omega) (by omega) (by omega)
    · intro hm
      apply hl
      convert hm using 1
      ring
    · intro hm
      apply hr
      convert hm using 1
      ring

private theorem translate_run_count (X : Set ℤ) (e : ℤ) :
    stepTwoRunCount {x | x-e ∈ X} = stepTwoRunCount X := by
  have he : maximalStepTwoRuns {x | x-e ∈ X} =
      (fun ab : ℤ × ℤ => (e+ab.1,e+ab.2)) '' maximalStepTwoRuns X := by
    ext ab
    rcases ab with ⟨a,b⟩
    rw [translate_run_iff]
    constructor
    · intro h
      exact ⟨(a-e,b-e),h,by ext <;> dsimp <;> ring⟩
    · rintro ⟨⟨c,d⟩,h,hcd⟩
      cases hcd
      simpa using h
  unfold stepTwoRunCount
  rw [he]
  apply Set.ncard_image_of_injective
  intro ab cd heq
  apply Prod.ext <;> have h := congrArg Prod.fst heq <;> have h' := congrArg Prod.snd heq <;>
    dsimp at * <;> omega

private theorem positive_upper_run {X : Set ℤ} (hp : ∀ x ∈ X, 2 ≤ x)
    (e : ℤ) {a b : ℤ} (hab : (a, b) ∈ maximalStepTwoRuns X) :
    (e+a,e+b) ∈ maximalStepTwoRuns {x | |x-e| ∈ X} := by
  have ha := hp a (run_endpoints_mem hab).1
  have hb := hp b (run_endpoints_mem hab).2
  rcases hab with ⟨hab,hpar,hs,hl,hr⟩
  refine ⟨by dsimp; omega,by dsimp; omega,?_,?_,?_⟩
  · intro z hz hzb hzp
    have hm := hs (z-e) (by dsimp at *; omega) (by dsimp at *; omega) (by dsimp at *; omega)
    change |z-e| ∈ X
    rw [abs_of_nonneg (by dsimp at *; omega)]
    exact hm
  · change |e+a-2-e| ∉ X
    rw [show e+a-2-e = a-2 by ring,abs_of_nonneg (by omega)]
    exact hl
  · change |e+b+2-e| ∉ X
    rw [show e+b+2-e = b+2 by ring,abs_of_nonneg (by omega)]
    exact hr

private theorem positive_upper_inverse {X : Set ℤ} (hp : ∀ x ∈ X, 2 ≤ x)
    (e : ℤ) {a b : ℤ} (hab : (a, b) ∈ maximalStepTwoRuns {x | |x-e| ∈ X})
    (ha : e + 2 ≤ a) : (a-e,b-e) ∈ maximalStepTwoRuns X := by
  rcases hab with ⟨hab,hpar,hs,hl,hr⟩
  refine ⟨by dsimp; omega,by dsimp; omega,?_,?_,?_⟩
  · intro z hz hzb hzp
    have hm := hs (e+z) (by dsimp at *; omega) (by dsimp at *; omega) (by dsimp at *; omega)
    change |e+z-e| ∈ X at hm
    simpa [abs_of_nonneg (by dsimp at *; omega : 0 ≤ z)] using hm
  · intro hm
    have hz := hp _ hm
    apply hl
    change |a-2-e| ∈ X
    rw [abs_of_nonneg (by dsimp at *; omega)]
    convert hm using 1
    ring
  · intro hm
    have hz := hp _ hm
    apply hr
    change |b+2-e| ∈ X
    rw [abs_of_nonneg (by dsimp at *; omega)]
    convert hm using 1
    ring

private theorem abs_run_reflect (X : Set ℤ) (e : ℤ) {a b : ℤ}
    (hab : (a, b) ∈ maximalStepTwoRuns {x | |x-e| ∈ X}) :
    (2*e-b,2*e-a) ∈ maximalStepTwoRuns {x | |x-e| ∈ X} := by
  rcases hab with ⟨hab,hpar,hs,hl,hr⟩
  have hsym : ∀ z : ℤ, |2*e-z-e| = |z-e| := by
    intro z
    rw [show 2*e-z-e = -(z-e) by ring,abs_neg]
  refine ⟨by dsimp; omega,by dsimp; omega,?_,?_,?_⟩
  · intro z hz hzb hzp
    have hm := hs (2*e-z) (by dsimp at *; omega) (by dsimp at *; omega) (by dsimp at *; omega)
    change |2*e-z-e| ∈ X at hm
    change |z-e| ∈ X
    rwa [hsym] at hm
  · intro hm
    apply hr
    change |b+2-e| ∈ X
    have he' : |2*e-b-2-e| = |b+2-e| := by
      rw [show 2*e-b-2-e = -(b+2-e) by ring,abs_neg]
    change |2*e-b-2-e| ∈ X at hm
    rwa [he'] at hm
  · intro hm
    apply hl
    change |a-2-e| ∈ X
    change |2*e-a+2-e| ∈ X at hm
    rw [show 2*e-a+2-e = -(a-2-e) by ring,abs_neg] at hm
    exact hm

private theorem positive_abs_run_count {X : Set ℤ} (hf : X.Finite)
    (hp : ∀ x ∈ X, 2 ≤ x) (e : ℤ) :
    stepTwoRunCount {x | |x-e| ∈ X} = 2*stepTwoRunCount X := by
  let up : ℤ × ℤ → ℤ × ℤ := fun ab => (e+ab.1,e+ab.2)
  let dn : ℤ × ℤ → ℤ × ℤ := fun ab => (e-ab.2,e-ab.1)
  have he : maximalStepTwoRuns {x | |x-e| ∈ X} =
      up '' maximalStepTwoRuns X ∪ dn '' maximalStepTwoRuns X := by
    ext ab
    rcases ab with ⟨a,b⟩
    constructor
    · intro hab
      have ha := hp _ (run_endpoints_mem hab).1
      have hb := hp _ (run_endpoints_mem hab).2
      have hcases : e+2 ≤ a ∨ b ≤ e-2 := by
        by_contra hn
        push Not at hn
        have hseg := hab.2.2.1
        have hlo := hab.1
        have hpar := hab.2.1
        change 2 ≤ |a-e| at ha
        change 2 ≤ |b-e| at hb
        have hmod : 0 ≤ (e-a)%2 ∧ (e-a)%2 < 2 :=
          ⟨Int.emod_nonneg _ (by omega),Int.emod_lt_of_pos _ (by omega)⟩
        have hm := hseg (e-(e-a)%2) (by simp only [abs_eq_max_neg] at ha hb; omega)
          (by simp only [abs_eq_max_neg] at ha hb; omega) (by omega)
        have ht := hp _ hm
        change 2 ≤ |e-(e-a)%2-e| at ht
        simp only [abs_eq_max_neg] at ht
        omega
      rcases hcases with ha | hb
      · left
        exact ⟨(a-e,b-e),positive_upper_inverse hp e hab ha,by dsimp [up]; ext <;> dsimp <;> ring⟩
      · right
        have href := abs_run_reflect X e hab
        have hs := positive_upper_inverse hp e href (by omega)
        refine ⟨(e-b,e-a),?_,by ext <;> simp only [dn] <;> ring⟩
        have hep : (2*e-b-e,2*e-a-e) = (e-b,e-a) := by
          ext <;> dsimp <;> ring
        change (2*e-b-e,2*e-a-e) ∈ maximalStepTwoRuns X at hs
        rwa [hep] at hs
    · rintro (⟨⟨c,d⟩,h,heq⟩ | ⟨⟨c,d⟩,h,heq⟩)
      · rw [← heq]
        exact positive_upper_run hp e h
      · rw [← heq]
        have hh := abs_run_reflect X e (positive_upper_run hp e h)
        have hep : (2*e-(e+d),2*e-(e+c)) = dn (c,d) := by
          change (2*e-(e+d),2*e-(e+c)) = (e-d,e-c)
          congr 1 <;> ring
        rwa [hep] at hh
  have hd : Disjoint (up '' maximalStepTwoRuns X) (dn '' maximalStepTwoRuns X) := by
    apply Set.disjoint_left.mpr
    rintro ab ⟨⟨a,b⟩,hab,heq⟩ ⟨⟨c,d⟩,hcd,heq'⟩
    have ha := hp a (run_endpoints_mem hab).1
    have hd := hp d (run_endpoints_mem hcd).2
    have hh := congrArg Prod.fst (heq.trans heq'.symm)
    dsimp [up,dn] at hh
    omega
  have hui : Function.Injective up := by
    intro ab cd h
    apply Prod.ext <;> have h₁ := congrArg Prod.fst h <;> have h₂ := congrArg Prod.snd h <;>
      dsimp [up] at * <;> omega
  have hdi : Function.Injective dn := by
    intro ab cd h
    apply Prod.ext <;> have h₁ := congrArg Prod.fst h <;> have h₂ := congrArg Prod.snd h <;>
      dsimp [dn] at * <;> omega
  unfold stepTwoRunCount
  rw [he,Set.ncard_union_eq hd
    ((maximal_runs_finite hf).image _) ((maximal_runs_finite hf).image _),
    Set.ncard_image_of_injective _ hui,Set.ncard_image_of_injective _ hdi]
  omega

private theorem interval_runs (a b : ℤ) (hab : a ≤ b) (hpar : (b - a) % 2 = 0) :
    maximalStepTwoRuns (parityInterval a b) = {(a,b)} := by
  ext cd
  rcases cd with ⟨c,d⟩
  constructor
  · intro h
    have hc := (run_endpoints_mem h).1
    have hd := (run_endpoints_mem h).2
    change a ≤ c ∧ c ≤ b ∧ (c-a)%2=0 at hc
    change a ≤ d ∧ d ≤ b ∧ (d-a)%2=0 at hd
    have hec : c=a := by
      by_contra he
      apply h.2.2.2.1
      exact ⟨by omega,by omega,by omega⟩
    have hed : d=b := by
      by_contra he
      apply h.2.2.2.2
      exact ⟨by omega,by omega,by omega⟩
    simp [hec,hed]
  · intro he
    change (c,d) = (a,b) at he
    obtain ⟨hc,hd⟩ := Prod.mk.inj he
    rw [hc,hd]
    refine ⟨hab,hpar,?_,?_,?_⟩
    · intro z hz hzb hzp
      exact ⟨hz,hzb,hzp⟩
    · intro h
      change a ≤ a-2 ∧ _ at h
      omega
    · intro h
      change _ ∧ b+2 ≤ b ∧ _ at h
      omega

private theorem attaining_base_extensions :
    validExtensions (attainingPrefix 0) = parityInterval 3 11 := by
  have hv : attainingPrefix 0 = [2,3,5,7] := by norm_num [attainingPrefix,u]
  rw [hv]
  ext k
  change isGilbreath [2,3,5,7,k] ↔ 3 ≤ k ∧ k ≤ 11 ∧ (k-3)%2=0
  constructor
  · intro h
    have h4 := h 4 (by omega) (by simp)
    change some (abs (abs (abs (abs (k-7)-2)-0)-1)) = some (1:ℤ) at h4
    have hh := Option.some.inj h4
    simp only [sub_zero,abs_eq_max_neg] at hh
    omega
  · intro h r hr hrl
    simp only [List.length_cons,List.length_nil] at hrl
    interval_cases r <;> norm_num [row,difference]
    simp only [abs_eq_max_neg]
    omega

private theorem attaining_extension_recursion (m : ℕ) (k : ℤ) :
    k ∈ validExtensions (attainingPrefix (m+1)) ↔
      |k-((2:ℤ)^(m+4)-1)|+1 ∈ validExtensions (attainingPrefix m) := by
  rw [extension_recursion _ (by rw [attaining_length]; omega) (attaining_gilbreath _),
    attaining_difference,attaining_last]
  simpa only [sub_eq_add_neg,neg_neg] using
    extensions_shift (attainingPrefix m) (-1) |k-((2:ℤ)^(m+4)-1)|

private theorem attaining_extension_bounds (m : ℕ) :
    ∀ k ∈ validExtensions (attainingPrefix m),
      2*(m:ℤ)+3 ≤ k ∧ k ≤ (2:ℤ)^(m+4)-2*(m:ℤ)-5 := by
  induction m with
  | zero =>
    intro k hk
    rw [attaining_base_extensions] at hk
    change 3 ≤ k ∧ k ≤ 11 ∧ _ at hk
    norm_num
    exact ⟨hk.1,hk.2.1⟩
  | succ m ih =>
    intro k hk
    rw [attaining_extension_recursion] at hk
    have hh := (ih _ hk).2
    have ha : |k-((2:ℤ)^(m+4)-1)| ≤ (2:ℤ)^(m+4)-2*(m:ℤ)-6 := by omega
    have hl := (abs_le.mp ha).1
    have hu := (abs_le.mp ha).2
    simp only [Nat.cast_add,Nat.cast_one]
    rw [show m+1+4=m+4+1 by omega,pow_succ]
    constructor <;> omega

private theorem attaining_run_count (m : ℕ) :
    stepTwoRunCount (validExtensions (attainingPrefix m)) = 2^m := by
  induction m with
  | zero =>
    unfold stepTwoRunCount
    rw [attaining_base_extensions,interval_runs 3 11 (by omega) (by norm_num)]
    simp
  | succ m ih =>
    let X : Set ℤ := {x | x+1 ∈ validExtensions (attainingPrefix m)}
    have hf := (admissible_extension_geometry (attaining_admissible m)).1
    have hX : X.Finite := by
      apply (hf.image (fun y : ℤ => y-1)).subset
      intro x hx
      exact ⟨x+1,hx,by dsimp; ring⟩
    have hp : ∀ x ∈ X, 2 ≤ x := by
      intro x hx
      have h := (attaining_extension_bounds m (x+1) hx).1
      have hm : 0 ≤ (m:ℤ) := Nat.cast_nonneg _
      omega
    have hc : stepTwoRunCount X = stepTwoRunCount (validExtensions (attainingPrefix m)) := by
      simpa only [sub_neg_eq_add] using
        translate_run_count (validExtensions (attainingPrefix m)) (-1)
    have he : validExtensions (attainingPrefix (m+1)) =
        {x | |x-((2:ℤ)^(m+4)-1)| ∈ X} := by
      ext k
      exact attaining_extension_recursion m k
    rw [he,positive_abs_run_count hX hp,hc,ih,pow_succ]
    omega

/-- The whole published component-maximum question, with finite geometry as conclusions. -/
theorem result : componentMaximum := by
  intro n hn
  constructor
  · intro s hs
    refine ⟨admissible_extension_geometry hs, ?_⟩
    have h := universal_component_bound (s := s) (by rw [hs.1]; omega) hs.2.2.2
    simpa only [hs.1] using h
  · let m := n-4
    have hm : m+4=n := Nat.sub_add_cancel (by omega)
    refine ⟨attainingPrefix m,?_,admissible_extension_geometry (attaining_admissible m),?_⟩
    · rw [← hm]
      exact attaining_admissible m
    · exact attaining_run_count m

end D5.S3.Combinatorics.FiniteDifferences.GilbreathExtension

