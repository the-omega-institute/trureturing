/- GID: D5/S1/Words/EndpointShuffleSupport
   generality: I
   mirror-B: D5/B/S1/Words/EndpointShuffleSupport
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact distinct support of ordinary endpoint-word self-shuffles. -/

import D5.S1.Words.UnaryGapWords
import D5.S1.Words.Complexity.ExactDecks.UpperBound.OverlapInfiltration

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Words.EndpointShuffleSupport

open D5.S1.Words.UnaryGapWords
open D5.S1.Words.Complexity.ExactDecks.UpperBound.OverlapInfiltration

/-- Two endpoint ones separated by an arbitrary number of zeros. -/
def endpointWord (m : Nat) : List Bool :=
  [true] ++ List.replicate m false ++ [true]

/-- The two outer zero gaps determine the middle gap. -/
def endpointOutput (m a c : Nat) : List Bool :=
  gap false [true, true, true, true] [0, a, (m - a) + (m - c), c, 0]

/-- A set of output words, with equal words counted only once. -/
def endpointFamily (m : Nat) : Finset (List Bool) :=
  Finset.univ.image (fun p : Fin (m + 1) × Fin (m + 1) =>
    endpointOutput m p.1.val p.2.val)

private theorem prefix_left {α : Type*} (p u v z : List α)
    (hz : z ∈ ordinaryShuffles u v) :
    p ++ z ∈ ordinaryShuffles (p ++ u) v := by
  induction p with
  | nil => simpa using hz
  | cons x p ih =>
      cases v with
      | nil =>
          have hzu : z = u := by
            cases u <;> simpa [ordinaryShuffles] using hz
          subst z
          simp [ordinaryShuffles]
      | cons y v =>
          simp only [List.cons_append, ordinaryShuffles, List.mem_append, List.mem_map]
          exact Or.inl ⟨p ++ z, ih, rfl⟩

private theorem prefix_right {α : Type*} (p u v z : List α)
    (hz : z ∈ ordinaryShuffles u v) :
    p ++ z ∈ ordinaryShuffles u (p ++ v) := by
  induction p with
  | nil => simpa using hz
  | cons y p ih =>
      cases u with
      | nil =>
          have hzv : z = v := by simpa [ordinaryShuffles] using hz
          subst z
          simp [ordinaryShuffles]
      | cons x u =>
          simp only [List.cons_append, ordinaryShuffles, List.mem_append, List.mem_map]
          exact Or.inr ⟨p ++ z, ih, rfl⟩

/-- Every bounded pair of outer gaps is realized by an actual ordinary shuffle. -/
theorem endpointOutput_mem (m a c : Nat) (ha : a ≤ m) (hc : c ≤ m) :
    endpointOutput m a c ∈ ordinaryShuffles (endpointWord m) (endpointWord m) := by
  let za := List.replicate a false
  let zr := List.replicate (m - a) false
  let zs := List.replicate (m - c) false
  let zc := List.replicate c false
  have h0 : zc ++ [true] ∈ ordinaryShuffles [] (zc ++ [true]) := by
    simp [ordinaryShuffles]
  have h1 := prefix_left [true] [] (zc ++ [true]) (zc ++ [true]) h0
  have h2 := prefix_right zs ([true] ++ []) (zc ++ [true])
    ([true] ++ (zc ++ [true])) h1
  have h3 := prefix_left zr ([true] ++ []) (zs ++ (zc ++ [true]))
    (zs ++ ([true] ++ (zc ++ [true]))) h2
  have h4 := prefix_right [true] (zr ++ ([true] ++ []))
    (zs ++ (zc ++ [true]))
    (zr ++ (zs ++ ([true] ++ (zc ++ [true])))) h3
  have h5 := prefix_left ([true] ++ za) (zr ++ ([true] ++ []))
    ([true] ++ (zs ++ (zc ++ [true])))
    ([true] ++ (zr ++ (zs ++ ([true] ++ (zc ++ [true]))))) h4
  have hab : a + (m - a) = m := by omega
  have hcd : (m - c) + c = m := by omega
  have hmerge (r s : Nat) (t : List Bool) :
      List.replicate r false ++ (List.replicate s false ++ t) =
        List.replicate (r + s) false ++ t := by
    rw [← List.append_assoc, ← List.replicate_add]
  simpa only [za, zr, zs, zc, endpointWord, endpointOutput, gap,
    List.headD_cons, List.tail_cons, List.replicate_zero, List.nil_append,
    List.append_nil, List.singleton_append, List.cons_append, List.append_assoc,
    hmerge, hab, hcd] using h5

private theorem endpointOutput_injective (m : Nat) :
    Function.Injective (fun p : Fin (m + 1) × Fin (m + 1) =>
      endpointOutput m p.1.val p.2.val) := by
  intro p q hpq
  have hg := (gap_injective false [true, true, true, true] [true, true, true, true]
    [0, p.1.val, (m - p.1.val) + (m - p.2.val), p.2.val, 0]
    [0, q.1.val, (m - q.1.val) + (m - q.2.val), q.2.val, 0]
    (by simp) (by simp) (by simp) (by simp) hpq).2
  have ha : p.1.val = q.1.val := by
    simpa using congrArg (fun l : List Nat => l.tail.headD 0) hg
  have hc : p.2.val = q.2.val := by
    simpa using congrArg (fun l : List Nat => l.tail.tail.tail.headD 0) hg
  exact Prod.ext (Fin.ext ha) (Fin.ext hc)

/-- The parameter rectangle counts distinct words, independently of schedules. -/
theorem endpointFamily_card (m : Nat) : (endpointFamily m).card = (m + 1) ^ 2 := by
  rw [endpointFamily, Finset.card_image_of_injective _ (endpointOutput_injective m)]
  simp [pow_two]

/-- An unbounded lower bound on distinct ordinary self-shuffle words. -/
theorem endpoint_self_shuffle_card_lower (m : Nat) :
    (m + 1) ^ 2 ≤
      ((ordinaryShuffles (endpointWord m) (endpointWord m)).toFinset).card := by
  rw [← endpointFamily_card m]
  apply Finset.card_le_card
  intro w hw
  obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hw
  exact List.mem_toFinset.mpr
    (endpointOutput_mem m p.1.val p.2.val (by omega) (by omega))


private theorem mem_swap {α : Type*} (u v w : List α)
    (h : w ∈ ordinaryShuffles u v) : w ∈ ordinaryShuffles v u := by
  cases u with
  | nil => cases v <;> simpa [ordinaryShuffles] using h
  | cons a u =>
    cases v with
    | nil => simpa [ordinaryShuffles] using h
    | cons b v =>
      simp only [ordinaryShuffles, List.mem_append, List.mem_map] at h ⊢
      rcases h with ⟨z, hz, rfl⟩ | ⟨z, hz, rfl⟩
      · exact Or.inr ⟨z, mem_swap u (b :: v) z hz, rfl⟩
      · exact Or.inl ⟨z, mem_swap (a :: u) v z hz, rfl⟩
termination_by u.length + v.length

private def zeroTail (r : Nat) : List Bool := List.replicate r false ++ [true]

private theorem tail_support (r s : Nat) (w : List Bool)
    (h : w ∈ ordinaryShuffles (zeroTail r) (zeroTail s)) :
    ∃ b c, b + c = r + s ∧ c ≤ max r s ∧
      w = List.replicate b false ++ true :: (List.replicate c false ++ [true]) := by
  cases r with
  | zero =>
    cases s with
    | zero =>
      have hw : w = [true, true] := by simpa [zeroTail, ordinaryShuffles] using h
      subst w
      exact ⟨0, 0, rfl, by omega, rfl⟩
    | succ s =>
      simp only [zeroTail, List.replicate_zero, List.nil_append,
        List.replicate_succ, List.cons_append, ordinaryShuffles,
        List.mem_append, List.mem_map] at h
      rcases h with ⟨z, hz, rfl⟩ | ⟨z, hz, rfl⟩
      · have hz' : z = false :: zeroTail s := by simpa [ordinaryShuffles, zeroTail] using hz
        subst z
        exact ⟨0, s+1, by omega, by omega, by simp [zeroTail, List.replicate_succ]⟩
      · obtain ⟨b,c,hbc,hc,rfl⟩ := tail_support 0 s z hz
        exact ⟨b+1,c,by omega,by omega,by simp [List.replicate_succ]⟩
  | succ r =>
    cases s with
    | zero =>
      obtain ⟨b,c,hbc,hc,hw⟩ := tail_support 0 (r+1) w
        (mem_swap _ _ _ h)
      exact ⟨b,c,by omega,by simpa [max_comm] using hc,hw⟩
    | succ s =>
      simp only [zeroTail, List.replicate_succ, List.cons_append,
        ordinaryShuffles, List.mem_append, List.mem_map] at h
      rcases h with ⟨z, hz, rfl⟩ | ⟨z, hz, rfl⟩
      · obtain ⟨b,c,hbc,hc,rfl⟩ := tail_support r (s+1) z hz
        refine ⟨b+1,c,by omega,?_,by simp [List.replicate_succ]⟩
        omega
      · obtain ⟨b,c,hbc,hc,rfl⟩ := tail_support (r+1) s z hz
        refine ⟨b+1,c,by omega,?_,by simp [List.replicate_succ]⟩
        omega
termination_by (r + s, r)
decreasing_by all_goals omega

private theorem mixed_support (r m : Nat) (hr : r ≤ m) (w : List Bool)
    (h : w ∈ ordinaryShuffles (zeroTail r) (endpointWord m)) :
    ∃ a b c, a ≤ r ∧ c ≤ m ∧ a + b + c = r + m ∧
      w = List.replicate a false ++ true ::
        (List.replicate b false ++ true :: (List.replicate c false ++ [true])) := by
  cases r with
  | zero =>
    simp only [zeroTail, List.replicate_zero, List.nil_append,
      endpointWord, List.singleton_append, List.cons_append, ordinaryShuffles,
      List.mem_append, List.mem_map] at h
    rcases h with ⟨z,hz,rfl⟩ | ⟨z,hz,rfl⟩
    · have hz' : z = endpointWord m := by simpa [ordinaryShuffles, endpointWord] using hz
      subst z
      exact ⟨0,0,m,by omega,by omega,by omega,by simp [endpointWord]⟩
    · obtain ⟨b,c,hbc,hc,rfl⟩ := tail_support 0 m z hz
      exact ⟨0,b,c,by omega,by simpa using hc,by omega,by simp⟩
  | succ r =>
    simp only [zeroTail, List.replicate_succ, List.cons_append,
      endpointWord, List.singleton_append, List.cons_append, ordinaryShuffles,
      List.mem_append, List.mem_map] at h
    rcases h with ⟨z,hz,rfl⟩ | ⟨z,hz,rfl⟩
    · obtain ⟨a,b,c,ha,hc,habc,rfl⟩ := mixed_support r m (by omega) z hz
      exact ⟨a+1,b,c,by omega,hc,by omega,by simp [List.replicate_succ]⟩
    · obtain ⟨b,c,hbc,hc,rfl⟩ := tail_support (r+1) m z hz
      exact ⟨0,b,c,by omega,by simpa [max_eq_right hr] using hc,by omega,by simp⟩
termination_by r

/-- Every ordinary self-shuffle is determined by two bounded outer gaps. -/
theorem endpoint_support_exhaustion (m : Nat) (w : List Bool)
    (h : w ∈ ordinaryShuffles (endpointWord m) (endpointWord m)) :
    ∃ a ≤ m, ∃ c ≤ m, w = endpointOutput m a c := by
  simp only [endpointWord, List.singleton_append, List.cons_append, ordinaryShuffles,
    List.mem_append, List.mem_map] at h
  have finish (z : List Bool) (hz : z ∈ ordinaryShuffles (zeroTail m) (endpointWord m)) :
      ∃ a ≤ m, ∃ c ≤ m, true :: z = endpointOutput m a c := by
    obtain ⟨a,b,c,ha,hc,habc,rfl⟩ := mixed_support m m (by omega) z hz
    have hb : b = (m-a)+(m-c) := by omega
    exact ⟨a,ha,c,hc,by simp [endpointOutput,gap,hb]⟩
  rcases h with ⟨z,hz,rfl⟩ | ⟨z,hz,rfl⟩
  · exact finish z hz
  · exact finish z (mem_swap _ _ _ hz)

/-- Equality holds for support sets, so multiplicities of schedules disappear. -/
theorem endpoint_support_eq (m : Nat) :
    (ordinaryShuffles (endpointWord m) (endpointWord m)).toFinset = endpointFamily m := by
  apply Finset.Subset.antisymm
  · intro w hw
    obtain ⟨a,ha,c,hc,rfl⟩ := endpoint_support_exhaustion m w (List.mem_toFinset.mp hw)
    exact Finset.mem_image.mpr ⟨(⟨a,by omega⟩,⟨c,by omega⟩),Finset.mem_univ _,rfl⟩
  · intro w hw
    obtain ⟨p,_,rfl⟩ := Finset.mem_image.mp hw
    exact List.mem_toFinset.mpr (endpointOutput_mem m p.1.val p.2.val (by omega) (by omega))

/-- Exact cardinality for every zero-run length, including zero. -/
theorem endpoint_self_shuffle_card (m : Nat) :
    ((ordinaryShuffles (endpointWord m) (endpointWord m)).toFinset).card = (m+1)^2 := by
  apply Nat.le_antisymm
  · rw [endpoint_support_eq, endpointFamily_card]
  · exact endpoint_self_shuffle_card_lower m

/-- Ordinary binary numerals, most significant digit first, with no leading zeros. -/
def binaryWord (n : Nat) : List Bool := (Nat.digits 2 n).reverse.map (fun d => d == 1)

/-- The sequence counts distinct words, irrespective of the producing schedule. -/
def distinctSelfShuffleCount (n : Nat) : Nat :=
  ((ordinaryShuffles (binaryWord n) (binaryWord n)).toFinset).card

/-- The ordinary binary numeral of 2^k+1 has exactly k-1 interior zeros. -/
theorem binaryWord_pow_add_one (k : Nat) (hk : 1 ≤ k) :
    binaryWord (2^k+1) = endpointWord (k-1) := by
  have hd := Nat.digits_append_zeroes_append_digits (b := 2) (k := k-1)
    (m := 1) (n := 1) (by decide) (by decide)
  have hk' : 1 + (k-1) = k := by omega
  have hd' : Nat.digits 2 (2^k+1) = [1] ++ List.replicate (k-1) 0 ++ [1] := by
    simpa [Nat.digits_one, hk', Nat.add_comm] using hd.symm
  unfold binaryWord
  rw [hd']
  simp [endpointWord,List.reverse_append,List.reverse_replicate]

/-- The published eventual identity, with the explicit valid threshold one. -/
theorem result : ∃ K : Nat, 1 ≤ K ∧ ∀ k : Nat, K ≤ k →
    distinctSelfShuffleCount (2^k+1) = k^2 := by
  refine ⟨1,by omega,?_⟩
  intro k hk
  unfold distinctSelfShuffleCount
  rw [binaryWord_pow_add_one k hk,endpoint_self_shuffle_card]
  congr 1
  omega

end D5.S1.Words.EndpointShuffleSupport
