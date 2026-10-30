/- GID: D5/S1/Words/DoubleTailShuffleSupport
   generality: I
   mirror-B: D5/B/S1/Words/DoubleTailShuffleSupport
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Distinct self-shuffles of a unary prefix with two final zeros have triangular support. -/

import D5.S1.Words.EndpointShuffleSupport
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

open D5.S1.Words.UnaryGapWords
open D5.S1.Words.Complexity.ExactDecks.UpperBound.OverlapInfiltration
open scoped BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S1.Words.DoubleTailShuffleSupport
open D5.S1.Words.EndpointShuffleSupport

def root (m : Nat) : List Bool := List.replicate m true ++ [false, false]
private def parameters (m : Nat) : Finset (Sigma (fun _ : Nat => Nat)) :=
  (Finset.range (m+1)).sigma (fun i => Finset.range (i+1))
private def output (m : Nat) (p : Sigma (fun _ : Nat => Nat)) : List Bool :=
  gap true [false,false,false,false] [m+(m-p.1),p.2,p.1-p.2,0,0]
private def family (m : Nat) : Finset (List Bool) := (parameters m).image (output m)

private theorem output_injective_on (m : Nat) : Set.InjOn (output m) (parameters m) := by
  intro p hp q hq he
  have hp' : p.1 < m+1 ∧ p.2 < p.1+1 := by simpa [parameters] using hp
  have hq' : q.1 < m+1 ∧ q.2 < q.1+1 := by simpa [parameters] using hq
  have hg := (gap_injective true [false,false,false,false] [false,false,false,false]
    [m+(m-p.1),p.2,p.1-p.2,0,0] [m+(m-q.1),q.2,q.1-q.2,0,0]
    (by simp) (by simp) (by simp) (by simp) he).2
  have ha := congrArg (fun l : List Nat => l.headD 0) hg
  have hb := congrArg (fun l : List Nat => l.tail.headD 0) hg
  simp only [List.headD_cons, List.tail_cons] at ha hb
  have hi : p.1 = q.1 := by omega
  exact Sigma.ext hi (by simpa using hb)

private theorem family_card (m : Nat) : (family m).card = (m+2)*(m+1)/2 := by
  rw [family, Finset.card_image_iff.mpr (output_injective_on m)]
  simp only [parameters, Finset.card_sigma, Finset.card_range]
  have hs : (∑ i ∈ Finset.range (m+1), (i+1)) = ∑ i ∈ Finset.range (m+2), i := by
    simpa using (Finset.sum_range_succ' (fun i : Nat => i) (m+1)).symm
  rw [hs, Finset.sum_range_id]
  simp

private theorem ones_value (m : Nat) : Nat.ofDigits 2 (List.replicate m 1) + 1 = 2^m := by
  induction m with
  | zero => simp
  | succ m ih =>
    simp only [List.replicate_succ, Nat.ofDigits, pow_succ]
    omega

private theorem digits_ones (m : Nat) (hm : 1 ≤ m) :
    Nat.digits 2 (2^m-1) = List.replicate m 1 := by
  have hv : Nat.ofDigits 2 (List.replicate m 1) = 2^m-1 := by
    have := ones_value m
    omega
  rw [← hv]
  apply Nat.digits_ofDigits 2 (by decide)
  · intro d hd
    have : d = 1 := (List.mem_replicate.mp hd).2
    omega
  · intro hn
    obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
    simp

private theorem binary_root (m : Nat) (hm : 1 ≤ m) :
    binaryWord (2^(m+2)-4) = root m := by
  have hp : 1 < 2^m := Nat.one_lt_pow (by omega : m ≠ 0) (by decide)
  have hn : 2^(m+2)-4 = 2^2 * (2^m-1) := by
    rw [pow_add, Nat.mul_sub_left_distrib]
    norm_num
    omega
  unfold binaryWord
  rw [hn, Nat.digits_base_pow_mul (by decide) (by omega), digits_ones m hm]
  simp [root, List.reverse_replicate]

theorem binary_root_original (k : Nat) (hk : 3 ≤ k) :
    binaryWord (2^k-4) = root (k-2) := by
  have := binary_root (k-2) (by omega)
  simpa only [show k-2+2 = k by omega] using this


private theorem single_zero_support (s : Nat) (w : List Bool)
    (h : w ∈ ordinaryShuffles [false] (root s)) :
    ∃ a b, a + b = s ∧
      w = List.replicate a true ++ false :: (List.replicate b true ++ [false,false]) := by
  induction s generalizing w with
  | zero =>
      have hw : w = [false,false,false] := by simpa [root,ordinaryShuffles] using h
      exact ⟨0,0,rfl,by simpa using hw⟩
  | succ s ih =>
      simp only [root,List.replicate_succ,List.cons_append,ordinaryShuffles,
        List.mem_append,List.mem_map] at h
      rcases h with ⟨z,hz,rfl⟩ | ⟨z,hz,rfl⟩
      · have hz' : z = true :: root s := by simpa [ordinaryShuffles,root] using hz
        subst z
        exact ⟨0,s+1,by omega,by simp [root,List.replicate_succ]⟩
      · obtain ⟨a,b,hab,rfl⟩ := ih z hz
        exact ⟨a+1,b,by omega,by simp [List.replicate_succ]⟩

private theorem double_zero_support (s : Nat) (w : List Bool)
    (h : w ∈ ordinaryShuffles [false,false] (root s)) :
    ∃ a b c, a + b + c = s ∧
      w = List.replicate a true ++ false ::
        (List.replicate b true ++ false :: (List.replicate c true ++ [false,false])) := by
  induction s generalizing w with
  | zero =>
      have hw : w = [false,false,false,false] := by simpa [root,ordinaryShuffles] using h
      exact ⟨0,0,0,rfl,by simpa using hw⟩
  | succ s ih =>
      change w ∈ ordinaryShuffles (false :: [false]) (true :: root s) at h
      rw [ordinaryShuffles,List.mem_append] at h
      simp only [List.mem_map] at h
      rcases h with ⟨z,hz,rfl⟩ | ⟨z,hz,rfl⟩
      · obtain ⟨a,b,hab,rfl⟩ := single_zero_support (s+1) z hz
        exact ⟨0,a,b,by omega,by simp⟩
      · obtain ⟨a,b,c,habc,rfl⟩ := ih z hz
        exact ⟨a+1,b,c,by omega,by simp [List.replicate_succ]⟩

private theorem root_support (r s : Nat) (w : List Bool)
    (h : w ∈ ordinaryShuffles (root r) (root s)) :
    ∃ a b c, min r s ≤ a ∧ a + b + c = r + s ∧
      w = List.replicate a true ++ false ::
        (List.replicate b true ++ false :: (List.replicate c true ++ [false,false])) := by
  cases r with
  | zero =>
      obtain ⟨a,b,c,habc,hw⟩ := double_zero_support s w h
      exact ⟨a,b,c,by simp,by simpa using habc,hw⟩
  | succ r =>
      cases s with
      | zero =>
          obtain ⟨a,b,c,habc,hw⟩ := double_zero_support (r+1) w (mem_swap _ _ _ h)
          exact ⟨a,b,c,by simp,by simpa using habc,hw⟩
      | succ s =>
          simp only [root,List.replicate_succ,List.cons_append,ordinaryShuffles,
            List.mem_append,List.mem_map] at h
          rcases h with ⟨z,hz,rfl⟩ | ⟨z,hz,rfl⟩
          · obtain ⟨a,b,c,ha,habc,rfl⟩ := root_support r (s+1) z hz
            exact ⟨a+1,b,c,by omega,by omega,by simp [List.replicate_succ]⟩
          · obtain ⟨a,b,c,ha,habc,rfl⟩ := root_support (r+1) s z hz
            exact ⟨a+1,b,c,by omega,by omega,by simp [List.replicate_succ]⟩
termination_by r+s

private theorem output_mem (m i j : Nat) (hi : i ≤ m) (hj : j ≤ i) :
    output m ⟨i,j⟩ ∈ ordinaryShuffles (root m) (root m) := by
  let x := List.replicate (i-j) true ++ [false,false]
  have h0 : x ∈ ordinaryShuffles [] x := by simp [ordinaryShuffles]
  have h1 := prefix_left [false] [] x x h0
  have h2 := prefix_right (List.replicate j true) [false] x ([false] ++ x) h1
  have h3 := prefix_left [false] [false] (List.replicate j true ++ x)
    (List.replicate j true ++ ([false] ++ x)) h2
  have h4 := prefix_right (List.replicate (m-i) true) [false,false]
    (List.replicate j true ++ x)
    ([false] ++ (List.replicate j true ++ ([false] ++ x))) h3
  have h5 := prefix_left (List.replicate m true) [false,false]
    (List.replicate (m-i) true ++ (List.replicate j true ++ x))
    (List.replicate (m-i) true ++ ([false] ++
      (List.replicate j true ++ ([false] ++ x)))) h4
  have hsum : m-i+(j+(i-j)) = m := by omega
  have merge (r s : Nat) (t : List Bool) :
      List.replicate r true ++ (List.replicate s true ++ t) =
        List.replicate (r+s) true ++ t := by
    rw [← List.append_assoc, ← List.replicate_add]
  simpa only [x,root,output,gap,List.headD_cons,List.tail_cons,List.replicate_zero,
    List.nil_append,List.append_nil,List.singleton_append,List.cons_append,
    List.append_assoc,merge,hsum] using h5

private theorem support_exhaustion (m : Nat) (w : List Bool)
    (h : w ∈ ordinaryShuffles (root m) (root m)) :
    ∃ i ≤ m, ∃ j ≤ i, w = output m ⟨i,j⟩ := by
  obtain ⟨a,b,c,ha,habc,rfl⟩ := root_support m m w h
  simp only [min_self] at ha
  refine ⟨b+c,by omega,b,by omega,?_⟩
  have hfirst : m+(m-(b+c)) = a := by omega
  have hlast : b+c-b = c := by omega
  simp [output,gap,hfirst,hlast]

private theorem support_eq (m : Nat) :
    (ordinaryShuffles (root m) (root m)).toFinset = family m := by
  apply Finset.Subset.antisymm
  · intro w hw
    obtain ⟨i,hi,j,hj,rfl⟩ := support_exhaustion m w (List.mem_toFinset.mp hw)
    apply Finset.mem_image.mpr
    exact ⟨⟨i,j⟩,by simp [parameters]; omega,rfl⟩
  · intro w hw
    obtain ⟨⟨i,j⟩,hp,rfl⟩ := Finset.mem_image.mp hw
    have hp' : i < m+1 ∧ j < i+1 := by simpa [parameters] using hp
    exact List.mem_toFinset.mpr (output_mem m i j (by omega) (by omega))

theorem self_shuffle_card (m : Nat) :
    ((ordinaryShuffles (root m) (root m)).toFinset).card = (m+2)*(m+1)/2 := by
  rw [support_eq,family_card]

theorem result : ∃ K : Nat, 3 ≤ K ∧ ∀ k : Nat, K ≤ k →
    distinctSelfShuffleCount (2^k-4) = k*(k-1)/2 := by
  refine ⟨3,by omega,?_⟩
  intro k hk
  unfold distinctSelfShuffleCount
  rw [binary_root_original k hk,self_shuffle_card]
  rw [show k-2+2 = k by omega, show k-2+1 = k-1 by omega]

end D5.S1.Words.DoubleTailShuffleSupport
