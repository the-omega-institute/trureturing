/- GID: D5/S3/Arith/FibonacciAtomic/Geometry/AncestorAreaInstability
   generality: I
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/Geometry/AncestorAreaInstability
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Native Fibonacci sources have unbounded intrinsic-depth gaps at vanishing normalized ancestor-area distance. -/

import D5.S3.Arith.FibonacciAtomic.Geometry.AncestorAreaInterval
import D5.S3.Arith.FibonacciAtomic.CliffordLeafOrbit
import D5.S3.Arith.FibonacciAtomic.Geometry.GeometryEntranceRatio
import Mathlib.Order.ConditionallyCompleteLattice.Finset
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S3.Arith.FibonacciAtomic.Geometry.AncestorAreaInstability
open scoped BigOperators
open GenealogicalFiberTransport (Source substitution)
open D5.S3.Combinatorics.Partitions.WordPartitionInverse (wd)
open AncestorAreaInterval (coordinates)

/-- The maximal actual inverse-substitution exponent, rather than address height. -/
def depth (t : Source) : ℕ := sSup {k : ℕ | ∃ p : Source, substitution^[k] p = t}
/-- The prescribed alpha generation ray. -/
def T (n : ℕ) : Source := substitution^[n] (.of true)
/-- The prescribed rotated family, indexed from its three-leaf member. -/
def rotated : ℕ → Source
  | 0 => .mul (.of false) (.mul (.of true) (.of false))
  | k+1 => .mul (rotated k) (T (k+2))
/-- The source U(n), for n at least three. -/
def U (n : ℕ) : Source := rotated (n-3)
/-- The existing ancestor coordinates in their actual inorder positions. -/
def readout (m : ℕ) (t : Source) : Fin (m-1) → ℝ := fun i => (coordinates t)[i.val]?.getD 0
/-- Total-area normalization of the entire vector. -/
def normalized (m : ℕ) (t : Source) : Fin (m-1) → ℝ := fun i => readout m t i / (m.choose 2 : ℝ)
/-- The ordinary Euclidean distance between full finite vectors. -/
def ltwo {m : ℕ} (x y : Fin (m-1) → ℝ) : ℝ := Real.sqrt (∑ i, (x i-y i)^2)
/-- The same midpoint is supplied to both sources and to every estimator. -/
def midpoint (n : ℕ) : Fin ((T n).length-1) → ℝ :=
  fun i => (normalized (T n).length (T n) i + normalized (T n).length (U n) i)/2

set_option maxHeartbeats 1600000 in
/-- The full prescribed native family has a fixed unnormalized area distance,
no uniform depth Lipschitz bound, and the stated midpoint estimation lower bound. -/
theorem result :
    (∀ n : ℕ, 3 ≤ n →
      wd (T n) = wd (U n) ∧ (T n).length = Nat.fib (n+1) ∧
      (U n).length = (T n).length ∧ depth (T n) = n ∧ depth (U n) = 0 ∧
      ltwo (readout (T n).length (T n)) (readout (T n).length (U n)) = Real.sqrt 2 ∧
      ‖readout (T n).length (T n) - readout (T n).length (U n)‖ = 1 ∧
      ‖normalized (T n).length (T n) - normalized (T n).length (U n)‖ =
        1 / ((Nat.fib (n+1)).choose 2 : ℝ)) ∧
    (¬ ∃ L : ℝ, ∀ s t : Source, s.length = t.length →
      |(depth s : ℝ) - (depth t : ℝ)| ≤ L * ltwo (readout s.length s) (readout s.length t)) ∧
    Filter.Tendsto (fun n : ℕ => 1 / ((Nat.fib (n+1)).choose 2 : ℝ))
      Filter.atTop (nhds 0) ∧
    (∀ (n : ℕ), 3 ≤ n → ∀ ε : ℝ,
      1 / (2 * ((Nat.fib (n+1)).choose 2 : ℝ)) ≤ ε →
      ‖midpoint n - normalized (T n).length (T n)‖ ≤ ε ∧
      ‖midpoint n - normalized (T n).length (U n)‖ ≤ ε ∧
      ∀ E : (Fin ((T n).length-1) → ℝ) → ℝ,
        (n : ℝ)/2 ≤ max |E (midpoint n) - (depth (T n) : ℝ)|
          |E (midpoint n) - (depth (U n) : ℝ)|) := by
  classical
  have finiteEntrances (t : Source) :
      Set.Finite {k : ℕ | ∃ p : Source, substitution^[k] p = t} := by
    let g := D5.S3.Combinatorics.Partitions.PaddedWordPartition.G (wd t)
    exact (Set.finite_range (fun e : GeometryEntranceRatio.EntranceFiber g => e.val.2.2)).subset
      (by rintro k ⟨p,hp⟩; exact ⟨⟨(t,p,k),rfl,hp⟩,rfl⟩)
  have maximal (t : Source) : (∃ p : Source, substitution^[depth t] p = t) ∧
      ∀ k : ℕ, (∃ p : Source, substitution^[k] p = t) → k ≤ depth t := by
    have ne : Set.Nonempty {k : ℕ | ∃ p : Source, substitution^[k] p = t} :=
      ⟨0,t,rfl⟩
    exact ⟨ne.csSup_mem (finiteEntrances t), fun k hk => le_csSup (finiteEntrances t).bddAbove hk⟩
  have injective : Function.Injective (substitution : Source → Source) :=
    SourceTransportCentralizer.source_transport_centralizer.2.2.1 substitution
      ⟨substitution.map_mul, fun _ => rfl⟩
  have noAlpha : ∀ p : Source, substitution p ≠ .of true := by
    intro p
    cases p with
    | of b => cases b <;> decide
    | mul l r => intro h; cases h
  have rayDepth (n : ℕ) : depth (T n) = n := by
    apply le_antisymm
    · obtain ⟨p,hp⟩ := (maximal (T n)).1
      by_contra h
      obtain ⟨j,hj⟩ := Nat.exists_eq_add_of_le (by omega : n+1 ≤ depth (T n))
      have he : substitution^[n] (substitution (substitution^[j] p)) = substitution^[n] (.of true) := by
        rw [hj] at hp
        simpa only [T, Nat.add_assoc, Function.iterate_add_apply, Function.iterate_succ_apply', Function.iterate_zero_apply] using hp
      exact noAlpha _ ((injective.iterate n) he)
    · exact (maximal (T n)).2 n ⟨.of true,rfl⟩
  have recurrence (n : ℕ) : T (n+2) = .mul (T (n+1)) (T n) := by
    have h := (SourceTransportCentralizer.source_transport_centralizer.1 (T n)).mpr ⟨n,rfl⟩
    simpa only [T, Function.iterate_succ_apply', Nat.add_assoc] using h
  have compositionLength (s : Source) :
      (GenealogicalFiberTransport.composition s).1 +
        (GenealogicalFiberTransport.composition s).2 = s.length := by
    induction s with
    | of b => cases b <;> rfl
    | mul l r hl hr =>
      simp only [GenealogicalFiberTransport.composition, Prod.fst_add, Prod.snd_add,
        FreeMagma.length]
      omega
  have rayLength (n : ℕ) : (T n).length = Nat.fib (n+1) := by
    cases n with
    | zero => rfl
    | succ n =>
      have packet := GraftAffineClosure.result.2 1 (by decide)
        (GraftAffineClosure.atomicBlock (n+1))
      rcases packet with
        ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, atomic⟩
      have hc := (atomic (n+1) rfl).2.2.2.2.1 (by omega)
      have he : GenealogicalFiberTransport.composition (T (n+1)) =
          (Nat.fib n, Nat.fib (n+1)) := by
        calc
          GenealogicalFiberTransport.composition (T (n+1)) =
              GraftAffineClosure.atomicBlock (n+1) := (CliffordLeafOrbit.result.{0}).1 (n+1)
          _ = (Nat.fib n, Nat.fib (n+1)) := by simpa using hc
      rw [← compositionLength, he]
      exact (Nat.fib_add_two (n := n)).symm
  have coordLength (s : Source) : (coordinates s).length = s.length-1 := by
    induction s with
    | of b => rfl
    | mul l r hl hr =>
      have hp := l.length_pos
      have hq := r.length_pos
      simp only [coordinates, List.length_append, List.length_singleton, hl, hr, FreeMagma.length]
      omega
  have family (k : ℕ) : wd (T (k+3)) = wd (rotated k) ∧
      (rotated k).length = (T (k+3)).length ∧
      (∀ p : Source, substitution p ≠ rotated k) ∧
      ∃ tail : List ℕ, coordinates (T (k+3)) = [1,2] ++ tail ∧
        coordinates (rotated k) = [2,1] ++ tail := by
    induction k with
    | zero =>
      refine ⟨by decide, rfl, ?_, [],rfl,rfl⟩
      intro p
      cases p with
      | of b => cases b <;> decide
      | mul l r =>
        intro h
        have hr : substitution r = .mul (.of true) (.of false) := by
          injection h with _ hr
        cases r with
        | of b => cases b <;> cases hr
        | mul a b =>
          have ha : substitution a = .of true := by injection hr with ha
          exact noAlpha a ha
    | succ k ih =>
      obtain ⟨hw,hl,hp,tail,ht,hu⟩ := ih
      have hlpos := (T (k+3)).length_pos
      refine ⟨?_, ?_, ?_, tail ++ [(T (k+3)).length*(T (k+2)).length] ++ coordinates (T (k+2)), ?_, ?_⟩
      · rw [show k+1+3 = (k+2)+2 by omega, recurrence]
        simpa [rotated,wd,map_mul] using congrArg (fun w => w ++ wd (T (k+2))) hw
      · rw [show k+1+3 = (k+2)+2 by omega, recurrence]
        simp [rotated,FreeMagma.length,hl]
      · intro p he
        cases p with
        | of b =>
          cases b
          · have hh : .of false = rotated k := by injection he with hh
            have hh' := congrArg FreeMagma.length hh
            rw [hl,rayLength] at hh'
            have hf := Nat.fib_mono (show 4 ≤ k+3+1 by omega)
            norm_num at hf hh'
            omega
          · simp [substitution,rotated] at he
        | mul l r =>
          have hh : substitution l = rotated k := by injection he with hh
          exact hp l hh
      · rw [show k+1+3 = (k+2)+2 by omega, recurrence]
        simp [coordinates,ht,List.append_assoc]
      · simp [rotated,coordinates,hu,hl,List.append_assoc]
  have native (n : ℕ) (hn : 3 ≤ n) :
      wd (T n) = wd (U n) ∧ (U n).length = (T n).length ∧
      depth (U n) = 0 ∧ ∃ tail : List ℕ,
        coordinates (T n) = [1,2] ++ tail ∧ coordinates (U n) = [2,1] ++ tail := by
    obtain ⟨hw,hl,hp,tail,ht,hu⟩ := family (n-3)
    have he : n-3+3 = n := by omega
    rw [he] at hw hl ht
    refine ⟨hw,hl,?_,tail,ht,hu⟩
    obtain ⟨p,hp'⟩ := (maximal (U n)).1
    cases hd : depth (U n) with
    | zero => rfl
    | succ j =>
      rw [hd,Function.iterate_succ_apply'] at hp'
      exact False.elim (hp _ hp')
  have completeFamily : ∀ n : ℕ, 3 ≤ n →
      wd (T n) = wd (U n) ∧ (T n).length = Nat.fib (n+1) ∧
      (U n).length = (T n).length ∧ depth (T n) = n ∧ depth (U n) = 0 ∧
      ltwo (readout (T n).length (T n)) (readout (T n).length (U n)) = Real.sqrt 2 ∧
      ‖readout (T n).length (T n) - readout (T n).length (U n)‖ = 1 ∧
      ‖normalized (T n).length (T n) - normalized (T n).length (U n)‖ =
        1 / ((Nat.fib (n+1)).choose 2 : ℝ) := by
    intro n hn
    obtain ⟨hw,hl,hd,tail,ht,hu⟩ := native n hn
    have hp : 3 ≤ (T n).length := by
      have h := congrArg List.length ht
      rw [coordLength] at h
      simp only [List.length_append,List.length_cons,List.length_nil] at h
      omega
    have diff (i : Fin ((T n).length-1)) :
        readout (T n).length (T n) i - readout (T n).length (U n) i =
          if i.val=0 then -1 else if i.val=1 then 1 else 0 := by
      dsimp [readout]
      rw [ht,hu]
      rcases i with ⟨i,hi⟩
      cases i with
      | zero => norm_num
      | succ i => cases i with
        | zero => norm_num
        | succ i => simp
    have sumsq : (∑ i : Fin ((T n).length-1),
        (readout (T n).length (T n) i-readout (T n).length (U n) i)^2) = (2 : ℝ) := by
      simp_rw [diff]
      rw [show (T n).length-1 = 2+((T n).length-3) by omega, Fin.sum_univ_add]
      have hz : ∀ i : Fin ((T n).length-3), (2+i.val ≠ 0 ∧ 2+i.val ≠ 1) := by intro i; omega
      simp [Fin.sum_univ_two, (fun i => (hz i).1), (fun i => (hz i).2)]
      norm_num
    have sup : ‖readout (T n).length (T n) - readout (T n).length (U n)‖ = (1 : ℝ) := by
      apply le_antisymm
      · apply (pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ)≤1)).mpr
        intro i
        change ‖readout _ _ i-readout _ _ i‖ ≤ 1
        rw [diff]
        split_ifs <;> norm_num
      · have h := norm_le_pi_norm (readout (T n).length (T n)-readout (T n).length (U n))
          (⟨0,by omega⟩ : Fin ((T n).length-1))
        simpa [Pi.sub_apply,diff] using h
    refine ⟨hw,rayLength n,hl,rayDepth n,hd,?_,sup,?_⟩
    · exact congrArg Real.sqrt sumsq
    · have he : normalized (T n).length (T n)-normalized (T n).length (U n) =
          ((T n).length.choose 2 : ℝ)⁻¹ • (readout (T n).length (T n)-readout (T n).length (U n)) := by
        ext i; simp [normalized,div_eq_mul_inv]; ring
      rw [he,norm_smul,sup,Real.norm_eq_abs,abs_of_nonneg (by positivity),mul_one,rayLength,one_div]
  refine ⟨completeFamily, ?_, ?_, ?_⟩
  · rintro ⟨L,hL⟩
    obtain ⟨n,hn⟩ := exists_nat_gt (max 3 (L*Real.sqrt 2))
    have hthree : 3 ≤ n := by
      have h := (le_max_left (3:ℝ) (L*Real.sqrt 2)).trans_lt hn
      exact_mod_cast h.le
    obtain ⟨_,_,hl,ht,hu,h₂,_⟩ := completeFamily n hthree
    have h := hL (T n) (U n) hl.symm
    rw [ht,hu,Nat.cast_zero,sub_zero,abs_of_nonneg (Nat.cast_nonneg n),h₂] at h
    exact (not_lt_of_ge h) ((le_max_right (3:ℝ) (L*Real.sqrt 2)).trans_lt hn)
  · simp only [one_div]
    apply tendsto_inv_atTop_zero.comp
    apply tendsto_natCast_atTop_atTop.comp
    apply Filter.tendsto_atTop_atTop.mpr
    intro K
    refine ⟨max 4 (2*K+1),fun n hn => ?_⟩
    have hf : n+1 ≤ Nat.fib (n+1) := Nat.le_fib_self (by omega)
    have hc : K ≤ (n+1).choose 2 := by
      rw [Nat.choose_two_right]
      apply (Nat.le_div_iff_mul_le (by decide : 0 < 2)).mpr
      have he : n+1-1 = n := by omega
      rw [he]
      have hnK : 2*K+1 ≤ n := (le_max_right _ _).trans hn
      nlinarith
    exact hc.trans (Nat.choose_le_choose 2 hf)
  · intro n hn ε hε
    obtain ⟨_,hlen,hl,ht,hu,_,_,hsup⟩ := completeFamily n hn
    have hpos : 0 < ((T n).length.choose 2 : ℝ) := by
      apply Nat.cast_pos.mpr
      apply Nat.choose_pos
      rw [hlen]
      have hf := Nat.fib_mono (show 4 ≤ n+1 by omega)
      norm_num at hf
      omega
    have hmT : midpoint n-normalized (T n).length (T n) =
        (-(1/2:ℝ)) • (normalized (T n).length (T n)-normalized (T n).length (U n)) := by
      ext i; simp [midpoint]; ring
    have hmU : midpoint n-normalized (T n).length (U n) =
        (1/2:ℝ) • (normalized (T n).length (T n)-normalized (T n).length (U n)) := by
      ext i; simp [midpoint]; ring
    refine ⟨?_,?_,?_⟩
    · rw [hmT,norm_smul,hsup]
      norm_num
      convert hε using 1 <;> ring
    · rw [hmU,norm_smul,hsup]
      norm_num
      convert hε using 1 <;> ring
    · intro E
      rw [ht,hu,Nat.cast_zero,sub_zero]
      have h := abs_sub_le (n:ℝ) (E (midpoint n)) 0
      rw [sub_zero,abs_of_nonneg (Nat.cast_nonneg n),abs_sub_comm,sub_zero] at h
      have h₁ := le_max_left |E (midpoint n)-(n:ℝ)| |E (midpoint n)|
      have h₂ := le_max_right |E (midpoint n)-(n:ℝ)| |E (midpoint n)|
      linarith

end D5.S3.Arith.FibonacciAtomic.Geometry.AncestorAreaInstability

#print axioms D5.S3.Arith.FibonacciAtomic.Geometry.AncestorAreaInstability.result
