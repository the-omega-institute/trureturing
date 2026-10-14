/- GID: D5/S3/Arith/FibonacciAtomic/Observer/NativeSuppliedWidth
   generality: I
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/Observer/NativeSuppliedWidth
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Attained complete-word widths of the full fixed-skeleton native comparison classes. -/

import D5.S3.Arith.FibonacciAtomic.Observer.NativeSuppliedComparison
import D5.S3.Axis.AxisConvergence
import Mathlib.Analysis.SpecialFunctions.Log.Base

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.Observer.NativeSuppliedWidth

open GenealogicalFiberTransport (Source substitution)
open ActualTreeReadoutAcquisition (Address Reply readout)
open NativeActiveParityExecution (chartOf source labels)
open CombLiteralInstallationBounds (Controller Run)
open NativeSuppliedComparison (Correct Static)
open D5.S1.Words.AdmissibleWords.AdmissibleCount (Adm)

/-- Every installed state is encoded, including states without promised support.
Internal rows are unrestricted source-blind deterministic work. Primitive rows
immediately hold or change one bit on each of the four raw replies. -/
structure Installation (width : Nat) where
  State : Type
  finite : Fintype State
  machine : Controller State
  encode : State → Fin width → Bool
  positive : 0 < width
  injective : Function.Injective encode
  admissible : ∀ c, Adm width (encode c)
  readLegal : ∀ c p k, machine.instruction c = .read p k →
    ∀ y, hammingDist (encode c) (encode (k y)) ≤ 1
  updateLegal : ∀ c v, machine.instruction c = .applyRho v →
    hammingDist (encode c) (encode v) ≤ 1

attribute [instance] Installation.finite

/-- Feasibility quantifies the entire installation, without a runtime bound. -/
def Feasible (S : Source) (T width : Nat) : Prop :=
  ∃ I : Installation width, Correct I.machine S T

def StaticFeasible (S : Source) (T width : Nat) : Prop :=
  ∃ I : Installation width, Correct I.machine S T ∧ Static I.machine S T

/-- The existing dimension is exactly inverse capacity for n positive words. -/
noncomputable def capacity (n : Nat) : Nat := NativeFibonacciActiveTable.dimension (n-1)

private theorem dimension_spec (h : Nat) :
    h+1 ≤ Nat.fib (NativeFibonacciActiveTable.dimension h+2) ∧
    (∀ d, d < NativeFibonacciActiveTable.dimension h → Nat.fib (d+2) < h+1) :=
  ⟨(NativeFibonacciActiveTable.native_fibonacci_active_table h (fun _ => []) 0).1,
    (NativeFibonacciActiveTable.native_fibonacci_active_table h (fun _ => []) 0).2.1⟩

private theorem capacity_le {n d : Nat} (positive : 0 < n)
    (bound : n ≤ Nat.fib (d+2)) : capacity n ≤ d := by
  by_contra h
  have small := (dimension_spec (n-1)).2 d (by change d < capacity n; omega)
  omega

private theorem capacity_mono {m n : Nat} (positive : 0 < m) (le : m ≤ n) :
    capacity m ≤ capacity n := by
  apply capacity_le positive
  have cap := (dimension_spec (n-1)).1
  change m ≤ Nat.fib (NativeFibonacciActiveTable.dimension (n-1)+2)
  omega

private theorem capacity_double (n : Nat) (positive : 0 < n) :
    capacity (2*n) ≤ capacity n+2 := by
  apply capacity_le (by omega)
  have cap := (dimension_spec (n-1)).1
  have recurrence : Nat.fib (capacity n+2+2) =
      Nat.fib (capacity n+2)+Nat.fib (capacity n+2+1) := Nat.fib_add_two
  have mono : Nat.fib (capacity n+2) ≤ Nat.fib (capacity n+2+1) := Nat.fib_le_fib_succ
  change n-1+1 ≤ Nat.fib (capacity n+2) at cap
  omega

/-- The operational bridge uses the original Run rather than another interpreter.
Native epochs annotate chronology and are not supplied to the machine. -/
private theorem to_native {E : Type} {M : Controller E} {u : Source}
    {e f : E} {t : Nat} {qs : List (E × Nat)} {updates : Nat} {b : Bool}
    (run : Run M u e t qs updates f b) (epoch : Nat) :
    ∃ trace, NativeSerialMachine.Run M.instruction e epoch (substitution^[t] u) trace b := by
  induction run generalizing epoch with
  | halt row => exact ⟨[],.stop row⟩
  | @read e f t p k qs updates b row tail ih =>
      obtain ⟨trace,r⟩ := ih epoch
      exact ⟨_,.read row rfl r⟩
  | @update e k f t qs updates b row tail ih =>
      obtain ⟨trace,r⟩ := ih (epoch+1)
      rw [Function.iterate_succ_apply'] at r
      exact ⟨_,.update row r⟩
  | internal row tail ih =>
      obtain ⟨trace,r⟩ := ih epoch
      exact ⟨_,.localStep row r⟩

private theorem from_native {E : Type} (M : Controller E) {c : E} {epoch : Nat}
    {r : Source} {trace : NativeSerialMachine.Trace} {b : Bool}
    (run : NativeSerialMachine.Run M.instruction c epoch r trace b)
    (u : Source) (t : Nat) (cert : r = substitution^[t] u) :
    ∃ qs updates f, Run M u c t qs updates f b := by
  induction run generalizing t with
  | stop row => exact ⟨[],0,_,.halt row⟩
  | localStep row run ih =>
      obtain ⟨qs,updates,f,r⟩ := ih t cert
      exact ⟨qs,updates,f,.internal row r⟩
  | update row run ih =>
      obtain ⟨qs,updates,f,r⟩ := ih (t+1) (by rw [cert,Function.iterate_succ_apply'])
      exact ⟨qs,updates+1,f,.update row r⟩
  | @read c epoch r p k y trace b row reply run ih =>
      obtain ⟨qs,updates,f,r'⟩ := ih t cert
      have eq : readout p (substitution^[t] u) = y := by rw [← cert]; exact reply
      exact ⟨(c,t)::qs,updates,f,.read row (by simpa [eq] using r')⟩

private theorem correct_of_native {E : Type} (M : Controller E) (S : Source) (T : Nat)
    (exec : ∀ (x : Fin S.length → Bool) (t : Nat), t ≤ T →
      ∃ trace, NativeSerialMachine.Run M.instruction M.initial 0
        (substitution^[t] (source (chartOf S) x)) trace
        (NativeActiveParityExecution.parity (labels x) S.length)) : Correct M S T := by
  intro x t ht
  obtain ⟨trace,native⟩ := exec x t ht
  obtain ⟨qs,updates,f,run⟩ := from_native M native _ t rfl
  refine ⟨⟨qs,updates,f,_,run⟩,?_⟩
  intro qs updates f b run
  obtain ⟨other,native'⟩ := to_native run 0
  exact (NativeSerialDepth.run_unique native' native).2

private theorem no_updates {E : Type} {M : Controller E}
    (quiet : ∀ c v, M.instruction c ≠ .applyRho v) {u : Source}
    {c f : E} {t : Nat} {qs : List (E × Nat)} {updates : Nat} {b : Bool}
    (run : Run M u c t qs updates f b) : updates = 0 := by
  induction run with
  | halt => rfl
  | read _ _ ih => exact ih
  | update row => exact False.elim (quiet _ _ row)
  | internal _ _ ih => exact ih

private noncomputable def active (S : Source) (K : Nat) :
    Installation (NativeFibonacciActiveTable.dimension S.length+7) where
  State := NativeActiveParityExecution.Control S.length
  finite := inferInstance
  machine := ⟨NativeActiveParityExecution.start S.length,
    NativeFibonacciActiveTable.nativeProgram (chartOf S).address K⟩
  encode := NativeFibonacciActiveTable.encode (NativeFibonacciActiveTable.path S.length)
  positive := by omega
  injective := (NativeFibonacciActiveTable.native_fibonacci_active_table S.length (chartOf S).address K).2.2.1
  admissible := (NativeFibonacciActiveTable.native_fibonacci_active_table S.length (chartOf S).address K).2.2.2.1
  readLegal := by
    intro c p k row y
    have rows := (NativeFibonacciActiveTable.native_fibonacci_active_table
      S.length (chartOf S).address K).2.2.2.2.2.1 c
    dsimp only at row
    rw [row] at rows
    rw [rows y]
    split <;> omega
  updateLegal := by
    intro c v row
    have rows := (NativeFibonacciActiveTable.native_fibonacci_active_table
      S.length (chartOf S).address K).2.2.2.2.2.1 c
    dsimp only at row
    rw [row] at rows
    exact rows.le

private noncomputable def stationary (S : Source) (K : Nat) :
    Installation (NativeFibonacciActiveTable.dimension
      (NativeFibonacciStaticScan.dataList (chartOf S) K).length+7) := by
  let ps := NativeFibonacciStaticScan.dataList (chartOf S) K
  let facts := (NativeFibonacciStaticScan.native_static_complete_scan ps (.of true)).1
  exact {
    State := NativeFibonacciStaticScan.Control ps.length
    finite := inferInstance
    machine := ⟨NativeFibonacciStaticScan.start ps.length,NativeFibonacciStaticScan.program ps⟩
    encode := NativeFibonacciStaticScan.encode
    positive := by omega
    injective := facts.injective
    admissible := facts.admissible
    readLegal := by
      intro c p k row y
      have rows := facts.rows c
      dsimp only at row
      rw [row] at rows
      exact (rows y).le
    updateLegal := by
      intro c v row
      have rows := facts.rows c
      dsimp only at row
      rw [row] at rows
      exact rows.elim }

/-- Actual delivered upper executions and whole-table encodings establish
nonemptiness of the full classes on the original supplied parity family. -/
theorem native_upper_members (S : Source) (T : Nat) (even : S.length%2=0) :
    Feasible S T (NativeFibonacciActiveTable.dimension S.length+7) ∧
      StaticFeasible S T (NativeFibonacciActiveTable.dimension (S.length*((T+1)/2+1))+7) := by
  let K := (T+1)/2
  have bound : ∀ t, t ≤ T → t ≤ 2*K := by intro t ht; dsimp [K]; omega
  have ac : Correct (active S K).machine S T := by
    apply correct_of_native
    intro x t ht
    obtain ⟨trace,run,_⟩ := NativeFibonacciActiveTable.encoded_active_parity_execution
      S x t K (bound t ht) (Or.inl even)
    exact ⟨trace,run⟩
  let ps := NativeFibonacciStaticScan.dataList (chartOf S) K
  have size : ps.length = S.length*(K+1) :=
    (NativeFibonacciStaticScan.original_static_parity_scan S (fun _ => false) 0 K
      (by omega) (Or.inl even)).2.1
  have sc : Correct (stationary S K).machine S T := by
    apply correct_of_native
    intro x t ht
    have facts := (NativeFibonacciStaticScan.original_static_parity_scan
      S x t K (bound t ht) (Or.inl even)).2.2.1
    exact ⟨_,facts.native⟩
  have st : Static (stationary S K).machine S T := by
    intro x t ht qs updates f b run
    apply no_updates (M := (stationary S K).machine) _ run
    intro c v row
    have rows := (NativeFibonacciStaticScan.native_static_complete_scan ps (.of true)).1.rows c
    change NativeFibonacciStaticScan.program ps c = .applyRho v at row
    rw [row] at rows
    exact rows
  refine ⟨⟨active S K,ac⟩,?_⟩
  have result : StaticFeasible S T (NativeFibonacciActiveTable.dimension ps.length+7) :=
    ⟨stationary S K,sc,st⟩
  simpa only [size,K] using result

private theorem feasible_lower {S : Source} {T w : Nat} (feasible : Feasible S T w) :
    capacity (S.length+2) ≤ w := by
  obtain ⟨I,correct⟩ := feasible
  have lower := (NativeSuppliedComparison.installed_lower_bound correct).2.2
  let code (c : I.State) : {v : Fin w → Bool // Adm w v} := ⟨I.encode c,I.admissible c⟩
  have inj : Function.Injective code := by
    intro a b eq
    exact I.injective (congrArg Subtype.val eq)
  have count := Fintype.card_le_of_injective code inj
  rw [D5.S1.Words.AdmissibleWords.AdmissibleCount.admissibleWord_card_eq_fib] at count
  exact capacity_le (by omega) (lower.trans count)

private theorem static_feasible_lower {S : Source} {T w : Nat}
    (feasible : StaticFeasible S T w) : capacity (S.length*((T+3)/3)+2) ≤ w := by
  obtain ⟨I,correct,static⟩ := feasible
  have lower := (NativeSuppliedComparison.static_installed_lower_bound correct static).2
  let code (c : I.State) : {v : Fin w → Bool // Adm w v} := ⟨I.encode c,I.admissible c⟩
  have inj : Function.Injective code := fun a b eq => I.injective (congrArg Subtype.val eq)
  have count := Fintype.card_le_of_injective code inj
  rw [D5.S1.Words.AdmissibleWords.AdmissibleCount.admissibleWord_card_eq_fib] at count
  exact capacity_le (by omega) (lower.trans count)

private theorem active_exists (S : Source) (T : Nat) (even : S.length%2=0) :
    ∃ w, Feasible S T w := ⟨_,(native_upper_members S T even).1⟩
private theorem static_exists (S : Source) (T : Nat) (even : S.length%2=0) :
    ∃ w, StaticFeasible S T w := ⟨_,(native_upper_members S T even).2⟩

noncomputable def activeMinimum (S : Source) (T : Nat) (even : S.length%2=0) : Nat :=
  by classical exact Nat.find (active_exists S T even)
noncomputable def staticMinimum (S : Source) (T : Nat) (even : S.length%2=0) : Nat :=
  by classical exact Nat.find (static_exists S T even)

/-- Both least widths are attained over the full comparison classes. The
inverse capacity counts the entire admissible word space. -/
theorem minimum_width_bounds (S : Source) (T : Nat) (even : S.length%2=0) :
    let a := activeMinimum S T even
    let s := staticMinimum S T even
    let K := (T+1)/2
    let M := S.length*(K+1)
    let r := (T+3)/3
    Feasible S T a ∧ (∀ w, Feasible S T w → a ≤ w) ∧
    StaticFeasible S T s ∧ (∀ w, StaticFeasible S T w → s ≤ w) ∧
    capacity (S.length+2) ≤ a ∧ a ≤ capacity (S.length+1)+7 ∧
    capacity (S.length+1)+7 ≤ capacity (S.length+2)+7 ∧
    capacity (S.length*r+2) ≤ s ∧ s ≤ capacity (M+1)+7 ∧
    capacity (M+1)+7 ≤ capacity (S.length*r+2)+9 := by
  classical
  dsimp only
  have am := Nat.find_spec (active_exists S T even)
  have sm := Nat.find_spec (static_exists S T even)
  have amin : ∀ w, Feasible S T w → activeMinimum S T even ≤ w :=
    fun w hw => Nat.find_min' (active_exists S T even) hw
  have smin : ∀ w, StaticFeasible S T w → staticMinimum S T even ≤ w :=
    fun w hw => Nat.find_min' (static_exists S T even) hw
  have upper := native_upper_members S T even
  have al : capacity (S.length+2) ≤ activeMinimum S T even := feasible_lower am
  have sl : capacity (S.length*((T+3)/3)+2) ≤ staticMinimum S T even := static_feasible_lower sm
  have au := amin _ upper.1
  have su := smin _ upper.2
  have ac : capacity (S.length+1)+7 ≤ capacity (S.length+2)+7 :=
    Nat.add_le_add_right (capacity_mono (by omega) (by omega)) 7
  have rpos : 1 ≤ (T+3)/3 := by omega
  have Kbound : (T+1)/2+1 ≤ 2*((T+3)/3) := by omega
  have mBound : S.length*((T+1)/2+1)+1 ≤ 2*(S.length*((T+3)/3)+2) := by
    nlinarith
  have sc := (capacity_mono (by omega) mBound).trans
    (capacity_double (S.length*((T+3)/3)+2) (by omega))
  refine ⟨am,amin,sm,smin,al,?_,ac,sl,?_,by omega⟩
  · simpa [capacity] using au
  · simpa [capacity] using su

private theorem fib_phi_lower (d : Nat) :
    Real.goldenRatio^d ≤ (Nat.fib (d+2) : ℝ) := by
  have h := D5.S3.Axis.AxisConvergence.goldenRatio_pow_div_le_fib_succ (d+1)
  simpa [pow_succ,Real.goldenRatio_pos.ne'] using h

private theorem fib_phi_upper (d : Nat) :
    (Nat.fib (d+2) : ℝ) ≤ Real.goldenRatio^(d+1) := by
  have h := Real.goldenRatio_mul_fib_succ_add_fib d
  have one := Real.one_lt_goldenRatio
  have nonneg : 0 ≤ (Nat.fib (d+1) : ℝ) := by positivity
  have recurrence : (Nat.fib (d+2) : ℝ) = Nat.fib d + Nat.fib (d+1) := by
    exact_mod_cast (Nat.fib_add_two (n := d))
  nlinarith

private theorem capacity_log_bounds (n : Nat) (positive : 0 < n) :
    Real.logb Real.goldenRatio n-1 ≤ (capacity n : ℝ) ∧
      (capacity n : ℝ) ≤ Real.logb Real.goldenRatio n+1 := by
  let d := capacity n
  have phi := Real.one_lt_goldenRatio
  have pn : 0 < (n : ℝ) := by exact_mod_cast positive
  have self : Real.logb Real.goldenRatio Real.goldenRatio = 1 :=
    Real.logb_self_eq_one phi
  have cap : n ≤ Nat.fib (d+2) := by
    have h := (dimension_spec (n-1)).1
    change n-1+1 ≤ Nat.fib (d+2) at h
    omega
  have castCap : (n : ℝ) ≤ (Nat.fib (d+2) : ℝ) := by exact_mod_cast cap
  have powbound : (n : ℝ) ≤ Real.goldenRatio^(d+1) := castCap.trans (fib_phi_upper d)
  have lo := Real.logb_le_logb_of_le phi pn powbound
  rw [Real.logb_pow,self,mul_one] at lo
  constructor
  · dsimp [d] at lo
    push_cast at lo
    linarith
  · by_cases zero : d = 0
    · have nonneg := Real.logb_nonneg phi (show 1 ≤ (n : ℝ) by exact_mod_cast positive)
      change (d : ℝ) ≤ _
      rw [zero]
      norm_num only [Nat.cast_zero]
      linarith
    · have minimal := (dimension_spec (n-1)).2 (d-1) (by change d-1 < d; omega)
      have strict : Real.goldenRatio^(d-1) < (n : ℝ) := by
        have h : (Nat.fib (d-1+2) : ℝ) < n := by exact_mod_cast (show Nat.fib (d-1+2) < n by omega)
        exact (fib_phi_lower (d-1)).trans_lt h
      have hi := Real.logb_lt_logb phi (pow_pos Real.goldenRatio_pos _) strict
      rw [Real.logb_pow,self,mul_one] at hi
      rw [Nat.cast_sub (by omega : 1 ≤ d)] at hi
      change (d : ℝ) ≤ _
      norm_num at hi
      linarith

/-- Explicit absolute errors give coefficient one, uniformly over all supplied
shapes, even leaf counts and finite lag promises. -/
theorem uniform_logarithmic_width (S : Source) (T : Nat) (even : S.length%2=0) :
    |(activeMinimum S T even : ℝ)-Real.logb Real.goldenRatio S.length| ≤ 10 ∧
    |(staticMinimum S T even : ℝ)-
      Real.logb Real.goldenRatio (S.length*(T+1) : Nat)| ≤ 10 := by
  obtain ⟨_,_,_,_,al,au,_,sl,su,_⟩ := minimum_width_bounds S T even
  have hpos := S.length_pos
  have hlog := capacity_log_bounds S.length hpos
  have acl := (capacity_mono hpos (by omega : S.length ≤ S.length+2)).trans al
  have acu : activeMinimum S T even ≤ capacity S.length+9 := by
    have mon := capacity_mono (by omega : 0 < S.length+1)
      (by omega : S.length+1 ≤ 2*S.length)
    have dbl := capacity_double S.length hpos
    omega
  have aleft : (capacity S.length : ℝ) ≤ activeMinimum S T even := by exact_mod_cast acl
  have aright : (activeMinimum S T even : ℝ) ≤ (capacity S.length : ℝ)+9 := by exact_mod_cast acu
  constructor
  · exact abs_le.mpr ⟨by linarith [hlog.1],by linarith [hlog.2]⟩
  · let n := S.length*(T+1)
    let q := S.length*((T+3)/3)+2
    have npos : 0 < n := by dsimp [n]; positivity
    have qpos : 0 < q := by dsimp [q]; omega
    have log := capacity_log_bounds n npos
    have nbound : n ≤ 2*(2*q) := by
      have rbound : T+1 ≤ 3*((T+3)/3) := by omega
      dsimp [n,q]
      nlinarith
    have inv := (capacity_mono npos nbound).trans
      ((capacity_double (2*q) (by omega)).trans
        (Nat.add_le_add_right (capacity_double q qpos) 2))
    have lower : capacity n ≤ staticMinimum S T even+4 := by
      change capacity q ≤ staticMinimum S T even at sl
      omega
    have mBound : S.length*((T+1)/2+1)+1 ≤ 2*n := by
      have kbound : (T+1)/2+1 ≤ T+1 := by omega
      dsimp [n]
      nlinarith
    have mon := (capacity_mono (by omega) mBound).trans (capacity_double n npos)
    have upper : staticMinimum S T even ≤ capacity n+9 := by omega
    have left : (capacity n : ℝ) ≤ (staticMinimum S T even : ℝ)+4 := by exact_mod_cast lower
    have right : (staticMinimum S T even : ℝ) ≤ (capacity n : ℝ)+9 := by exact_mod_cast upper
    exact abs_le.mpr ⟨by linarith [log.1],by linarith [log.2]⟩

#print axioms native_upper_members
#print axioms minimum_width_bounds
#print axioms uniform_logarithmic_width

end D5.S3.Arith.FibonacciAtomic.Observer.NativeSuppliedWidth
