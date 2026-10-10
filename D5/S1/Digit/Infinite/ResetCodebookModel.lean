/- GID: D5/S1/Digit/Infinite/ResetCodebookModel
   generality: I
   mirror-B: D5/B/S1/Digit/Infinite/ResetCodebookModel
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Source returns, bilateral histories, and pruned weighted transition matrices. -/

import D5.S1.Digit.Infinite.FixedTailClosedBudget
import D5.S1.Digit.Infinite.SixWindowForcing
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.List.OfFn
import Mathlib.Order.Filter.AtTopBot.CompleteLattice
import Mathlib.Tactic.LinearCombination
local notation "g_bounds" => And.intro (And.left (And.right D5.S1.Digit.Infinite.SixWindowForcing.algebra)) (And.left (And.right (And.right D5.S1.Digit.Infinite.SixWindowForcing.algebra)))
local notation "g_relation" => (And.left D5.S1.Digit.Infinite.SixWindowForcing.algebra)
local notation "g_eq" => (And.left (And.right (And.right (And.right D5.S1.Digit.Infinite.OddColorThreeSource.golden_relations))))
local notation "t_sq" => (And.right (And.right (And.right (And.right D5.S1.Digit.Infinite.SixWindowForcing.algebra))))
local notation "t_linear" => (And.left (And.right (And.right (And.right D5.S1.Digit.Infinite.SixWindowForcing.algebra))))
set_option autoImplicit false
set_option maxHeartbeats 1600000
open D5.S1.Digit.Infinite.ClosedObservationCommonTailWidthModel
open D5.S1.Digit.Infinite.FixedTailClosedBudget
open D5.S1.Digit.Infinite.SuccessorContinuity (LegalDigits)
open D5.S1.Digit.Infinite.ClosedObservationGraphRealization
open D5.S1.Words.Powers (wordPower)
namespace D5.S1.Digit.Infinite.ResetCodebook
def U : List Label := [fiveLabel, nullLabel, threeLabel, nullLabel, threeLabel, threeLabel]
def V : List Label := [nullLabel, threeLabel, threeLabel, fiveLabel, nullLabel, threeLabel]
def C : List Label := [fiveLabel, fiveLabel, threeLabel, twoLabel, twoLabel, nullLabel,
  threeLabel, threeLabel, threeLabel, twoFiveLabel, fiveLabel, nullLabel, nullLabel,
  twoLabel, twoLabel, twoFiveLabel, threeLabel, threeLabel, nullLabel, fiveLabel]
def sixColor : List (Fin 6) := [2,1,0,2,1,0]
def twentyColor : List (Fin 6) := [2,3,0,3,4,2,0,1,0,5,2,1,1,3,3,5,0,0,1,2]
def sideWord (low : Bool) : List Label := if low then V else U
noncomputable def c0 : ℝ := 2*t/5
noncomputable def rho : ℝ := g^6
noncomputable def chi : ℝ := g^20
noncomputable def h (low : Bool) : ℝ := if low then (46+31*g)/380 else (39-6*g)/380
noncomputable def A (low : Bool) : ℝ := (1-rho)*h low
noncomputable def E (low : Bool) : ℝ := if low then c0 else t^2-c0
noncomputable def X (low : Bool) : ℝ := A low + rho*chi^3*E low
noncomputable def Y (low : Bool) : ℝ := A low + rho*chi*X low
noncomputable def coord (low : Bool) (D : ℝ) : ℝ := if low then c0-D else c0+D
theorem center : c0=(1+g)/5 := by unfold c0; rw [g_eq]; ring
def zeroAddress : LegalDigits := ⟨fun _ => false, by simp⟩
theorem zero_state (s : Bool) : stateAddress s zeroAddress := by simp [stateAddress,zeroAddress]
theorem zero_finite : finiteTail zeroAddress := ⟨0, by simp [zeroAddress]⟩
theorem zero_scalar : kappa zeroAddress = 0 := by
  simp [kappa, window, D5.S1.Digit.Infinite.WindowSuccessorGraph.P,
    bitShift, zeroAddress, offset]
theorem finite_of_prefix (w : List Label) (x y : LegalDigits)
    (hp : addressPrefix w x y) (hy : finiteTail y) : finiteTail x := by
  induction w generalizing x with
  | nil => simpa [addressPrefix] using hp.symm ▸ hy
  | cons l w ih =>
    obtain ⟨N,hN⟩ := ih (originalT x) hp.2
    refine ⟨N+3, ?_⟩
    intro j hj
    have hv := hN (j-3) (by omega)
    simpa [originalT,bitShift, Nat.sub_add_cancel (show 3≤j by omega)] using hv
theorem U_path (s : Bool) : SourcePath s U false := by
  cases s <;> exact (SourcePath.cons (s' := true) (by simp [lawful,outgoing,fiveLabel,nullLabel,threeLabel,twoLabel,twoFiveLabel]) (SourcePath.cons (s' := false) (by simp [lawful,outgoing,fiveLabel,nullLabel,threeLabel,twoLabel,twoFiveLabel]) (SourcePath.cons (s' := false) (by simp [lawful,outgoing,fiveLabel,nullLabel,threeLabel,twoLabel,twoFiveLabel]) (SourcePath.cons (s' := false) (by simp [lawful,outgoing,fiveLabel,nullLabel,threeLabel,twoLabel,twoFiveLabel]) (SourcePath.cons (s' := false) (by simp [lawful,outgoing,fiveLabel,nullLabel,threeLabel,twoLabel,twoFiveLabel]) (SourcePath.cons (s' := false) (by simp [lawful,outgoing,fiveLabel,nullLabel,threeLabel,twoLabel,twoFiveLabel]) (SourcePath.nil false)))))))
theorem V_path (s : Bool) : SourcePath s V false := by
  cases s <;> exact (SourcePath.cons (s' := false) (by simp [lawful,outgoing,fiveLabel,nullLabel,threeLabel,twoLabel,twoFiveLabel]) (SourcePath.cons (s' := false) (by simp [lawful,outgoing,fiveLabel,nullLabel,threeLabel,twoLabel,twoFiveLabel]) (SourcePath.cons (s' := false) (by simp [lawful,outgoing,fiveLabel,nullLabel,threeLabel,twoLabel,twoFiveLabel]) (SourcePath.cons (s' := true) (by simp [lawful,outgoing,fiveLabel,nullLabel,threeLabel,twoLabel,twoFiveLabel]) (SourcePath.cons (s' := false) (by simp [lawful,outgoing,fiveLabel,nullLabel,threeLabel,twoLabel,twoFiveLabel]) (SourcePath.cons (s' := false) (by simp [lawful,outgoing,fiveLabel,nullLabel,threeLabel,twoLabel,twoFiveLabel]) (SourcePath.nil false)))))))
theorem C_path (s : Bool) : SourcePath s C true := by
  cases s <;> exact (SourcePath.cons (s' := true) (by simp [lawful,outgoing,fiveLabel,nullLabel,threeLabel,twoLabel,twoFiveLabel]) (SourcePath.cons (s' := true) (by simp [lawful,outgoing,fiveLabel,nullLabel,threeLabel,twoLabel,twoFiveLabel]) (SourcePath.cons (s' := false) (by simp [lawful,outgoing,fiveLabel,nullLabel,threeLabel,twoLabel,twoFiveLabel]) (SourcePath.cons (s' := false) (by simp [lawful,outgoing,fiveLabel,nullLabel,threeLabel,twoLabel,twoFiveLabel]) (SourcePath.cons (s' := false) (by simp [lawful,outgoing,fiveLabel,nullLabel,threeLabel,twoLabel,twoFiveLabel]) (SourcePath.cons (s' := false) (by simp [lawful,outgoing,fiveLabel,nullLabel,threeLabel,twoLabel,twoFiveLabel]) (SourcePath.cons (s' := false) (by simp [lawful,outgoing,fiveLabel,nullLabel,threeLabel,twoLabel,twoFiveLabel]) (SourcePath.cons (s' := false) (by simp [lawful,outgoing,fiveLabel,nullLabel,threeLabel,twoLabel,twoFiveLabel]) (SourcePath.cons (s' := false) (by simp [lawful,outgoing,fiveLabel,nullLabel,threeLabel,twoLabel,twoFiveLabel]) (SourcePath.cons (s' := true) (by simp [lawful,outgoing,fiveLabel,nullLabel,threeLabel,twoLabel,twoFiveLabel]) (SourcePath.cons (s' := true) (by simp [lawful,outgoing,fiveLabel,nullLabel,threeLabel,twoLabel,twoFiveLabel]) (SourcePath.cons (s' := false) (by simp [lawful,outgoing,fiveLabel,nullLabel,threeLabel,twoLabel,twoFiveLabel]) (SourcePath.cons (s' := false) (by simp [lawful,outgoing,fiveLabel,nullLabel,threeLabel,twoLabel,twoFiveLabel]) (SourcePath.cons (s' := false) (by simp [lawful,outgoing,fiveLabel,nullLabel,threeLabel,twoLabel,twoFiveLabel]) (SourcePath.cons (s' := false) (by simp [lawful,outgoing,fiveLabel,nullLabel,threeLabel,twoLabel,twoFiveLabel]) (SourcePath.cons (s' := true) (by simp [lawful,outgoing,fiveLabel,nullLabel,threeLabel,twoLabel,twoFiveLabel]) (SourcePath.cons (s' := false) (by simp [lawful,outgoing,fiveLabel,nullLabel,threeLabel,twoLabel,twoFiveLabel]) (SourcePath.cons (s' := false) (by simp [lawful,outgoing,fiveLabel,nullLabel,threeLabel,twoLabel,twoFiveLabel]) (SourcePath.cons (s' := false) (by simp [lawful,outgoing,fiveLabel,nullLabel,threeLabel,twoLabel,twoFiveLabel]) (SourcePath.cons (s' := true) (by simp [lawful,outgoing,fiveLabel,nullLabel,threeLabel,twoLabel,twoFiveLabel]) (SourcePath.nil true)))))))))))))))))))))
theorem path_power {s : Bool} (w : List Label) (hw : SourcePath s w s) (n : ℕ) :
    SourcePath s (wordPower n w) s := by
  induction n with
  | zero => exact .nil s
  | succ n ih =>
    simpa [wordPower, List.replicate_succ, List.flatten_cons] using path_append hw ih
theorem side_path (low s : Bool) : SourcePath s (sideWord low) false := by
  cases low <;> first | exact U_path s | exact V_path s
def Return := {mr : ℕ × ℕ // 1 ≤ mr.1 ∧ 1 ≤ mr.2}
def returnWord (low : Bool) (a : Return) :=
  wordPower a.val.1 (sideWord low) ++ wordPower a.val.2 C
def returnColors (a : Return) := wordPower a.val.1 sixColor ++ wordPower a.val.2 twentyColor
theorem return_path (low : Bool) (a : Return) : SourcePath true (returnWord low a) true := by
  have hm0 : a.val.1 ≠ 0 := by have := a.property.1; omega
  obtain ⟨m,hm⟩ := Nat.exists_eq_succ_of_ne_zero hm0
  have hr0 : a.val.2 ≠ 0 := by have := a.property.2; omega
  obtain ⟨r,hr⟩ := Nat.exists_eq_succ_of_ne_zero hr0
  unfold returnWord
  rw [hm,hr]
  simp only [wordPower, List.replicate_succ, List.flatten_cons]
  apply path_append
  · exact path_append (side_path low true)
      (path_power (sideWord low) (side_path low false) m)
  · exact path_append (C_path false) (path_power C (C_path true) r)
def tailWord (low : Bool) := sideWord low ++ wordPower 3 C ++ (if low then [] else [fiveLabel])
theorem tail_path (low : Bool) : SourcePath true (tailWord low) true := by
  unfold tailWord
  rw [List.append_assoc]
  apply path_append (side_path low true)
  apply path_append
  · change SourcePath false (C ++ (C ++ (C ++ []))) true
    exact path_append (C_path false) (path_append (C_path true) (path_append (C_path true) (.nil true)))
  · cases low
    · exact .cons (by simp [lawful,outgoing,fiveLabel,nullLabel,threeLabel,twoLabel,twoFiveLabel]) (.nil true)
    · exact .nil true
noncomputable def literalTail (low : Bool) : LegalDigits :=
  Classical.choose (source_path_realization (tail_path low) zeroAddress (zero_state true))
theorem literal_tail_spec (low : Bool) : stateAddress true (literalTail low) ∧
    finiteTail (literalTail low) ∧ addressPrefix (tailWord low) (literalTail low) zeroAddress ∧
    kappa (literalTail low)=wordScalar (tailWord low) 0 := by
  have hs := Classical.choose_spec (source_path_realization (tail_path low) zeroAddress (zero_state true))
  refine ⟨hs.1, finite_of_prefix _ _ _ hs.2 zero_finite, hs.2, ?_⟩
  exact (prefix_scalar _ _ _ hs.2).trans (congrArg (wordScalar (tailWord low)) zero_scalar)
def listWord (low : Bool) (as : List Return) := as.flatMap (returnWord low)
def listColors (as : List Return) := as.flatMap returnColors
def sourcePrefix (low anchor : Bool) (exec : List Return) :=
  (sideWord low ++ C) ++ listWord low exec.reverse ++ (if anchor then sideWord low ++ C else [])
def colors (anchor : Bool) (exec : List Return) :=
  (sixColor ++ twentyColor) ++ listColors exec.reverse ++ (if anchor then sixColor ++ twentyColor else [])
theorem list_path (low : Bool) (as : List Return) : SourcePath true (listWord low as) true := by
  induction as with
  | nil => exact .nil true
  | cons a as ih => exact path_append (return_path low a) ih
theorem prefix_path (low anchor : Bool) (exec : List Return) : SourcePath false (sourcePrefix low anchor exec) true := by
  unfold sourcePrefix
  apply path_append
  · exact path_append (path_append (side_path low false) (C_path false)) (list_path low exec.reverse)
  · cases anchor
    · exact .nil true
    · exact path_append (side_path low true) (C_path false)
theorem actual_pair (anchor : Bool) (exec : List Return) :
    ∃ src : Bool → LegalDigits, ∀ low,
      stateAddress false (src low) ∧ finiteTail (src low) ∧
      addressPrefix (sourcePrefix low anchor exec) (src low) (literalTail low) ∧
      kappa (src low)=wordScalar (sourcePrefix low anchor exec) (kappa (literalTail low)) := by
  have hp (low : Bool) := source_path_realization (prefix_path low anchor exec)
    (literalTail low) (literal_tail_spec low).1
  choose src hs using hp
  exact ⟨src, fun low => ⟨(hs low).1,
    finite_of_prefix _ _ _ (hs low).2 (literal_tail_spec low).2.1,
    (hs low).2, prefix_scalar _ _ _ (hs low).2⟩⟩
end D5.S1.Digit.Infinite.ResetCodebook
set_option autoImplicit false
open D5.S1.Digit.Infinite.ClosedObservationCommonTailWidthModel
open D5.S1.Digit.Infinite.FixedTailClosedBudget
open D5.S1.Digit.Infinite.SuccessorContinuity (LegalDigits)
open scoped Topology
namespace D5.S1.Digit.Infinite.ResetCodebook.Statement
noncomputable def G (low : Bool) (a : D5.S1.Digit.Infinite.ResetCodebook.Return) (D : ℝ) :=
  h low-rho^a.val.1*(h low-chi^a.val.2*D)
noncomputable def weak (K : ℕ) (d : ℝ) : List D5.S1.Digit.Infinite.ResetCodebook.Return → ℝ → Prop
  | [], _ => True
  | a::as, D => a.val.2 ≤ K ∧ (a.val.2=K → d ≤ D) ∧ weak K d as (G false a D)
def weight (as : List D5.S1.Digit.Infinite.ResetCodebook.Return) := (as.map (fun a => 6*a.val.1+20*a.val.2)).sum
noncomputable def codebook (anchor : Bool) (K N : ℕ) (d : ℝ) : Set (List D5.S1.Digit.Infinite.ResetCodebook.Return) :=
  {as | weight as=N ∧ weak K d as (if anchor then Y false else X false)}
def letters (as : List D5.S1.Digit.Infinite.ResetCodebook.Return) : List Bool :=
  as.flatMap (fun a => List.replicate a.val.2 true ++ List.replicate a.val.1 false)
def letterWeight (w : List Bool) := (w.map (fun c => if c then 20 else 6)).sum
noncomputable def f (a : Bool) (D : ℝ) := if a then chi*D else A false+rho*D
noncomputable def past (w : ℤ → Bool) (i : ℤ) (n : ℕ) (z : ℝ) :=
  ((List.range n).map (fun j => w (i-(n:ℤ)+(j:ℤ)))).foldl (fun D a => f a D) z
noncomputable def state (w : ℤ → Bool) (i : ℤ) := sSup (Set.range (fun n => past w i n 0))
def high (K : ℕ) (w : ℤ → Bool) (i : ℤ) := ∀ j<K, w (i-(j:ℤ))=true
def cap (K : ℕ) (w : ℤ → Bool) := ∀ i, ¬high (K+1) w i
noncomputable def lowerLanguage (K n : ℕ) (d : ℝ) : Set (ℤ → Bool) :=
  {w | cap K w ∧ ∀ i, high K w i → chi^(K-1)*d < past w i n 0}
def factor (w : List Bool) (omega : ℤ → Bool) :=
  ∃ i : ℤ, ∀ j : Fin w.length, omega (i+(j.val:ℤ))=w[j.val]
noncomputable def factorCount (lang : Set (ℤ → Bool)) (N : ℕ) :=
  Nat.card {w : List Bool // letterWeight w=N ∧ ∃ omega∈lang, factor w omega}
noncomputable def rate (lang : Set (ℤ → Bool)) :=
  Filter.limsup (fun N : ℕ => Real.log (max 1 (factorCount lang N):ℝ)/Real.log 2/(N:ℝ)) Filter.atTop
def reset (M : ℕ) (hM : 1 ≤ M) : D5.S1.Digit.Infinite.ResetCodebook.Return := ⟨(M,1),hM,Nat.le_refl 1⟩
noncomputable def B (M : ℕ) := h false-rho^M*(h false-chi*A false)
noncomputable def autoCost (K : ℕ) :=
  max (lambda-g^2*chi*X false) (max (lambda-g^2*chi^(K-1)*A false) (lambda-rho))
noncomputable def actualEps (anchor : Bool) (K M N : ℕ) (b : ℝ) :=
  min (b-autoCost K) (g^2*chi^K*(B M-(if anchor then Y false else X false))*g^N)/2
noncomputable def concatenation (anchor : Bool) (K M N : ℕ) (d : ℝ) (hM : 1 ≤ M)
    (omega : ℤ → Bool) : Prop :=
  ∃ cuts : ℤ → ℤ, StrictMono cuts ∧
    Filter.Tendsto cuts Filter.atTop Filter.atTop ∧
    Filter.Tendsto cuts Filter.atBot Filter.atBot ∧
    ∃ v : ℤ → List D5.S1.Digit.Infinite.ResetCodebook.Return, ∀ i,
      v i ∈ codebook anchor K N d ∧
      cuts (i+1)-cuts i=(letters (reset M hM::v i)).length ∧
      ∀ j : Fin (letters (reset M hM::v i)).length,
        omega (cuts i+(j.val:ℤ))=(letters (reset M hM::v i))[j.val]
noncomputable def finiteActual (anchor : Bool) (K M N : ℕ) (b d : ℝ) (hM : 1 ≤ M) : Prop :=
  ∀ vs : List (List D5.S1.Digit.Infinite.ResetCodebook.Return), (∀ v∈vs, v∈codebook anchor K N d) →
  let exec := (vs.map (fun v => reset M hM::v)).flatten
  weak K (d+(B M-(if anchor then Y false else X false))*g^N) exec
      (if anchor then Y false else X false) ∧
  ∃ src : Bool → LegalDigits, ∀ low,
    stateAddress false (src low) ∧ finiteTail (src low) ∧
    addressPrefix (sourcePrefix low anchor exec) (src low) (literalTail low) ∧
    wordCost (sourcePrefix low anchor exec) (colors anchor exec) (kappa (literalTail low))
      ≤ b-2*actualEps anchor K M N b ∧
    ∀ Q : ℝ → Fin 6,
      (∀ j z, z∈Set.Ioo (cellLower j) (cellUpper j) → Q z=j) →
      ∃ errors : ℕ → ℝ, ∀ p : Fin (colors anchor exec).length,
        |errors p.val| < b-actualEps anchor K M N b ∧
        Q (min (1+t) (max (-1) (kappa ((originalT)^[p.val] (src low))+errors p.val)))
          =(colors anchor exec)[p.val]
noncomputable def target6218Language (anchor : Bool) (K M N : ℕ) (b d : ℝ)
    (hK : 2 ≤ K) (hM : 1 ≤ M) (hN : 0 < N)
    (hbudget : lambda-g^2*chi^K*h false < b ∧
      b < lambda-g^2*chi^K*(A false/(1-rho*chi^K)))
    (hd : d=(lambda-b)/(g^2*chi^K))
    (hreset : max (max (X false) (Y false)) d < B M)
    (hne : (codebook anchor K N d).Nonempty) : Prop :=
  let delta := B M-(if anchor then Y false else X false)
  let eps := chi^(K-1)*delta*g^N
  (codebook anchor K N d).Finite ∧ 0<actualEps anchor K M N b ∧
  finiteActual anchor K M N b d hM ∧
  (∀ omega, concatenation anchor K M N d hM omega →
    cap K omega ∧ (∀ i, Filter.Tendsto (fun n => past omega i n 0) Filter.atTop (nhds (state omega i))) ∧
    ∀ i, high K omega i → chi^(K-1)*d+eps ≤ state omega i) ∧
  ∃ n : ℕ, K≤n ∧ h false*rho^n<eps ∧
    (∀ omega, concatenation anchor K M N d hM omega → omega∈lowerLanguage K n d) ∧
    Real.log (Nat.card {v // v∈codebook anchor K N d}:ℝ)/Real.log 2/(N+20+6*M:ℝ)
      ≤ rate (lowerLanguage K n d)
end D5.S1.Digit.Infinite.ResetCodebook.Statement
set_option autoImplicit false
open scoped Matrix.Norms.Operator
namespace D5.S1.Digit.Infinite.ResetCodebook.Transfer
open D5.S1.Digit.Infinite.ResetCodebook
noncomputable section
attribute [local instance] Classical.propDecidable
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
def wordSet : ℕ → Finset (List Bool)
  | 0 => {[]}
  | k+1 => (wordSet k).image (List.cons false) ∪ (wordSet k).image (List.cons true)
lemma mem_wordSet (w : List Bool) (k : ℕ) : w∈wordSet k ↔ w.length=k := by
  induction k generalizing w with
  | zero => simp [wordSet]
  | succ k ih =>
      cases w with
      | nil => simp [wordSet]
      | cons c w => cases c <;> simp [wordSet,ih]
lemma wordSet_disjoint (k : ℕ) :
    Disjoint ((wordSet k).image (List.cons false)) ((wordSet k).image (List.cons true)) := by
  apply Finset.disjoint_left.mpr
  intro w hw hw'
  obtain ⟨u,_,hu⟩ := Finset.mem_image.mp hw
  obtain ⟨v,_,hv⟩ := Finset.mem_image.mp hw'
  rw [←hu] at hv
  simp at hv
variable (next : ι → Bool → ι) (allow : ι → Bool → Prop)
def mass (z : ℝ) : ι → List Bool → ℝ
  | _, [] => 1
  | v, c::w => if allow v c then z^(if c then 20 else 6) * mass z (next v c) w else 0
def accepts : ι → List Bool → Prop
  | _, [] => True
  | v,c::w => allow v c ∧ accepts (next v c) w
lemma mass_of_accepts (z : ℝ) (v : ι) (w : List Bool) (hw : accepts next allow v w) :
    mass next allow z v w=z^Statement.letterWeight w := by
  induction w generalizing v with
  | nil => simp [mass,Statement.letterWeight]
  | cons c w ih =>
    rw [mass,if_pos hw.1,ih _ hw.2]
    change z^(if c then 20 else 6)*z^Statement.letterWeight w = z^((if c then 20 else 6)+Statement.letterWeight w)
    rw [pow_add]
lemma mass_nonneg (z : ℝ) (hz : 0 ≤ z) (v : ι) (w : List Bool) :
    0 ≤ mass next allow z v w := by
  induction w generalizing v with
  | nil => simp [mass]
  | cons c w ih =>
    dsimp [mass]
    split
    · exact mul_nonneg (pow_nonneg hz _) (ih _)
    · exact le_rfl
def transfer (z : ℝ) : Matrix ι ι ℝ := fun v u =>
  (if allow v false ∧ next v false=u then z^6 else 0) +
  (if allow v true ∧ next v true=u then z^20 else 0)
lemma transfer_nonneg (z : ℝ) (hz : 0 ≤ z) (v u : ι) :
    0 ≤ transfer next allow z v u := by unfold transfer; positivity
lemma transfer_pow_nonneg (z : ℝ) (hz : 0 ≤ z) (k : ℕ) (v u : ι) :
    0 ≤ (transfer next allow z ^ k) v u := by
  induction k generalizing v u with
  | zero => simp only [pow_zero,Matrix.one_apply]; split <;> positivity
  | succ k ih =>
    rw [pow_succ',Matrix.mul_apply]
    exact Finset.sum_nonneg (fun x _ => mul_nonneg (transfer_nonneg next allow z hz v x) (ih x u))
lemma word_mass_eq_row (z : ℝ) (v : ι) (k : ℕ) :
    ∑ w ∈ wordSet k, mass next allow z v w = ∑ u, (transfer next allow z ^ k) v u := by
  induction k generalizing v with
  | zero => simp [wordSet,mass,Matrix.one_apply]
  | succ k ih =>
      rw [wordSet,Finset.sum_union (wordSet_disjoint k)]
      rw [Finset.sum_image (by intro x _ y _ h; exact List.cons.inj h |>.2),
        Finset.sum_image (by intro x _ y _ h; exact List.cons.inj h |>.2)]
      simp only [mass,Bool.false_eq_true,↓reduceIte]
      simp_rw [Finset.sum_ite_irrel,←Finset.mul_sum,ih]
      have hp : transfer next allow z ^ (k+1) = transfer next allow z * transfer next allow z ^ k := pow_succ' _ _
      rw [hp]
      simp only [Matrix.mul_apply]
      rw [Finset.sum_comm]
      simp_rw [←Finset.mul_sum]
      by_cases hf : allow v false <;> by_cases ht : allow v true <;>
        simp [transfer,hf,ht,Finset.sum_add_distrib,ite_mul,add_mul]
end
end D5.S1.Digit.Infinite.ResetCodebook.Transfer
set_option autoImplicit false
open scoped Matrix.Norms.Operator NNReal ENNReal
namespace D5.S1.Digit.Infinite.ResetCodebook.Transfer
open D5.S1.Digit.Infinite.ResetCodebook
noncomputable section
attribute [local instance] Classical.propDecidable
def history (n : ℕ) (w : ℤ → Bool) (i : ℤ) : Fin n → Bool :=
  fun j => w (i-(n:ℤ)+(j.val:ℤ))
def shiftHistory (n : ℕ) (v : Fin n → Bool) (c : Bool) : Fin n → Bool :=
  fun j => if hj : j.val+1<n then v ⟨j.val+1,hj⟩ else c
lemma history_shift (n : ℕ) (w : ℤ → Bool) (i : ℤ) :
    history n w (i+1)=shiftHistory n (history n w i) (w i) := by
  funext j
  dsimp [history,shiftHistory]
  split
  · congr 1; omega
  · congr 1; omega
-- Past vertices are exactly those occurring in bilateral lower-language realizations.
end
end D5.S1.Digit.Infinite.ResetCodebook.Transfer
local notation "Vertex" => fun (lang : Set (ℤ → Bool)) (n : ℕ) =>
  {v : Fin n → Bool // ∃ w∈lang, ∃ i : ℤ, D5.S1.Digit.Infinite.ResetCodebook.Transfer.history n w i=v}
namespace D5.S1.Digit.Infinite.ResetCodebook.Transfer
open D5.S1.Digit.Infinite.ResetCodebook
noncomputable section
attribute [local instance] Classical.propDecidable
def vertexAt (lang : Set (ℤ → Bool)) (n : ℕ) (w : ℤ → Bool) (hw : w∈lang) (i : ℤ) :
    Vertex lang n := ⟨history n w i,w,hw,i,rfl⟩
def graphAllowed (lang : Set (ℤ → Bool)) (n : ℕ) (v : Vertex lang n) (c : Bool) : Prop :=
  ∃ w∈lang, ∃ i : ℤ, history n w i=v.val ∧ w i=c
def graphNext (lang : Set (ℤ → Bool)) (n : ℕ) (v : Vertex lang n) (c : Bool) :
    Vertex lang n :=
  if h : ∃ w∈lang, ∃ i : ℤ, history n w i=shiftHistory n v.val c
  then ⟨shiftHistory n v.val c,h⟩ else v
lemma graphNext_at (lang : Set (ℤ → Bool)) (n : ℕ) (w : ℤ → Bool) (hw : w∈lang) (i : ℤ) :
    graphNext lang n (vertexAt lang n w hw i) (w i)=vertexAt lang n w hw (i+1) := by
  have h : ∃ u∈lang, ∃ j : ℤ, history n u j=
      shiftHistory n (vertexAt lang n w hw i).val (w i) := by
    exact ⟨w,hw,i+1,history_shift n w i⟩
  rw [graphNext,dif_pos h]
  apply Subtype.ext
  exact (history_shift n w i).symm
lemma factor_accepts (lang : Set (ℤ → Bool)) (n : ℕ) (w : List Bool)
    (u : ℤ → Bool) (hu : u∈lang) (i : ℤ)
    (hw : ∀ j : Fin w.length, u (i+(j.val:ℤ))=w[j.val]) :
    accepts (graphNext lang n) (graphAllowed lang n) (vertexAt lang n u hu i) w := by
  induction w generalizing i with
  | nil => trivial
  | cons c w ih =>
      have hc : u i=c := by simpa using hw ⟨0,by simp⟩
      refine ⟨⟨u,hu,i,rfl,hc⟩,?_⟩
      rw [←hc,graphNext_at]
      apply ih
      intro j
      have hh := hw ⟨j.val+1,by simpa using j.isLt⟩
      simpa [show i+1+(j.val:ℤ)=i+((j.val+1:ℕ):ℤ) by omega] using hh
/-- The 6/20 adjacency on the bilateral part of the memory graph. -/
def lowerMatrix (K n : ℕ) (d z : ℝ) :
    Matrix (Vertex (Statement.lowerLanguage K n d) n) (Vertex (Statement.lowerLanguage K n d) n) ℝ :=
  transfer (graphNext (Statement.lowerLanguage K n d) n)
    (graphAllowed (Statement.lowerLanguage K n d) n) z
def lowerComplexMatrix (K n : ℕ) (d z : ℝ) :
    Matrix (Vertex (Statement.lowerLanguage K n d) n) (Vertex (Statement.lowerLanguage K n d) n) ℂ :=
  (Complex.ofRealHom.mapMatrix) (lowerMatrix K n d z)
def SpectralRoot (K n : ℕ) (d z : ℝ) : Prop :=
  0<z ∧ z<1 ∧ spectralRadius ℂ (lowerComplexMatrix K n d z)=1
def gamma (z : ℝ) : ℝ := -Real.log z/Real.log 2
end
end D5.S1.Digit.Infinite.ResetCodebook.Transfer
set_option autoImplicit false
namespace D5.S1.Digit.Infinite.ResetCodebook.Transfer
open D5.S1.Digit.Infinite.ResetCodebook
open D5.S1.Digit.Infinite.ClosedObservationCommonTailWidthModel
noncomputable section
attribute [local instance] Classical.propDecidable
lemma shift_path_history (n : ℕ) (hn : 0<n) (v : ℤ → Fin n → Bool) (w : ℤ → Bool)
    (hs : ∀ i, v (i+1)=shiftHistory n (v i) (w i)) :
    ∀ i, v i=history n w i := by
  have hcoord : ∀ k : ℕ, k<n → ∀ i : ℤ,
      v i ⟨n-1-k,by omega⟩=w (i-1-(k:ℤ)) := by
    intro k
    induction k with
    | zero =>
      intro hk i
      have hp : v i=shiftHistory n (v (i-1)) (w (i-1)) := by simpa using hs (i-1)
      have he := congrFun hp ⟨n-1,by omega⟩
      simpa [shiftHistory,show ¬n-1+1<n by omega] using he
    | succ k ih =>
      intro hk i
      have hp : v i=shiftHistory n (v (i-1)) (w (i-1)) := by simpa using hs (i-1)
      have he := congrFun hp ⟨n-1-(k+1),by omega⟩
      simp only [shiftHistory,dif_pos (by omega : n-1-(k+1)+1<n)] at he
      have hj : (⟨n-1-(k+1)+1,by omega⟩:Fin n)=⟨n-1-k,by omega⟩ := by
        apply Fin.ext
        change n-1-(k+1)+1=n-1-k
        omega
      rw [hj,ih (by omega) (i-1)] at he
      have hi : (i-1)-1-(k:ℤ)=i-1-((k+1:ℕ):ℤ) := by omega
      rw [hi] at he
      exact he
  intro i
  funext j
  have he := hcoord (n-1-j.val) (by omega) i
  have hj : (⟨n-1-(n-1-j.val),by omega⟩:Fin n)=j := by
    apply Fin.ext
    change n-1-(n-1-j.val)=j.val
    omega
  rw [hj] at he
  have hi : i-1-((n-1-j.val:ℕ):ℤ)=i-(n:ℤ)+(j.val:ℤ) := by omega
  rw [hi] at he
  exact he
end
end D5.S1.Digit.Infinite.ResetCodebook.Transfer
set_option autoImplicit false
namespace D5.S1.Digit.Infinite.ResetCodebook.Transfer
open D5.S1.Digit.Infinite.ResetCodebook
open D5.S1.Digit.Infinite.ClosedObservationCommonTailWidthModel
noncomputable section
attribute [local instance] Classical.propDecidable
/-- The current letter has age zero; the state is measured before it. -/
def recent (n : ℕ) (v : Fin n → Bool) (c : Bool) (j : ℕ) : Bool :=
  if hz : j=0 then c else if hj : j≤n then v ⟨n-j,by omega⟩ else false
def memoryHigh (n k : ℕ) (v : Fin n → Bool) (c : Bool) : Prop :=
  ∀ j<k, recent n v c j=true
def memoryLow (n : ℕ) (v : Fin n → Bool) : ℝ :=
  (List.ofFn v).foldl (fun D a => Statement.f a D) 0
/-- The unpruned local edge predicate of definition 62.12. -/
def localAllowed (K n : ℕ) (d : ℝ) (v : Fin n → Bool) (c : Bool) : Prop :=
  ¬memoryHigh n (K+1) v c ∧
  (memoryHigh n K v c → chi^(K-1)*d < memoryLow n v)
lemma recent_history (n : ℕ) (w : ℤ → Bool) (i : ℤ) (j : ℕ) (hj : j≤n) :
    recent n (history n w i) (w i) j=w (i-(j:ℤ)) := by
  by_cases hz : j=0
  · subst j; simp [recent]
  · simp only [recent,dif_neg hz,dif_pos hj,history]
    congr 1
    change i-(n:ℤ)+((n-j:ℕ):ℤ)=i-(j:ℤ)
    omega
lemma memoryHigh_history (n k : ℕ) (w : ℤ → Bool) (i : ℤ) (hk : k≤n+1) :
    memoryHigh n k (history n w i) (w i) ↔ Statement.high k w i := by
  unfold memoryHigh Statement.high
  constructor <;> intro h j hj <;> specialize h j hj
  · rwa [recent_history n w i j (by omega)] at h
  · rwa [recent_history n w i j (by omega)]
lemma memoryLow_history (n : ℕ) (w : ℤ → Bool) (i : ℤ) :
    memoryLow n (history n w i)=Statement.past w i n 0 := by
  have hl : List.ofFn (history n w i)=
      (List.range n).map (fun j : ℕ => w (i-(n:ℤ)+(j:ℤ))) := by
    apply List.ext_getElem
    · simp
    · intro j hj hj'
      simp [history]
  have hcoerce : (do let a ← List.range n; pure (a:ℤ)) =
      (List.range n).map (fun a : ℕ => (a:ℤ)) := by
    induction (List.range n) with
    | nil => rfl
    | cons a l ih =>
        change [(a:ℤ)] ++ (do let b ← l; pure (b:ℤ)) =
          [(a:ℤ)] ++ l.map (fun b : ℕ => (b:ℤ))
        rw [ih]
  unfold memoryLow Statement.past
  rw [hl,hcoerce]
  simp only [List.map_map,Function.comp_def]
lemma localAllowed_history (K n : ℕ) (d : ℝ) (w : ℤ → Bool) (i : ℤ) (hKn : K≤n) :
    localAllowed K n d (history n w i) (w i) ↔
      ¬Statement.high (K+1) w i ∧
      (Statement.high K w i → chi^(K-1)*d<Statement.past w i n 0) := by
  simp only [localAllowed,memoryHigh_history n (K+1) w i (by omega),
    memoryHigh_history n K w i (by omega),memoryLow_history]
/-- Bilateral paths in the original graph before pruning. -/
def RawGraphLabels (K n : ℕ) (d : ℝ) (w : ℤ → Bool) : Prop :=
  ∃ v : ℤ → Fin n → Bool, ∀ i,
    localAllowed K n d (v i) (w i) ∧ v (i+1)=shiftHistory n (v i) (w i)
theorem raw_labels_iff_lower_language (K n : ℕ) (d : ℝ) (hn : 0<n) (hKn : K≤n)
    (w : ℤ → Bool) :
    RawGraphLabels K n d w ↔ w∈Statement.lowerLanguage K n d := by
  constructor
  · rintro ⟨v,hv⟩
    have hh := shift_path_history n hn v w (fun i => (hv i).2)
    have hl (i : ℤ) := (localAllowed_history K n d w i hKn).mp
      (hh i ▸ (hv i).1)
    exact ⟨fun i => (hl i).1,fun i => (hl i).2⟩
  · intro hw
    refine ⟨history n w,fun i => ?_⟩
    exact ⟨(localAllowed_history K n d w i hKn).mpr ⟨hw.1 i,hw.2 i⟩,
      history_shift n w i⟩
/-- The retained edge set is exactly the edges occurring on original bilateral paths. -/
theorem graphAllowed_iff_pruned (K n : ℕ) (d : ℝ) (hn : 0<n) (hKn : K≤n)
    (v : Vertex (Statement.lowerLanguage K n d) n) (c : Bool) :
    graphAllowed (Statement.lowerLanguage K n d) n v c ↔
      ∃ w : ℤ → Bool, RawGraphLabels K n d w ∧
        ∃ i : ℤ, history n w i=v.val ∧ w i=c := by
  simp only [graphAllowed,raw_labels_iff_lower_language K n d hn hKn]
end
end D5.S1.Digit.Infinite.ResetCodebook.Transfer
set_option autoImplicit false
namespace D5.S1.Digit.Infinite.ResetCodebook.Transfer
open D5.S1.Digit.Infinite.ResetCodebook
noncomputable section
attribute [local instance] Classical.propDecidable
def originalPrunedAllowed (K n : ℕ) (d : ℝ)
    (v : Vertex (Statement.lowerLanguage K n d) n) (c : Bool) : Prop :=
  ∃ w : ℤ → Bool, RawGraphLabels K n d w ∧
    ∃ i : ℤ, history n w i=v.val ∧ w i=c
/-- 6/20 adjacency after deleting precisely the edges without bilateral extension. -/
def originalLowerMatrix (K n : ℕ) (d z : ℝ) :=
  transfer (graphNext (Statement.lowerLanguage K n d) n) (originalPrunedAllowed K n d) z
def originalLowerComplexMatrix (K n : ℕ) (d z : ℝ) :=
  Complex.ofRealHom.mapMatrix (originalLowerMatrix K n d z)
lemma originalLowerMatrix_eq (K n : ℕ) (d z : ℝ) (hn : 0<n) (hKn : K≤n) :
    originalLowerMatrix K n d z=lowerMatrix K n d z := by
  unfold originalLowerMatrix lowerMatrix transfer
  ext v u
  simp only [originalPrunedAllowed,←graphAllowed_iff_pruned K n d hn hKn]
lemma originalLowerComplexMatrix_eq (K n : ℕ) (d z : ℝ) (hn : 0<n) (hKn : K≤n) :
    originalLowerComplexMatrix K n d z=lowerComplexMatrix K n d z := by
  unfold originalLowerComplexMatrix lowerComplexMatrix
  rw [originalLowerMatrix_eq K n d z hn hKn]
def OriginalSpectralRoot (K n : ℕ) (d z : ℝ) : Prop :=
  0<z ∧ z<1 ∧ spectralRadius ℂ (originalLowerComplexMatrix K n d z)=1
end
end D5.S1.Digit.Infinite.ResetCodebook.Transfer
set_option autoImplicit false
open scoped Matrix.Norms.Operator Topology
namespace D5.S1.Digit.Infinite.ResetCodebook.Spectral
open D5.S1.Digit.Infinite.ResetCodebook D5.S1.Digit.Infinite.ResetCodebook.Transfer
noncomputable section
attribute [local instance] Classical.propDecidable
def lowFuture (w : ℤ → Bool) (i : ℤ) (c : Bool) (p : ℤ) : Bool :=
  if p < i then w p else if p = i+1 then c else false
lemma lowFuture_history (n : ℕ) (w : ℤ → Bool) (i p : ℤ) (c : Bool) (hp : p ≤ i) :
    history n (lowFuture w i c) p = history n w p := by
  funext j
  dsimp [history, lowFuture]
  rw [if_pos (by omega)]
lemma lowFuture_noHigh (k : ℕ) (hk : 2 ≤ k) (w : ℤ → Bool) (i p : ℤ) (c : Bool)
    (hp : i ≤ p) : ¬Statement.high k (lowFuture w i c) p := by
  intro hh
  have h0 := hh 0 (by omega)
  have h1 := hh 1 (by omega)
  simp only [Nat.cast_zero, sub_zero, lowFuture, if_neg (by omega : ¬ p < i)] at h0
  have he : p = i+1 := by
    by_contra hn
    simp [hn] at h0
  subst p
  simp [lowFuture] at h1
lemma lowFuture_mem (K n : ℕ) (d : ℝ) (hK : 2 ≤ K) (hKn : K ≤ n)
    (w : ℤ → Bool) (hw : w∈Statement.lowerLanguage K n d) (i : ℤ) (c : Bool) :
    lowFuture w i c∈Statement.lowerLanguage K n d := by
  constructor
  · intro p
    by_cases hp : p < i
    · intro hh
      apply hw.1 p
      intro j hj
      have hjj := hh j hj
      simpa [lowFuture, show p-(j:ℤ) < i by omega] using hjj
    · exact lowFuture_noHigh (K+1) (by omega) w i p c (by omega)
  · intro p hh
    by_cases hp : p < i
    · have hhigh : Statement.high K w p := by
        intro j hj
        have hjj := hh j hj
        simpa [lowFuture, show p-(j:ℤ) < i by omega] using hjj
      rw [←memoryLow_history, lowFuture_history n w i p c (by omega), memoryLow_history]
      exact hw.2 p hhigh
    · exact False.elim (lowFuture_noHigh K hK w i p c (by omega) hh)
lemma allow_false (K n : ℕ) (d : ℝ) (hK : 2 ≤ K) (hKn : K ≤ n)
    (v : Vertex (Statement.lowerLanguage K n d) n) :
    graphAllowed (Statement.lowerLanguage K n d) n v false := by
  obtain ⟨w,hw,i,hi⟩ := v.property
  exact ⟨lowFuture w i false, lowFuture_mem K n d hK hKn w hw i false, i,
    (lowFuture_history n w i i false le_rfl).trans hi, by simp [lowFuture]⟩
lemma allow_after_false (K n : ℕ) (d : ℝ) (hK : 2 ≤ K) (hKn : K ≤ n)
    (v : Vertex (Statement.lowerLanguage K n d) n) (c : Bool) :
    graphAllowed (Statement.lowerLanguage K n d) n
      (graphNext (Statement.lowerLanguage K n d) n v false) c := by
  obtain ⟨w,hw,i,hi⟩ := v.property
  let u := lowFuture w i c
  have hu : u∈Statement.lowerLanguage K n d := lowFuture_mem K n d hK hKn w hw i c
  have hv : vertexAt _ n u hu i=v := by
    apply Subtype.ext
    exact (lowFuture_history n w i i c le_rfl).trans hi
  have hi0 : u i=false := by simp [u,lowFuture]
  rw [←hv, ←hi0, graphNext_at]
  exact ⟨u,hu,i+1,rfl,by simp [u,lowFuture]⟩
lemma vertex_nonempty (K n : ℕ) (d : ℝ) (hK : 2 ≤ K) :
    Nonempty (Vertex (Statement.lowerLanguage K n d) n) := by
  have hw : (fun _ : ℤ => false)∈Statement.lowerLanguage K n d := by
    constructor
    · intro i hh; have he := hh 0 (by omega); simp at he
    · intro i hh; have he := hh 0 (by omega); simp at he
  exact ⟨vertexAt _ n _ hw 0⟩
end
end D5.S1.Digit.Infinite.ResetCodebook.Spectral
