/- GID: D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/ResetCodebook
   generality: G
   anchors: []
   utility: none
   digest: Positive reset blocks tile one bilateral letter realization with exact guards. -/

import D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion
import Mathlib.Topology.Sequences

set_option autoImplicit false

namespace D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ResetCodebook

open D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource
open D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Bilateral
open D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Completion
open D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.StrictSupply
open D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ClosedSupply
open D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Operations
open D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion

def forwardCut (W : ℤ → List CuLetter) : ℕ → ℤ
  | 0 => 0
  | n+1 => forwardCut W n + (W (n : ℤ)).length

def backwardCut (W : ℤ → List CuLetter) : ℕ → ℤ
  | 0 => 0
  | n+1 => backwardCut W n + (W (-((n : ℤ)+1))).length

/-- The zero boundary is fixed; negative blocks are summed toward the past. -/
def blockCut (W : ℤ → List CuLetter) : ℤ → ℤ
  | .ofNat n => forwardCut W n
  | .negSucc n => -backwardCut W (n+1)

/-- Positive block lengths produce one actual bilateral concatenation, including
variable letter lengths. The cuts and every letter of every block are fixed. -/
theorem positive_block_tiling (W : ℤ → List CuLetter)
    (positive : ∀ j, 0 < (W j).length) :
    blockCut W 0 = 0 ∧
    (∀ j, blockCut W (j + 1) = blockCut W j + (W j).length) ∧
    StrictMono (blockCut W) ∧
    ∃ ω : ℤ → CuLetter, ∀ j (k : Fin (W j).length),
      ω (blockCut W j + (k : ℕ)) = (W j)[k] := by
  classical
  have zero : blockCut W 0 = 0 := rfl
  have step (j : ℤ) : blockCut W (j + 1) = blockCut W j + (W j).length := by
    cases j with
    | ofNat n => rfl
    | negSucc n =>
      cases n with
      | zero => simp [blockCut,forwardCut,backwardCut]
      | succ n =>
        have a : (Int.negSucc (n + 1) + 1) = Int.negSucc n := by omega
        rw [a]
        simp only [blockCut,backwardCut]
        have e : -(((n+1 : ℕ) : ℤ)+1) = Int.negSucc (n+1) := by omega
        rw [e]
        ring
  have mono : StrictMono (blockCut W) := strictMono_int_of_lt_succ (by
    intro j; rw [step]; have hp := positive j; exact lt_add_of_pos_right _ (by exact_mod_cast hp))
  have right (n : ℕ) : (n : ℤ) ≤ blockCut W n := by
    induction n with
    | zero => simp [zero]
    | succ n ih =>
      rw [Nat.cast_add, Nat.cast_one, step]
      have hp := positive (n : ℤ); omega
  have left (n : ℕ) : blockCut W (-(n : ℤ)) ≤ -(n : ℤ) := by
    induction n with
    | zero => simp [zero]
    | succ n ih =>
      have h := step (-((n + 1 : ℕ) : ℤ))
      have hp := positive (-((n + 1 : ℕ) : ℤ))
      have eq : -((n + 1 : ℕ) : ℤ) + 1 = -(n : ℤ) := by omega
      rw [eq] at h; omega
  have locate (i : ℤ) : ∃ j, blockCut W j ≤ i ∧ i < blockCut W (j + 1) := by
    have ne : ∃ j, blockCut W j ≤ i := by
      refine ⟨-((-i).toNat : ℤ), (left _).trans ?_⟩; omega
    have bd : ∃ b : ℤ, ∀ j, blockCut W j ≤ i → j ≤ b := by
      refine ⟨(i.toNat : ℤ), ?_⟩
      intro j hj
      by_cases h : 0 ≤ j
      · have hh := right j.toNat; have eq : (j.toNat : ℤ) = j := Int.toNat_of_nonneg h
        rw [eq] at hh; omega
      · omega
    obtain ⟨j,hj,hmax⟩ := Int.exists_greatest_of_bdd bd ne
    refine ⟨j,hj,?_⟩
    by_contra hn
    have h := hmax (j+1) (by omega); omega
  let index : ℤ → ℤ := fun i => Classical.choose (locate i)
  have spec (i : ℤ) : blockCut W (index i) ≤ i ∧ i < blockCut W (index i + 1) :=
    Classical.choose_spec (locate i)
  let ω : ℤ → CuLetter := fun i => (W (index i))[(i-blockCut W (index i)).toNat]?.getD .u
  refine ⟨zero,step,mono,ω,?_⟩
  intro j k
  have unique : index (blockCut W j + (k : ℕ)) = j := by
    have h := spec (blockCut W j + (k : ℕ))
    have within : blockCut W j ≤ blockCut W j + (k : ℕ) ∧
        blockCut W j + (k : ℕ) < blockCut W (j+1) := by rw [step]; constructor <;> omega
    apply le_antisymm
    · by_contra hn
      have hh := mono.monotone (show j+1 ≤ index (blockCut W j + (k : ℕ)) by omega)
      omega
    · by_contra hn
      have hh := mono.monotone (show index (blockCut W j + (k : ℕ))+1 ≤ j by omega)
      omega
  dsimp [ω]; rw [unique]
  simp [List.getElem?_eq_getElem k.isLt]

/-- The original literal affine supplier fixes the gain on every return prefix. -/
theorem execute_seed_difference (xs : List Return) (x y : ℝ) :
    execute .high xs y - execute .high xs x = g ^ listWeight xs * (y-x) := by
  let sourceFacts := paired_source_reconstruction .high .original xs
  let ext := sourceFacts.2.2.2.2.2.2.2.2.2.1
  have len : (externalWord .high xs).length = listWeight xs := by
    have h := sourceFacts.2.2.2.2.1
    simp [observedPrefix,stem,block,U,C,anchor,observationOffset] at h
    omega
  have ev : Even (listWeight xs) := by
    clear sourceFacts ext len
    induction xs with
    | nil => exact ⟨0,rfl⟩
    | cons a xs ih => obtain ⟨q,hq⟩ := ih; refine ⟨3*a.m+10*a.r+q,?_⟩; simp only [listWeight]; omega
  simp only [sign,one_mul] at ext
  have affine := literal_source_geometry.2.2.2.1 (externalWord .high xs) (c0+x) (y-x)
  rw [show c0+x+(y-x)=c0+y by ring, ext xs y, ext xs x, len, ev.neg_pow] at affine
  linarith

/-- Transfer a weak original word using its exact weighted seed difference. -/
theorem exact_guard_gain (K N : ℕ) (d B : ℝ) (model : Model) (xs : List Return)
    (weak : GuardTrace K d false .high xs (initial .high model))
    (weight : listWeight xs = N) (above : initial .high model < B)
    (E : ℝ) (raised : B ≤ E) :
    GuardTrace K (d + (B-initial .high model)*g^N) false .high xs E ∧
    aSide .high < execute .high xs E := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)
  have gp : 0 < g := by dsimp [g,t]; nlinarith [Real.sqrt_nonneg (5 : ℝ)]
  have g1 : g < 1 := by dsimp [g,t]; nlinarith [Real.sqrt_nonneg (5 : ℝ)]
  have weightAppend (as bs : List Return) : listWeight (as++bs) =
      listWeight as + listWeight bs := by
    induction as with
    | nil => simp [listWeight]
    | cons a as ih => simp only [List.cons_append,listWeight,ih]; omega
  constructor
  · apply (uniform_guard_trace_iff_split K _ false .high xs E).mpr
    intro before a after split
    have original := (uniform_guard_trace_iff_split K d false .high xs _).mp weak
      before a after split
    refine ⟨original.1,?_⟩
    intro high
    have bound : listWeight before ≤ N := by
      rw [split,weightAppend,listWeight] at weight; omega
    have contracted : g^N ≤ g^listWeight before :=
      pow_le_pow_of_le_one gp.le g1.le bound
    have gain : (B-initial .high model)*g^N ≤
        execute .high before E - execute .high before (initial .high model) := by
      rw [execute_seed_difference]
      calc
        _ ≤ (B-initial .high model)*g^listWeight before :=
          mul_le_mul_of_nonneg_left contracted (sub_pos.mpr above).le
        _ ≤ g^listWeight before*(E-initial .high model) := by
          have hh := mul_le_mul_of_nonneg_left
            (show B-initial .high model ≤ E-initial .high model by linarith)
            (pow_pos gp (listWeight before)).le
          simpa only [mul_comm] using hh
    have old := original.2 high
    simp only [Bool.false_eq_true,if_false] at old ⊢
    linarith
  · have base := ((actual_complete_boundary_geometry model xs).1 .high xs.length).1
    simp only [List.take_length] at base
    have difference := execute_seed_difference xs (initial .high model) E
    have positive := mul_pos (pow_pos gp (listWeight xs))
      (show 0 < E-initial .high model by linarith)
    linarith

set_option maxHeartbeats 1000000 in
-- One exact guard transfer is reused at each reset boundary.
/-- One original reset supports all finite joint choices at the exact high
margin and tiles every two-sided choice without imposing a source hypothesis. -/
theorem reset_codebook_construction (o : Ownership) (b : ℝ) (K : ℕ)
    (hK : 2 ≤ K)
    (hqb : lam-g^2*chi^K*hSide .high < b)
    (hbp : b < lam-g^2*chi^K*(aSide .high/(1-rho*chi^K))) :
    ∃ R : Return, R.r = 1 ∧ ∀ (sourceModel : Model) (N : ℕ), 0 < N →
    let d := (lam-b)/g^2/chi^K
    let B := hSide .high-rho^R.m*(hSide .high-chi*aSide .high)
    let delta := B-initial .high sourceModel
    let gamma := delta*g^N
    let V := {xs : List Return //
      GuardTrace K d false .high xs (initial .high sourceModel) ∧ listWeight xs=N}
    0 < delta ∧ 0 < gamma ∧
    (∀ (targetModel : Model) (words : List V),
      let execution := resetConcatenation R (words.map Subtype.val)
      GuardTrace K (d+gamma) false .high execution (initial .high targetModel) ∧
      ActualPairSupply targetModel o
        (b-min (b-actualAutomaticCost K) (g^2*chi^K*gamma)/2) .strict execution) ∧
    (∃ n : ℕ, K ≤ n ∧ hSide .high*rho^n < chi^(K-1)*gamma) ∧
    (∀ choices : ℤ → V,
      let W := fun j => executionWord (R::(choices j).val)
      blockCut W 0 = 0 ∧
      (∀ j, blockCut W (j+1)=blockCut W j+(W j).length) ∧
      StrictMono (blockCut W) ∧
      ∃ ω : ℤ → CuLetter, ∀ j (k : Fin (W j).length),
        ω (blockCut W j+(k : ℕ))=(W j)[k]) := by
  obtain ⟨R,hr,hB,hstrict,hweak,htransfer,hweight,hfirst⟩ :=
    actual_reset_first_return o b K hK hqb hbp
  refine ⟨R,hr,?_⟩
  intro sourceModel N hN
  dsimp only
  let d := (lam-b)/g^2/chi^K
  let B := hSide .high-rho^R.m*(hSide .high-chi*aSide .high)
  let delta := B-initial .high sourceModel
  let gamma := delta*g^N
  let V := {xs : List Return //
    GuardTrace K d false .high xs (initial .high sourceModel) ∧ listWeight xs=N}
  have above : initial .high sourceModel < B := by
    apply lt_of_le_of_lt _ hB
    cases sourceModel
    · exact (le_max_left _ _).trans (le_max_left _ _)
    · exact (le_max_right _ _).trans (le_max_left _ _)
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)
  have gp : 0 < g := by dsimp [g,t]; nlinarith [Real.sqrt_nonneg (5 : ℝ)]
  have g1 : g < 1 := by dsimp [g,t]; nlinarith [Real.sqrt_nonneg (5 : ℝ)]
  have rp : 0 < rho := pow_pos gp 6
  have r1 : rho < 1 := pow_lt_one₀ gp.le g1 (by decide : (6 : ℕ) ≠ 0)
  have dp : 0 < delta := sub_pos.mpr above
  have gap : 0 < gamma := mul_pos dp (pow_pos gp N)
  have cp : 0 < chi := pow_pos gp 20
  have Hp : 0 < hSide .high := by dsimp [hSide]; linarith
  have appendTrace (as bs : List Return) (z : ℝ) :
      GuardTrace K (d+gamma) false .high (as++bs) z ↔
      GuardTrace K (d+gamma) false .high as z ∧
      GuardTrace K (d+gamma) false .high bs (execute .high as z) := by
    induction as generalizing z with
    | nil => simp [GuardTrace,execute]
    | cons a as ih => simp only [List.cons_append,GuardTrace,execute,ih]; tauto
  have joint (words : List V) (E : ℝ) (hE : aSide .high < E) :
      GuardTrace K (d+gamma) false .high
        (resetConcatenation R (words.map Subtype.val)) E := by
    induction words generalizing E with
    | nil => trivial
    | cons xs words ih =>
      have improved := exact_guard_gain K N d B sourceModel xs.val
        xs.property.1 xs.property.2 above (returnMap .high R E) (hweak E hE.le)
      change GuardTrace K (d+gamma) false .high
        ((R::xs.val)++resetConcatenation R (words.map Subtype.val)) E
      apply (appendTrace _ _ _).mpr
      refine ⟨⟨by rw [hr]; omega,?_,improved.1⟩,?_⟩
      · intro hk; omega
      · apply ih
        simpa only [execute] using improved.2
  refine ⟨dp,gap,?_,?_,?_⟩
  · intro targetModel words
    let execution := resetConcatenation R (words.map Subtype.val)
    have tr := joint words (initial .high targetModel)
      ((actual_complete_boundary_geometry targetModel []).1 .high 0).1
    refine ⟨tr,?_⟩
    let scale := g^2*chi^K
    let eps := min (b-actualAutomaticCost K) (scale*gamma)/2
    have sp : 0 < scale := mul_pos (pow_pos gp 2) (pow_pos cp K)
    have autop : 0 < b-actualAutomaticCost K :=
      sub_pos.mpr ((actual_automatic_cost_envelope K hK).1.trans hqb)
    have ep : 0 < eps := div_pos (lt_min autop (mul_pos sp gap)) (by norm_num)
    have ea : eps < b-actualAutomaticCost K := by
      have hm := min_le_left (b-actualAutomaticCost K) (scale*gamma)
      change min (b-actualAutomaticCost K) (scale*gamma)/2 < b-actualAutomaticCost K
      linarith
    have eg : eps < scale*gamma := by
      have hm := min_le_right (b-actualAutomaticCost K) (scale*gamma)
      change min (b-actualAutomaticCost K) (scale*gamma)/2 < scale*gamma
      have pos := mul_pos sp gap
      linarith
    apply actual_capped_strict_supply_of_high_costs targetModel o K hK (b-eps)
      (by linarith) execution
    · intro a ha
      obtain ⟨before,after,split⟩ := List.mem_iff_append.mp ha
      exact ((uniform_guard_trace_iff_split K _ false .high execution _).mp tr
        before a after split).1
    · intro before a after split high
      have hg := ((uniform_guard_trace_iff_split K _ false .high execution _).mp tr
        before a after split).2 high
      simp only [Bool.false_eq_true,if_false] at hg
      have eq : d*scale=lam-b := by dsimp [d,scale]; field_simp
      have bound := mul_le_mul_of_nonneg_right hg sp.le
      change lam-scale*execute .high before (initial .high targetModel) < b-eps
      nlinarith
  · have ep := mul_pos (pow_pos cp (K-1)) gap
    obtain ⟨m,hm⟩ := exists_pow_lt_of_lt_one (div_pos ep Hp) r1
    refine ⟨max K m,le_max_left _ _,?_⟩
    have pm : rho^(max K m) ≤ rho^m :=
      pow_le_pow_of_le_one rp.le r1.le (le_max_right _ _)
    have bound := mul_le_mul_of_nonneg_left pm Hp.le
    have small := (lt_div_iff₀ Hp).mp hm
    nlinarith
  · intro choices
    apply positive_block_tiling
    intro j
    have hp := R.r_pos
    simp only [executionWord,List.length_append,List.length_replicate]
    omega

def blockWindow (W : ℤ → List CuLetter) (a : ℤ) : ℕ → List CuLetter
  | 0 => []
  | n+1 => W a ++ blockWindow W (a+1) n

/-- Finite block windows respect the same integer cuts as the bilateral tiling. -/
theorem block_window_positions (W : ℤ → List CuLetter)
    (positive : ∀ j, 0 < (W j).length) (a : ℤ) (n : ℕ) :
    ((blockWindow W a n).length : ℤ) = blockCut W (a+n)-blockCut W a ∧
    ∀ j : ℕ, j < n → ∀ k : ℕ, k < (W (a+(j : ℤ))).length →
      (blockWindow W a n)[(blockCut W (a+(j : ℤ))-blockCut W a).toNat+k]?.getD .u =
        (W (a+(j : ℤ)))[k]?.getD .u := by
  obtain ⟨_,step,mono,_⟩ := positive_block_tiling W positive
  induction n generalizing a with
  | zero => simp [blockWindow]
  | succ n ih =>
    have tail := ih (a+1)
    constructor
    · simp only [blockWindow,List.length_append,Nat.cast_add]
      rw [tail.1]
      have idx : a+((n+1 : ℕ) : ℤ) = (a+1)+(n : ℤ) := by omega
      simp only [Nat.cast_add] at idx
      rw [idx]
      have st := step a
      omega
    · intro j hj k hk
      cases j with
      | zero =>
        simp only [Nat.cast_zero,add_zero,sub_self,Int.toNat_zero,Nat.zero_add,
          blockWindow]
        have hka : k < (W a).length := by simpa using hk
        rw [List.getElem?_append_left hka]
      | succ j =>
        have idx : a+((j+1 : ℕ) : ℤ) = (a+1)+(j : ℕ) := by omega
        have ge : blockCut W (a+1) ≤ blockCut W ((a+1)+(j : ℕ)) :=
          mono.monotone (by omega)
        have offset :
            (blockCut W (a+((j+1 : ℕ) : ℤ))-blockCut W a).toNat =
            (W a).length+(blockCut W ((a+1)+(j : ℕ))-blockCut W (a+1)).toNat := by
          rw [idx,step] at *; omega
        rw [idx] at hk
        have hh := tail.2 j (by omega) k hk
        rw [offset]
        simp only [blockWindow,Nat.add_assoc]
        rw [List.getElem?_append_right (Nat.le_add_right _ _)]
        simp only [Nat.add_sub_cancel_left]
        simpa only [idx] using hh

open Filter Topology in
set_option maxHeartbeats 1000000 in
-- Finite windows converge along a compact-language subsequence.
/-- If all finite windows use a common closed auxiliary guard, every two-sided
choice has a single realization with that same guard and the prescribed cuts. -/
theorem compact_block_tiling (K : ℕ) (d : ℝ) (hK : 1 ≤ K)
    (W : ℤ → List CuLetter) (positive : ∀ j, 0 < (W j).length)
    (windows : ∀ a n, uPadding (blockWindow W a n) ∈ AuxiliaryLanguage K d) :
    ∃ ω ∈ AuxiliaryLanguage K d, ∀ j (k : Fin (W j).length),
      ω (blockCut W j+(k : ℕ))=(W j)[k] := by
  classical
  rcases bilateral_past_state with ⟨_,_,_,_,_,_,_,_,_,compact,_,shift⟩
  let seq : ℕ → ℤ → CuLetter := fun q i =>
    uPadding (blockWindow W (-(q : ℤ)) (2*q+1)) (i-blockCut W (-(q : ℤ)))
  have member (q : ℕ) : seq q ∈ AuxiliaryLanguage K d := by
    exact (shift _ (-blockCut W (-(q : ℤ))) K d).mp
      (windows (-(q : ℤ)) (2*q+1))
  obtain ⟨ω,hω,f,hf,hlim⟩ := (compact K d hK).2.tendsto_subseq member
  refine ⟨ω,hω,?_⟩
  intro j k
  have eventually : ∀ᶠ q : ℕ in atTop,
      seq q (blockCut W j+(k : ℕ))=(W j)[k] := by
    filter_upwards [eventually_ge_atTop j.natAbs] with q hq
    let t := (j+(q : ℤ)).toNat
    have tcast : (t : ℤ)=j+(q : ℤ) := by dsimp [t]; omega
    have tbound : t < 2*q+1 := by
      have hj : j ≤ (j.natAbs : ℤ) := Int.le_natAbs
      have hn : -(j.natAbs : ℤ) ≤ j := by
        have h : -j ≤ ((-j).natAbs : ℤ) := Int.le_natAbs
        simpa using (neg_le_neg h)
      omega
    have eq : -(q : ℤ)+(t : ℤ)=j := by omega
    have pos := block_window_positions W positive (-(q : ℤ)) (2*q+1)
    have hp := pos.2 t tbound k.val (by simpa only [eq] using k.isLt)
    simp only [eq] at hp
    have nonneg : 0 ≤ blockCut W j-blockCut W (-(q : ℤ)) := by
      have m := (positive_block_tiling W positive).2.2.1.monotone
        (show -(q : ℤ) ≤ j by
          have h : -j ≤ ((-j).natAbs : ℤ) := Int.le_natAbs
          have hn : -(j.natAbs : ℤ) ≤ j := by simpa using (neg_le_neg h)
          omega)
      omega
    have index : (blockCut W j+(k : ℕ)-blockCut W (-(q : ℤ))).toNat =
        (blockCut W j-blockCut W (-(q : ℤ))).toNat+k.val := by omega
    dsimp [seq]
    rw [uPadding,if_pos (by omega),index]
    simpa only [List.getElem?_eq_getElem k.isLt,Option.getD_some] using hp
  have stable := hf.tendsto_atTop.eventually eventually
  have equalLimit : Tendsto (fun q => seq (f q) (blockCut W j+(k : ℕ))) atTop
      (𝓝 ((W j)[k])) := tendsto_const_nhds.congr' (by
        filter_upwards [stable] with q hq; exact hq.symm)
  exact tendsto_nhds_unique ((continuous_apply _).tendsto ω |>.comp hlim) equalLimit

/-- The original lower graph checks the current Kth c against the zero-seed past. -/
def LowerMemoryLanguage (n K : ℕ) (d : ℝ) : Set (ℤ → CuLetter) :=
  {ω | (∀ i : ℤ, ¬ ∀ k : Fin (K+1), ω (i+(k : ℕ))=.c) ∧
    ∀ i : ℤ, (∀ k : Fin K, ω (i-(k : ℕ))=.c) →
      chi^(K-1)*d < finitePast ω i n 0}

/-- A common auxiliary margin survives the original zero-seed memory estimate. -/
theorem uniform_guard_lower_memory (ω : ℤ → CuLetter) (n K : ℕ) (d gamma : ℝ)
    (guard : ω ∈ AuxiliaryLanguage K (d+gamma))
    (small : hSide .high*rho^n < chi^(K-1)*gamma) :
    ω ∈ LowerMemoryLanguage n K d := by
  rcases bilateral_past_state with ⟨difference,contraction,bounds,_,transition,_⟩
  have unroll (i : ℤ) (m : ℕ) :
      pastState ω i = finitePast ω i m (pastState ω (i-(m : ℤ))) := by
    induction m generalizing i with
    | zero => simp [finitePast]
    | succ m ih =>
      have step := transition ω (i-1)
      rw [show i-1+1=i by omega,ih (i-1)] at step
      simpa only [finitePast,show i-1-(m : ℤ)=i-((m+1 : ℕ) : ℤ) by omega] using step
  have lower (i : ℤ) : pastState ω i ≤ finitePast ω i n 0+hSide .high*rho^n := by
    have diff := difference ω i n 0 (pastState ω (i-(n : ℤ)))
    rw [← unroll i n,sub_zero] at diff
    have bound := mul_le_mul (contraction ω i n).2 (bounds ω (i-(n : ℤ))).2
      (bounds ω (i-(n : ℤ))).1 (by
        have hg := (bounds ω (i-(n : ℤ))).1
        exact (contraction ω i n).1.trans (contraction ω i n).2)
    nlinarith
  refine ⟨guard.1,?_⟩
  intro i high
  have hg := guard.2 i high
  have lo := lower i
  nlinarith

def choiceWindow {V : Type*} (choices : ℤ → V) (a : ℤ) : ℕ → List V
  | 0 => []
  | n+1 => choices a :: choiceWindow choices (a+1) n

set_option maxHeartbeats 1000000 in
-- The compact realization consumes exact finite reset guards before choosing memory.
/-- Original weak codebooks admit a single bilateral reset concatenation for
every two-sided choice, at the exact before-Kth-c margin and in one lower graph. -/
theorem bilateral_reset_codebook (o : Ownership) (b : ℝ) (K : ℕ)
    (hK : 2 ≤ K)
    (hqb : lam-g^2*chi^K*hSide .high < b)
    (hbp : b < lam-g^2*chi^K*(aSide .high/(1-rho*chi^K))) :
    ∃ R : Return, R.r=1 ∧ ∀ (sourceModel : Model) (N : ℕ), 0 < N →
    let d := (lam-b)/g^2/chi^K
    let B := hSide .high-rho^R.m*(hSide .high-chi*aSide .high)
    let delta := B-initial .high sourceModel
    let gamma := delta*g^N
    let V := {xs : List Return //
      GuardTrace K d false .high xs (initial .high sourceModel) ∧ listWeight xs=N}
    0 < delta ∧ 0 < gamma ∧ ∃ n : ℕ, K ≤ n ∧
      hSide .high*rho^n < chi^(K-1)*gamma ∧
      ∀ choices : ℤ → V,
        let W := fun j => executionWord (R::(choices j).val)
        ∃ ω : ℤ → CuLetter,
          ω ∈ AuxiliaryLanguage K (d+gamma) ∧ ω ∈ LowerMemoryLanguage n K d ∧
          (∀ j (k : Fin (W j).length), ω (blockCut W j+(k : ℕ))=(W j)[k]) ∧
          (∀ j, GuardTrace K (d+gamma) false .high (R::(choices j).val)
            (pastState ω (blockCut W j))) := by
  obtain ⟨R,hr,finite⟩ := reset_codebook_construction o b K hK hqb hbp
  refine ⟨R,hr,?_⟩
  intro sourceModel N hN
  dsimp only
  let d := (lam-b)/g^2/chi^K
  let B := hSide .high-rho^R.m*(hSide .high-chi*aSide .high)
  let delta := B-initial .high sourceModel
  let gamma := delta*g^N
  let V := {xs : List Return //
    GuardTrace K d false .high xs (initial .high sourceModel) ∧ listWeight xs=N}
  obtain ⟨dp,gp,joint,⟨n,hn,small⟩,tiles⟩ := finite sourceModel N hN
  refine ⟨dp,gp,n,hn,small,?_⟩
  intro choices
  let W := fun j => executionWord (R::(choices j).val)
  have positive (j : ℤ) : 0 < (W j).length := by
    dsimp [W]; simp only [executionWord,List.length_append,List.length_replicate]
    have h := R.r_pos; omega
  have appendWord (as bs : List Return) : executionWord (as++bs)=
      executionWord as++executionWord bs := by
    induction as with
    | nil => rfl
    | cons a as ih => simp [executionWord,ih,List.append_assoc]
  have window (a : ℤ) (m : ℕ) : blockWindow W a m =
      executionWord (resetConcatenation R ((choiceWindow choices a m).map Subtype.val)) := by
    induction m generalizing a with
    | zero => rfl
    | succ m ih => simp only [blockWindow,choiceWindow,List.map_cons,
        resetConcatenation,appendWord,ih]; rfl
  have guards (a : ℤ) (m : ℕ) : uPadding (blockWindow W a m) ∈
      AuxiliaryLanguage K (d+gamma) := by
    rw [window]
    have tr := (joint .original (choiceWindow choices a m)).1
    exact (auxiliary_lower_padding K (d+gamma) .original _ (by omega) tr).2.2.1
  obtain ⟨ω,hω,letters⟩ := compact_block_tiling K (d+gamma) (by omega) W positive guards
  refine ⟨ω,hω,uniform_guard_lower_memory ω n K d gamma hω small,letters,?_⟩
  intro j
  apply occurrence_run_guards K (d+gamma) (by omega) ω hω (blockCut W j)
  intro k _
  exact letters j k

end D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ResetCodebook
