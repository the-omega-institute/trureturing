/- GID: D5/S3/Quantum/Analysis/RefinedBMV84
   generality: G
   mirror-B: D5/B/S3/Quantum/Analysis/RefinedBMV84
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: An exact Gram certificate for the refined BMV trace bound at bidegree (8,4). -/

import D5.S3.Quantum.Analysis.RefinedBMV44
import Mathlib.Algebra.Star.Rat
import Mathlib.Data.List.Lex
import Mathlib.Data.Rat.BigOperators
import Mathlib.LinearAlgebra.Matrix.Notation

/-! # The refined BMV lower bound at bidegree (8,4)

The Hermitian-part comparison and three exact rational Gram matrices
bound the balanced fourth trace by the ordered word mean.
-/

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace RefinedBMV
namespace Algebra84

open Algebra44
open private Algebra44.realTrace_adjoint Algebra44.realTrace_mul_comm Algebra44.realTrace_add_four
  evalWord_reverse from D5.S3.Quantum.Analysis.RefinedBMV44
open private evalWord_append43 evalWord_block43 from D5.S3.Quantum.Analysis.RefinedBMV43

private abbrev Word := List Bool
private abbrev Terms := List (ℚ × Word)

private def rotations (w : Word) : List Word :=
  (List.range w.length).map w.rotate

private def representative (w : Word) : Word :=
  ((rotations w ++ rotations w.reverse).min?).getD w

private def addTerm (u : ℚ × Word) : Terms → Terms
  | [] => [u]
  | t :: ts =>
    if t.2 = u.2 then (u.1 + t.1, t.2) :: ts else t :: addTerm u ts

private def coefficients : Terms → Terms
  | [] => []
  | t :: ts => addTerm (t.1, representative t.2) (coefficients ts)

private def scaleTerms (c : ℚ) (p : Terms) : Terms :=
  p.map fun t => (c * t.1, t.2)

private def gramTerms {k : ℕ} (G : Matrix (Fin k) (Fin k) ℚ) (l : Word)
    (w : Fin k → Word) : Terms :=
  (List.finRange k).flatMap fun i =>
    (List.finRange k).map fun j => (G i j, (w i).reverse ++ l ++ w j ++ l)

private def aRun (i : ℕ) : Word := List.replicate i true
private def aGap (i : ℕ) : Word := aRun i ++ [false]

private def wordWithTwoB (i j k : ℕ) : Word := aGap i ++ aGap j ++ aRun k
private def wordWithOneB (i j : ℕ) : Word := aGap i ++ aRun j

private def w₀ : Fin 15 → Word :=
  ![wordWithTwoB 0 0 4, wordWithTwoB 0 1 3, wordWithTwoB 0 2 2,
    wordWithTwoB 0 3 1, wordWithTwoB 0 4 0, wordWithTwoB 1 0 3,
    wordWithTwoB 1 1 2, wordWithTwoB 1 2 1, wordWithTwoB 1 3 0,
    wordWithTwoB 2 0 2, wordWithTwoB 2 1 1, wordWithTwoB 2 2 0,
    wordWithTwoB 3 0 1, wordWithTwoB 3 1 0, wordWithTwoB 4 0 0]

private def w₁ : Fin 10 → Word :=
  ![wordWithTwoB 0 0 3, wordWithTwoB 0 1 2, wordWithTwoB 0 2 1,
    wordWithTwoB 0 3 0, wordWithTwoB 1 0 2, wordWithTwoB 1 1 1,
    wordWithTwoB 1 2 0, wordWithTwoB 2 0 1, wordWithTwoB 2 1 0, wordWithTwoB 3 0 0]

private def w₂ : Fin 5 → Word :=
  ![wordWithOneB 0 4, wordWithOneB 1 3, wordWithOneB 2 2, wordWithOneB 3 1,
    wordWithOneB 4 0]

private def shift (i : Bool) : ℕ := if i then 1 else 0

-- Begin at the first B, so the first gap displayed lies between the first and second B.
private def comparatorWord (i j k l : Bool) : Word :=
  [false] ++ aGap (2 + shift j - shift i) ++ aGap (2 + shift k - shift j) ++
    aGap (2 + shift l - shift k) ++ aRun (2 + shift i - shift l)

-- The six rotation classes of the four binary choices have multiplicities 1, 1, 4, 4, 4, 2.
private def comparatorTerms : Terms :=
  [(1, comparatorWord false false false false), (1, comparatorWord true true true true),
    (4, comparatorWord false false false true), (4, comparatorWord true true true false),
    (4, comparatorWord true true false false), (2, comparatorWord true false true false)]

-- For each supplied compressed block (C, G), the full matrix below is 2640000 • C G Cᵀ.
private def G₀ : Matrix (Fin 15) (Fin 15) ℚ :=
  !![36016, 36016, 31000, 30736, -7996, -28885, -29677, -38, -20416, -424, -10824, -20460, -2904, -6072, -6072;
     36016, 36016, 31000, 30736, -7996, -28885, -29677, -38, -20416, -424, -10824, -20460, -2904, -6072, -6072;
     31000, 31000, 151120, 143728, 9000, 7542, 78654, -29380, -116688, 31152, -117480, -116688, -61776, -20592, -20592;
     30736, 30736, 143728, 216064, 97908, 29712, 22980, -54188, -94220, -45672, -145992, -122496, -61248, -24024, -24024;
     -7996, -7996, 9000, 97908, 232376, 3168, -70056, -129832, 87004, -121440, -78144, 5544, -3168, -8184, -8184;
     -28885, -28885, 7542, 29712, 3168, 147744, 146660, 37840, -68112, -62776, -70488, -70752, -29568, -6600, -6600;
     -29677, -29677, 78654, 22980, -70056, 146660, 272712, 42948, -145992, 31944, -106392, -121704, -66528, -12936, -12936;
     -38, -38, -29380, -54188, -129832, 37840, 42948, 148792, -52800, -22704, 44088, -29040, 39600, 2376, 2376;
     -20416, -20416, -116688, -94220, 87004, -68112, -145992, -52800, 213840, -39336, 21120, 144408, 25080, 33264, 33264;
     -424, -424, 31152, -45672, -121440, -62776, 31944, -22704, -39336, 203280, 41184, 38016, -57552, 2376, 2376;
     -10824, -10824, -117480, -145992, -78144, -70488, -106392, 44088, 21120, 41184, 262152, 84480, 128832, -20856, -20856;
     -20460, -20460, -116688, -122496, 5544, -70752, -121704, -29040, 144408, 38016, 84480, 155760, 7392, 33000, 33000;
     -2904, -2904, -61776, -61248, -3168, -29568, -66528, 39600, 25080, -57552, 128832, 7392, 128040, -21648, -21648;
     -6072, -6072, -20592, -24024, -8184, -6600, -12936, 2376, 33264, 2376, -20856, 33000, -21648, 27984, 27984;
     -6072, -6072, -20592, -24024, -8184, -6600, -12936, 2376, 33264, 2376, -20856, 33000, -21648, 27984, 27984]

private def d₀ : Fin 12 → ℚ :=
  ![1 / 36016,
    1 / 2522098014480,
    1 / 9920873284468080,
    1 / 56203562380680370369288080,
    1 / 344371330409678324249293683992859846620,
    4 / 147106516380121045863604114084214403370317862023,
    4 / 917190201113602982383550077228359458517819866266142645,
    1 / 10069171575762932087013893982587614473899463871567962062829130,
    132 / 67553724926149235094670179443452607506943779471708834248520630343,
    11 / 155847649209690378967936214622848597920779802253045312012191385331323,
    55 / 5450461067256831577286969483392351765689345396507000874621520453251606286,
    43753680397670660384178873643255757949972 / 25715065419410649744791948598362934863]

private def F₀ : Matrix (Fin 15) (Fin 12) ℚ :=
  !![36016, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     36016, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     31000, 560217240, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     30736, 527961456, 28051016928, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     -7996, 71502500, 31747006390, 2671492565370730, 0, 0, 0, 0, 0, 0, 0, 0;
     -28885, 145883459, 8425898317, -722532603050213, 5859362101266702730577, 0, 0, 0, 0, 0, 0, 0;
     -29677, 469098683, -17645466041, -704317540204415, 5974686380070093001105, 25106234063998009377203799, 0, 0, 0, 0, 0, 0;
     -38, -132121510, -9371619480, -2021889719247320, 1611459552619838640830, -3623084950773225107401684, 109597106293473258907192019065, 0, 0, 0, 0, 0;
     -20416, -446217376, 5875050602, 1605672817145782, -2528605356713682463548, -7879505741377841264453513, -3824128400475000083727197063, 734995433094756641328557586731216, 0, 0, 0, 0;
     -424, 141889304, -26529839948, -855430447363700, -3513926053566547317440, 12103262259297276499291224, -111870532840355262578449038496, 8252568756322991737901942719952, 2941132829267639346579295334300486, 0, 0, 0;
     -10824, -486951960, -12314557860, -575079422015868, -2817376145178847360548, -7279442597624185150168809, -2692715944048456473180674729, -955390892151287321070865045427972, -20047304232489885586046472144644, 635867843813762446492393279576893366, 0, 0;
     -20460, -446046876, -4124735868, 564803255036988, -2973708008720568972072, -6249382193066581018651113, -47505888368869629554439023737, 222409682592949804811815106198609, 1529326566215359900067953697612217, -269392496667901085683936622771324803, 25715065419410649744791948598362934863, 0;
     -2904, -266862552, -1027865256, 148154140070376, -804220308651622819704, -7770088765976348338818852, 68987329938370603651464788688, -463370546523327278141022076761291, -2554055738735600913450872642156075, 563756638688084450735185974883659387, -33741279606439513532479247623525293705, 2;
     -6072, -69176184, -1542443892, -55436522871180, -403836080562682719600, -2203996037238552498500526, -6345585339047756934430436864, 226551877115292580666806243269743, -948178176257454223805164958805992, -465115992916972905771821315844613975, 4013107093514431893843649512581179421, -1;
     -6072, -69176184, -1542443892, -55436522871180, -403836080562682719600, -2203996037238552498500526, -6345585339047756934430436864, 226551877115292580666806243269743, -948178176257454223805164958805992, -465115992916972905771821315844613975, 4013107093514431893843649512581179421, -1]

private def G₁ : Matrix (Fin 10) (Fin 10) ℚ :=
  !![91410, 91410, 24288, -7260, -60324, -48048, -23100, 2640, -35508, -35508;
     91410, 91410, 24288, -7260, -60324, -48048, -23100, 2640, -35508, -35508;
     24288, 24288, 138336, 12144, -7656, -22704, -115896, -15312, -18744, -18744;
     -7260, -7260, 12144, 94512, -4224, -85800, 13464, -5544, -5016, -5016;
     -60324, -60324, -7656, -4224, 157608, 60720, -12408, -86064, 6336, 6336;
     -48048, -48048, -22704, -85800, 60720, 176352, -17688, 52800, -33792, -33792;
     -23100, -23100, -115896, 13464, -12408, -17688, 138072, -4224, 22440, 22440;
     2640, 2640, -15312, -5544, -86064, 52800, -4224, 148104, -47520, -47520;
     -35508, -35508, -18744, -5016, 6336, -33792, 22440, -47520, 73656, 73656;
     -35508, -35508, -18744, -5016, 6336, -33792, 22440, -47520, 73656, 73656]

private def d₁ : Fin 7 → ℚ :=
  ![66 / 1385,
    22 / 79854945,
    11 / 193989917007,
    11 / 119587523904239679,
    88 / 98918423825177557106229,
    264 / 868281758598794972546113877,
    845790031923557952 / 311991130358377]

private def F₁ : Matrix (Fin 10) (Fin 7) ℚ :=
  !![1385, 0, 0, 0, 0, 0, 0;
     1385, 0, 0, 0, 0, 0, 0;
     368, 691884, 0, 0, 0, 0, 0;
     -110, 73830, 40374612, 0, 0, 0, 0;
     -914, 43923, -4327977, 35543382729, 0, 0, 0;
     -728, -52134, -38680716, 6163209024, 8349100414503, 0, 0;
     -350, -575815, 10195459, -5561427287, -1694426066180, 311991130358377, 0;
     40, -84010, -1583624, -25599292724, 8619281105455, -169418987468217, 2;
     -538, -48839, -2988877, -5272935871, -7636977726889, -71286071445080, -1;
     -538, -48839, -2988877, -5272935871, -7636977726889, -71286071445080, -1]

private def G₂ : Matrix (Fin 5) (Fin 5) ℚ :=
  !![51744, 39864, -2376, -44616, -44616;
     39864, 44616, 0, -42240, -42240;
     -2376, 0, 2376, 0, 0;
     -44616, -42240, 0, 44616, 42240;
     -44616, -42240, 0, 42240, 44616]

private def d₂ : Fin 4 → ℚ :=
  ![66 / 49,
    594 / 56203,
    580932 / 1147,
    1188]

private def F₂ : Matrix (Fin 5) (Fin 4) ℚ :=
  !![196, 0, 0, 0;
     151, 1147, 0, 0;
     -9, 151, 2, 0;
     -169, -649, -1, 1;
     -169, -649, -1, -1]

private def ldlChecks {k r : ℕ} (G : Matrix (Fin k) (Fin k) ℚ)
    (d : Fin r → ℚ) (F : Matrix (Fin k) (Fin r) ℚ) : Bool :=
  (List.finRange r).all (fun t => decide (0 ≤ d t)) &&
    (List.finRange k).all fun i =>
      (List.finRange k).all fun j =>
        decide (G i j = ((List.finRange r).map fun t => d t * (F i t * F j t)).sum)

private theorem ldlChecks_sound {k r : ℕ} {G : Matrix (Fin k) (Fin k) ℚ}
    {d : Fin r → ℚ} {F : Matrix (Fin k) (Fin r) ℚ} (h : ldlChecks G d F = true) :
    (∀ t, 0 ≤ d t) ∧ (∀ i j, G i j = ∑ t, d t * (F i t * F j t)) := by
  simp only [ldlChecks, Bool.and_eq_true, List.all_eq_true, List.mem_finRange, true_implies,
    decide_eq_true_eq, ← Fin.sum_univ_def] at h
  exact h

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
private theorem ldl₀ : ldlChecks G₀ d₀ F₀ = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
private theorem ldl₁ : ldlChecks G₁ d₁ F₁ = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
private theorem ldl₂ : ldlChecks G₂ d₂ F₂ = true := by decide +kernel

private def orderedTerms : Terms := (balancedWords 8 4).map fun w => (1, w)

private def certificateTerms : Terms :=
  gramTerms G₀ [] w₀ ++ gramTerms G₁ [true] w₁ ++ gramTerms G₂ [false] w₂

private def gapTerms : Terms :=
  scaleTerms (16000 / 3) orderedTerms ++ scaleTerms (-165000) comparatorTerms

private def coefficientsVanish (p : Terms) : Bool :=
  (coefficients p).all fun t => decide (t.1 = 0)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
private theorem coefficients84 :
    coefficientsVanish (gapTerms ++ scaleTerms (-1) certificateTerms) = true := by
  simp only [gapTerms, orderedTerms, balancedWords, List.map_cons, List.map_nil,
    List.cons_append, List.nil_append]
  decide +kernel

noncomputable section

private def weightedSum (K : Type*) [Field K] {α M : Type*} [AddCommMonoid M] [Module K M]
    (f : α → M) : List (ℚ × α) → M
  | [] => 0
  | t :: ts => (t.1 : K) • f t.2 + weightedSum K f ts

private theorem weightedSum_eq_map (K : Type*) [Field K] {α M : Type*} [AddCommMonoid M]
    [Module K M] (f : α → M) (p : List (ℚ × α)) :
    weightedSum K f p = (p.map fun t => (t.1 : K) • f t.2).sum := by
  induction p with
  | nil => rfl
  | cons t ts ih => simp only [weightedSum, List.map_cons, List.sum_cons, ih]

private theorem weightedSum_append (K : Type*) [Field K] {α M : Type*} [AddCommMonoid M]
    [Module K M] (f : α → M) (p q : List (ℚ × α)) :
    weightedSum K f (p ++ q) = weightedSum K f p + weightedSum K f q := by
  simp only [weightedSum_eq_map, List.map_append, List.sum_append]

private theorem weightedSum_scale (f : Word → ℝ) (c : ℚ) (p : Terms) :
    weightedSum ℝ f (scaleTerms c p) = (c : ℝ) * weightedSum ℝ f p := by
  simp only [weightedSum_eq_map, scaleTerms, List.map_map, Function.comp_def, Rat.cast_mul,
    smul_eq_mul, mul_assoc, List.sum_map_mul_left]

private theorem weightedSum_flatMap (K : Type*) [Field K] {α β M : Type*} [AddCommMonoid M]
    [Module K M] (f : β → M) (xs : List α) (terms : α → List (ℚ × β)) :
    weightedSum K f (xs.flatMap terms) = (xs.map fun x => weightedSum K f (terms x)).sum := by
  simp only [weightedSum_eq_map, List.flatMap_def, List.map_flatten, List.sum_flatten,
    List.map_map, Function.comp_def]

private theorem weightedSum_addTerm (f : Word → ℝ) (u : ℚ × Word) (p : Terms) :
    weightedSum ℝ f (addTerm u p) = (u.1 : ℝ) • f u.2 + weightedSum ℝ f p := by
  induction p with
  | nil => rfl
  | cons t ts ih =>
    by_cases h : t.2 = u.2
    · rw [addTerm, ite_eq_left h]
      simp only [weightedSum, Rat.cast_add, add_smul, h, add_assoc]
    · simp only [addTerm, if_neg h, weightedSum, ih]
      exact add_left_comm _ _ _

private theorem coefficients_sound (f : Word → ℝ) (hf : ∀ w, f (representative w) = f w)
    (p : Terms) (h : coefficientsVanish p = true) : weightedSum ℝ f p = 0 := by
  have heval : weightedSum ℝ f (coefficients p) = weightedSum ℝ f p := by
    clear h
    induction p with
    | nil => rfl
    | cons t ts ih =>
      simp only [coefficients, weightedSum_addTerm, hf, ih, weightedSum]
  rw [← heval]
  have hz : ∀ t ∈ coefficients p, t.1 = 0 := fun t ht =>
    of_decide_eq_true (List.all_eq_true.mp h t ht)
  generalize coefficients p = terms at hz ⊢
  induction terms with
  | nil => rfl
  | cons t ts ih =>
    simp only [weightedSum, hz t List.mem_cons_self, Rat.cast_zero, zero_smul, zero_add]
    exact ih fun s hs => hz s (List.mem_cons_of_mem t hs)

variable {n : Type*} [Fintype n] [DecidableEq n]
local notation "Mat" => Matrix n n ℂ

private def traceWord (A B : Mat) (w : Word) : ℝ := realTrace (evalWord A B w)

private theorem traceWord_representative (A B : Mat) (hA : A.IsHermitian) (hB : B.IsHermitian)
    (w : Word) : traceWord A B (representative w) = traceWord A B w := by
  unfold representative
  cases h : (rotations w ++ rotations w.reverse).min? with
  | none => rfl
  | some r =>
    simp only [Option.getD_some]
    rcases List.mem_append.mp (List.min?_mem h) with hr | hr
    · obtain ⟨k, _, rfl⟩ := List.mem_map.mp hr
      exact congrArg Complex.re (evalWord_rotate_trace43 A B w k)
    · obtain ⟨k, _, rfl⟩ := List.mem_map.mp hr
      calc
        traceWord A B (w.reverse.rotate k) = traceWord A B w.reverse :=
          congrArg Complex.re (evalWord_rotate_trace43 A B w.reverse k)
        _ = traceWord A B w := by
          unfold traceWord
          rw [evalWord_reverse A B hA hB, Algebra44.realTrace_adjoint]

private def weightedGram {k : ℕ} (G : Matrix (Fin k) (Fin k) ℚ)
    (Z : Fin k → Mat) (L : Mat) : ℂ :=
  ∑ i, ∑ j, (G i j : ℂ) * trace ((Z i)ᴴ * L * Z j * L)

private theorem real_rat_mul (a : ℚ) (z : ℂ) : ((a : ℂ) * z).re = (a : ℝ) * z.re := by
  simp [Complex.mul_re]

private theorem eval_gramTerms (A B : Mat) (hA : A.IsHermitian) (hB : B.IsHermitian)
    {k : ℕ} (G : Matrix (Fin k) (Fin k) ℚ) (l : Word) (w : Fin k → Word) :
    weightedSum ℝ (traceWord A B) (gramTerms G l w) =
      (weightedGram G (fun i => evalWord A B (w i)) (evalWord A B l)).re := by
  change _ = Complex.reCLM _
  rw [gramTerms, weightedSum_flatMap]
  simp only [weightedSum_eq_map, List.map_map, Function.comp_def,
    ← Fin.sum_univ_def, weightedGram, map_sum, Complex.reCLM_apply, real_rat_mul, smul_eq_mul,
    traceWord, realTrace, evalWord_append43, evalWord_reverse A B hA hB, mul_assoc]

private theorem trace_weighted_pair {α : Type*} (f : α → Mat) (p q : List (ℚ × α))
    (L : Mat) :
    trace ((weightedSum ℂ f p)ᴴ * L * weightedSum ℂ f q * L) =
      (p.map fun u => (q.map fun v =>
        ((u.1 * v.1 : ℚ) : ℂ) * trace ((f u.2)ᴴ * L * f v.2 * L)).sum).sum := by
  have right (Z : Mat) (qs : List (ℚ × α)) :
      trace (Z * L * weightedSum ℂ f qs * L) =
        (qs.map fun v => (v.1 : ℂ) * trace (Z * L * f v.2 * L)).sum := by
    induction qs with
    | nil => simp [weightedSum]
    | cons v vs ih =>
      simp only [weightedSum, List.map_cons, List.sum_cons, mul_add, add_mul,
        Matrix.mul_smul, Matrix.smul_mul, trace_add, trace_smul, smul_eq_mul, ih]
  induction p with
  | nil => simp [weightedSum]
  | cons u us ih =>
    have head : trace (((u.1 : ℂ) • f u.2)ᴴ * L * weightedSum ℂ f q * L) =
        (q.map fun v =>
          ((u.1 * v.1 : ℚ) : ℂ) * trace ((f u.2)ᴴ * L * f v.2 * L)).sum := by
      simp only [conjTranspose_smul, star_ratCast, Matrix.smul_mul, trace_smul, smul_eq_mul]
      rw [right]
      simp only [← List.sum_map_mul_left, Rat.cast_mul, mul_assoc]
    simp only [weightedSum, List.map_cons, List.sum_cons, conjTranspose_add, add_mul,
      trace_add, head, ih]

private theorem trace_pair_nonneg (L U : Mat) (hL : L.PosSemidef) :
    0 ≤ (trace (Uᴴ * L * U * L)).re := by
  obtain ⟨S, hS⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hL.nonneg
  rw [star_eq_conjTranspose] at hS
  calc
    0 ≤ (trace (S * (Uᴴ * L * U) * Sᴴ)).re :=
      (Complex.le_def.mp
        ((hL.conjTranspose_mul_mul_same U).mul_mul_conjTranspose_same S).trace_nonneg).1
    _ = (trace (Uᴴ * L * U * L)).re := by
      rw [trace_mul_cycle S (Uᴴ * L * U) Sᴴ, ← hS, trace_mul_comm L]

private theorem weightedGram_nonneg {k r : ℕ} (G : Matrix (Fin k) (Fin k) ℚ)
    (Z : Fin k → Mat) (L : Mat) (hL : L.PosSemidef)
    {d : Fin r → ℚ} {F : Matrix (Fin k) (Fin r) ℚ} (h : ldlChecks G d F = true) :
    0 ≤ (weightedGram G Z L).re := by
  obtain ⟨hd, hG⟩ := ldlChecks_sound h
  let row (t : Fin r) := (List.finRange k).map fun i => (F i t, Z i)
  let U (t : Fin r) := weightedSum ℂ id (row t)
  have htrace (t : Fin r) : trace ((U t)ᴴ * L * U t * L) =
      ∑ i, ∑ j, (F i t : ℂ) * (F j t : ℂ) * trace ((Z i)ᴴ * L * Z j * L) := by
    dsimp only [U]
    rw [trace_weighted_pair]
    simp only [row, List.map_map, Function.comp_def, id_eq, Rat.cast_mul, ← Fin.sum_univ_def]
  have hdecomp : weightedGram G Z L =
      ∑ t, (d t : ℂ) * trace ((U t)ᴴ * L * U t * L) := by
    simp only [weightedGram, hG, Rat.cast_sum, Rat.cast_mul, Finset.sum_mul,
      htrace, Finset.mul_sum]
    calc
      _ = ∑ i, ∑ t, ∑ j, (d t : ℂ) * ((F i t : ℂ) * (F j t : ℂ)) *
          trace ((Z i)ᴴ * L * Z j * L) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.sum_comm]
      _ = _ := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro t _
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        ring
  change 0 ≤ Complex.reCLM (weightedGram G Z L)
  rw [hdecomp, map_sum]
  apply Finset.sum_nonneg
  intro t _
  simp only [Complex.reCLM_apply, real_rat_mul]
  exact mul_nonneg (Rat.cast_nonneg.mpr (hd t)) (trace_pair_nonneg L (U t) hL)

private theorem eval_aRun (A B : Mat) (i : ℕ) : evalWord A B (aRun i) = A ^ i := by
  simpa only [aRun, List.append_nil, evalWord, mul_one] using evalWord_block43 A B i []

private def shiftedFactor (X B : Mat) (i : Bool) : Mat :=
  X ^ (1 + 2 * shift i) * B * X ^ (3 - 2 * shift i)

-- Move the first left power across the trace. Its exponent adds to the last right power.
private theorem shiftedTerm_eval (X B : Mat) (i j k l : Bool) :
    realTrace (shiftedFactor X B i * (shiftedFactor X B j *
      (shiftedFactor X B k * shiftedFactor X B l))) =
      traceWord (X ^ 2) B (comparatorWord i j k l) := by
  simp only [shiftedFactor, mul_assoc]
  rw [Algebra44.realTrace_mul_comm (X ^ (1 + 2 * shift i))]
  unfold traceWord
  apply congrArg realTrace
  simp only [comparatorWord, aGap, evalWord_append43, eval_aRun, evalWord, mul_one, mul_assoc]
  cases i <;> cases j <;> cases k <;> cases l <;>
    norm_num [shift, pow_succ, mul_assoc] <;> noncomm_ring

private theorem realTrace_smul (r : ℝ) (Z : Mat) :
    realTrace (r • Z) = r * realTrace Z := by
  change (trace (r • Z)).re = r * (trace Z).re
  rw [trace_smul]
  exact RCLike.smul_re r (trace Z)

private theorem comparator_eval (X B : Mat) (hX : X.IsHermitian) (hB : B.IsHermitian) :
    weightedSum ℝ (traceWord (X ^ 2) B) comparatorTerms =
      16 * H (X ^ 2) (X * B * X) := by
  have hleft : X ^ 2 * (X * B * X) = shiftedFactor X B true := by
    simp [shiftedFactor, shift, pow_succ, mul_assoc] <;> noncomm_ring
  have hright : (X ^ 2 * (X * B * X))ᴴ = shiftedFactor X B false := by
    simp [shiftedFactor, shift, conjTranspose_mul, conjTranspose_pow, hX.eq, hB.eq,
      pow_succ, mul_assoc] <;> noncomm_ring
  rw [H, hright, hleft, smul_pow, realTrace_smul, Algebra44.realTrace_add_four]
  simp only [comparatorTerms, weightedSum, smul_eq_mul, ← shiftedTerm_eval]
  simp only [pow_succ, pow_zero, one_mul, mul_assoc]
  norm_num <;> ring

private def wordTraceSum (A B : Mat) : ℝ :=
  ((balancedWords 8 4).map (traceWord A B)).sum

private theorem eval_orderedTerms (A B : Mat) :
    weightedSum ℝ (traceWord A B) orderedTerms = wordTraceSum A B := by
  simp only [orderedTerms, wordTraceSum, weightedSum_eq_map, List.map_map, Function.comp_def,
    Rat.cast_one, one_smul]

private abbrev wordVector (A B : Mat) {k : ℕ} (w : Fin k → Word) (i : Fin k) : Mat :=
  evalWord A B (w i)

/-- The exact real-trace identity, with all three full Gram blocks scaled by 2640000. -/
private theorem trace_gap84 (X B : Mat) (hX : X.IsHermitian) (hB : B.IsHermitian) :
    let A := X ^ 2
    (16000 / 3) * wordTraceSum A B - 2640000 * H A (X * B * X) =
      (weightedGram G₀ (wordVector A B w₀) 1).re +
        ((weightedGram G₁ (wordVector A B w₁) A).re +
          (weightedGram G₂ (wordVector A B w₂) B).re) := by
  dsimp only
  have hA : (X ^ 2).IsHermitian := by
    change (X ^ 2)ᴴ = X ^ 2
    rw [conjTranspose_pow, hX.eq]
  have h := coefficients_sound (traceWord (X ^ 2) B)
    (traceWord_representative (X ^ 2) B hA hB) _ coefficients84
  simp only [gapTerms, certificateTerms, weightedSum_append, weightedSum_scale,
    eval_gramTerms (X ^ 2) B hA hB, eval_orderedTerms, comparator_eval X B hX hB,
    evalWord, mul_one] at h
  norm_num at h
  linarith only [h]

/-- The shifted Hermitian fourth trace is bounded by the mean of the ordered traces. -/
theorem shifted_bound84 (X B : Mat) (hX : X.PosSemidef) (hB : B.PosSemidef) :
    495 * H (X ^ 2) (X * B * X) ≤
      ((balancedWords 8 4).map fun w => realTrace (evalWord (X ^ 2) B w)).sum := by
  let A := X ^ 2
  have hA : A.PosSemidef := hX.pow 2
  have hgap := trace_gap84 X B hX.isHermitian hB.isHermitian
  have h₀ := weightedGram_nonneg G₀ (wordVector A B w₀) 1 Matrix.PosSemidef.one ldl₀
  have h₁ := weightedGram_nonneg G₁ (wordVector A B w₁) A hA ldl₁
  have h₂ := weightedGram_nonneg G₂ (wordVector A B w₂) B hB ldl₂
  change 495 * H A (X * B * X) ≤ wordTraceSum A B
  change (16000 / 3) * wordTraceSum A B - 2640000 * H A (X * B * X) =
    (weightedGram G₀ (wordVector A B w₀) 1).re +
      ((weightedGram G₁ (wordVector A B w₁) A).re +
        (weightedGram G₂ (wordVector A B w₂) B).re) at hgap
  linarith only [hgap, h₀, h₁, h₂]

end
end Algebra84

open private trace_cycle_power from D5.S3.Quantum.Analysis.RefinedBMVTracePower
open private trace_four_le_symmetrized44 from D5.S3.Quantum.Analysis.RefinedBMV44

/-- The refined BMV product lower bound at bidegree (8,4). -/
theorem product_bound84 {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ)
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    495 * (trace ((A ^ 2 * B) ^ 4)).re ≤
      ((balancedWords 8 4).map fun w => (trace (evalWord A B w)).re).sum := by
  let X := CFC.sqrt A
  let C := X * B * X
  have hX : X.PosSemidef := (CFC.sqrt_nonneg A).posSemidef
  have hsq : X ^ 2 = A := by
    rw [pow_two]
    exact CFC.sqrt_mul_sqrt_self A hA.nonneg
  have hC : C.PosSemidef := by
    simpa only [C, hX.isHermitian.eq] using hB.mul_mul_conjTranspose_same X
  have htrace : trace ((A ^ 2 * B) ^ 4) = trace ((A * C) ^ 4) := by
    rw [← hsq]
    calc
      _ = trace ((X * (X ^ 3 * B)) ^ 4) := congrArg trace (by noncomm_ring)
      _ = trace (((X ^ 3 * B) * X) ^ 4) := trace_cycle_power _ _ 4
      _ = _ := congrArg trace (by dsimp only [C]; noncomm_ring)
  have hcompare := trace_four_le_symmetrized44 A C hA hC
  change (trace ((A * C) ^ 4)).re ≤ Algebra44.H A C at hcompare
  have hgram := Algebra84.shifted_bound84 X B hX hB
  rw [hsq] at hgram
  rw [htrace]
  exact (mul_le_mul_of_nonneg_left hcompare (by norm_num)).trans hgram

open NormedSpace
open scoped CStarAlgebra

open private trace_exp_sum_le_fourth from D5.S3.Quantum.Analysis.RefinedBMV44

/-- The refined exponential lower bound at bidegree (8,4). -/
theorem exponential_bound84 {n : ℕ} (H K : Matrix (Fin n) (Fin n) ℂ)
    (hH : H.IsHermitian) (hK : K.IsHermitian) :
    495 * (trace (exp ((8 : ℝ) • H + (4 : ℝ) • K))).re ≤
      ((balancedWords 8 4).map fun w ↦ (trace (evalWord (exp H) (exp K) w)).re).sum := by
  by_cases hn : n = 0
  · subst n
    simp [trace_eq_zero_of_isEmpty]
  letI : NeZero n := ⟨hn⟩
  have hs : (exp H) ^ (2 : ℕ) = exp ((2 : ℝ) • H) := by
    simpa only [two_nsmul, two_smul] using (Matrix.exp_nsmul 2 H).symm
  have he := trace_exp_sum_le_fourth ((2 : ℝ) • H) K (hermitian_real_smul hH _) hK
  rw [smul_smul, show (4 : ℝ) * 2 = 8 by norm_num, ← hs] at he
  exact (mul_le_mul_of_nonneg_left he (by norm_num)).trans
    (product_bound84 _ _ (exp_posDef hH).posSemidef (exp_posDef hK).posSemidef)

#print axioms product_bound84
#print axioms exponential_bound84

end RefinedBMV
