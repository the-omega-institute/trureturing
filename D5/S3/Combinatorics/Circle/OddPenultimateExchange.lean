/- GID: D5/S3/Combinatorics/Circle/OddPenultimateExchange
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/OddPenultimateExchange
   mirror-E: none(waiver:audit-open-22063)
   anchors: [mathlib/module/Mathlib.Logic.Equiv.Fin.Rotate]
   utility: none
   digest: A positive actual-source odd penultimate boundary admits two explicit strict-G exchanges with genuine SMALL returns. -/
module
public import D5.S3.Combinatorics.Circle.TerminalLargeSubstitution
public import Mathlib.Logic.Equiv.Fin.Rotate

/-! Positive actual-source odd penultimate exchange, positive orientation only.

Exact input region, with all letters physical elements of Fin k:
  k>=3, s=actualSource k t, N=2^k-1, Q=2^(k-2), C=N/2;
  s(p)>0, n=hit k 1 p is LARGE, N<3|s(p)|;
  q=finRotate k a, zpen=finRotate k q;
  W=F++[zpen]++Tpre++[a]++Tpost++[z]++E0++E1 is Legal;
  n and q are unused in ALL W;
  Tpre,[a],Tpost,E0,E1 are SMALL; 3*s(a)>C+1 and s(q)<s(p);
  z is negative LARGE, -s(z)<=|s(n)|;
  the old pre-a height u is <|s(n)|;
  n cannot append either at W or at the original terminal prefix through E0;
  u+delta>=-s(z), OR that old terminal-prefix height is >=s(a)-delta,
  where delta=-s(zpen)-|s(n)| is a source-derived positive correction.

No unusedness or append-blocking of p is required: p supplies the genuine
source geometry, while the actual inserted labels are n and q. No claim that
the complete general deep-suffix branch satisfies this conditional region is
made. No legal new word, SMALL subset support, endpoint, energy drop, physical
partition or minimizer is supplied as a premise.

The first construction retains all old labels except zpen and SMALL a. The
second returns zpen, a, and the actual terminal SMALL suffix E1. All natural
zero-start takes and exact physical inventories are proved outputs. The
complete hand proof is deep-suffix-math-20261026/source-proof.txt section 7a;
the proof reuses the public blocked_gate helper from
TerminalLargeSubstitution with its original telescope.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
namespace D5.S3.Combinatorics.Circle.OddPenultimateExchange
open SourceWidth ExpandingSourcePath MixedSuffixEnergy SmallStepOrdering
open TwoOppositeLargeExchange
open scoped BigOperators

local macro "source_arith" : tactic =>
  `(tactic| ((try simp only [s, N, C, Q, Large, mass, List.cons_append,
    List.nil_append, List.take_zero, List.take_succ_cons, List.map_append,
    List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil,
    add_zero, zero_add] at *) <;> omega))

def oldWord {k : ℕ} (zpen a z : Fin k)
    (F Tpre Tpost E : List (Fin k)) : List (Fin k) :=
  F ++ [zpen] ++ Tpre ++ [a] ++ Tpost ++ [z] ++ E

def correction (k t : ℕ) (p zpen : Fin k) : ℤ :=
  -s k t zpen - |s k t (hit k 1 p)|

def firstBranch {k : ℕ} (t : ℕ) (p zpen z : Fin k)
    (F Tpre : List (Fin k)) : Prop :=
  -s k t z ≤ mass (s k t) (F ++ [zpen] ++ Tpre) + correction k t p zpen

instance {k : ℕ} (t : ℕ) (p zpen z : Fin k) (F Tpre : List (Fin k)) :
    Decidable (firstBranch t p zpen z F Tpre) :=
  inferInstanceAs (Decidable (-s k t z ≤
    mass (s k t) (F ++ [zpen] ++ Tpre) + correction k t p zpen))

def candidate {k : ℕ} (t : ℕ) (p q zpen z : Fin k)
    (F Tpre L M : List (Fin k)) : List (Fin k) :=
  if firstBranch t p zpen z F Tpre then F ++ [hit k 1 p] ++ L ++ [z,q] ++ M
  else F ++ [hit k 1 p] ++ L ++ [z,q]

def returned {k : ℕ} (t : ℕ) (p zpen a z : Fin k)
    (F Tpre E1 : List (Fin k)) : List (Fin k) :=
  if firstBranch t p zpen z F Tpre then [zpen,a] else [zpen,a] ++ E1

private theorem order_small {k : ℕ} (hk : 3 ≤ k) (t : ℕ)
    (T : List (Fin k)) (b e : ℤ)
    (hsmall : ∀ i ∈ T, |s k t i| < Q k)
    (hb : 0 ≤ b ∧ b ≤ C k) (he : 0 ≤ e ∧ e ≤ C k)
    (hsum : e = b + mass (s k t) T) :
    ∃ L : List (Fin k), L.Perm T ∧ InStrip (s k t) (C k) b L := by
  obtain ⟨_, _, hC, _, _⟩ := source_geometry hk
  change C k = 2 * Q k - 1 at hC
  have hcompat : ∀ p ∈ T, ∀ n ∈ T,
      0 < s k t p → s k t n < 0 → s k t p - s k t n ≤ C k := by
    intro p hp n hn hpp hnn
    have hpp' := hsmall p hp
    have hnn' := hsmall n hn
    rw [abs_of_pos hpp] at hpp'
    rw [abs_of_neg hnn] at hnn'
    omega
  apply exists_order_between (s k t) T (C k) b hb
  · have hend : 0 ≤ b + mass (s k t) T ∧ b + mass (s k t) T ≤ C k := by
      rw [← hsum]
      exact he
    simpa only [mass] using hend
  · exact hcompat

set_option maxHeartbeats 800000 in
/-- A full conditional actual-source exchange at the positive odd penultimate
boundary. The selected SMALL orders and literal physical word are outputs;
both branches strictly lower G, and all physical count/energy balances persist.
Negative orientation and general availability are outside this theorem. -/
theorem actualSource_odd_penultimate_positive_exchange_full
    (k t : ℕ) (hk : 3 ≤ k) (p a z : Fin k)
    (F Tpre Tpost E0 E1 : List (Fin k))
    (hpositive : 0 < s k t p)
    (hnlarge : Q k ≤ |s k t (hit k 1 p)|)
    (hexpand : N k < 3 * |s k t p|)
    (hW : Legal k t (oldWord (finRotate k (finRotate k a)) a z
      F Tpre Tpost (E0 ++ E1)))
    (hnunused : hit k 1 p ∉ oldWord (finRotate k (finRotate k a)) a z
      F Tpre Tpost (E0 ++ E1))
    (hqunused : finRotate k a ∉ oldWord (finRotate k (finRotate k a)) a z
      F Tpre Tpost (E0 ++ E1))
    (hsmall : ∀ i ∈ Tpre ++ [a] ++ Tpost ++ E0 ++ E1, |s k t i| < Q k)
    (hcrossSize : C k + 1 < 3 * s k t a)
    (hqsmaller : s k t (finRotate k a) < s k t p)
    (hzlarge : Q k ≤ -s k t z)
    (hzupper : -s k t z ≤ |s k t (hit k 1 p)|)
    (hprelow : mass (s k t) (F ++ [finRotate k (finRotate k a)] ++ Tpre) <
      |s k t (hit k 1 p)|)
    (hblockEnd : ¬ Legal k t
      (oldWord (finRotate k (finRotate k a)) a z F Tpre Tpost (E0 ++ E1) ++ [hit k 1 p]))
    (hblockPrefix : ¬ Legal k t
      (oldWord (finRotate k (finRotate k a)) a z F Tpre Tpost E0 ++ [hit k 1 p]))
    (hchoice : firstBranch t p (finRotate k (finRotate k a)) z F Tpre ∨
      s k t a - correction k t p (finRotate k (finRotate k a)) ≤
        mass (s k t) (oldWord (finRotate k (finRotate k a)) a z F Tpre Tpost E0)) :
    let n := hit k 1 p
    let q := finRotate k a
    let zpen := finRotate k q
    let W := oldWord zpen a z F Tpre Tpost (E0 ++ E1)
    let W0 := oldWord zpen a z F Tpre Tpost E0
    ∃ L M : List (Fin k),
      (if firstBranch t p zpen z F Tpre then
        L.Perm Tpre ∧ M.Perm (Tpost ++ E0 ++ E1)
       else L.Perm (Tpre ++ Tpost ++ E0) ∧ M = []) ∧
      (let V := candidate t p q zpen z F Tpre L M
       let R := returned t p zpen a z F Tpre E1
       Legal k t V ∧ InStrip (s k t) (C k) 0 V ∧
       (∀ j : ℕ, 0 ≤ mass (s k t) (V.take j) ∧ mass (s k t) (V.take j) ≤ C k) ∧
       Inventory k t W V [n,q] R ∧
       G k t V + 1 = G k t W ∧
       U V = U W + (if firstBranch t p zpen z F Tpre then 0 else E1.length) ∧
       H k t V + 3 ^ (s k t zpen).natAbs =
         H k t W + 3 ^ (s k t n).natAbs + 3 ^ (s k t q).natAbs ∧
       J k t V < J k t W ∧
       mass (s k t) V =
         (if firstBranch t p zpen z F Tpre then mass (s k t) W
          else mass (s k t) W0) + 2 * s k t p - 3 * s k t a) := by
  classical
  dsimp only
  let f := s k t
  let n := hit k 1 p
  let q := finRotate k a
  let zpen := finRotate k q
  let W := oldWord zpen a z F Tpre Tpost (E0 ++ E1)
  let W0 := oldWord zpen a z F Tpre Tpost E0
  let P := f p
  let D := |f n|
  let aa := f a
  let qq := f q
  let ZZ := -f zpen
  let Z := -f z
  let δ := ZZ - D
  let u := mass f (F ++ [zpen] ++ Tpre)
  let h := mass f W
  let vE := mass f W0
  let b := mass f F - D
  have geo := native_geometry hk t p hnlarge hexpand
  obtain ⟨hQ, hN, hC, hNpos, hNodd⟩ := source_geometry hk
  change 2 ≤ Q k at hQ
  change N k = 4 * Q k - 1 at hN
  change C k = 2 * Q k - 1 at hC
  change 0 < N k at hNpos
  change N k % 2 = 1 at hNodd
  have habound (i : Fin k) : |f i| ≤ C k := abs_le.mpr (centered_bounds hNpos hNodd _)
  have hpabs : |s k t p| = P := abs_of_pos hpositive
  have hnval : f n = -D := by
    have hn' := geo.nValue
    simpa [n, D, f, orient, show ¬ s k t p < 0 by ((try dsimp only [f, n, q, zpen, W, W0, P, D, aa, qq, ZZ, Z, δ, u, h, vE, b] at *); source_arith)] using hn'
  have hD : D = N k - 2 * P := by simpa [D, P, f, n, hpabs] using geo.firstEquation
  have hDbound : Q k ≤ D := hnlarge
  have hbudget : 2 * P ≤ C k + Q k := by simpa [P, f, hpabs] using geo.budget
  have hDpos : 0 < D := by ((try dsimp only [f, n, q, zpen, W, W0, P, D, aa, qq, ZZ, Z, δ, u, h, vE, b] at *); source_arith)
  have hasmall : |aa| < Q k := hsmall a (by simp)
  have hapos : 0 < aa := by change C k + 1 < 3 * aa at hcrossSize; ((try dsimp only [f, n, q, zpen, W, W0, P, D, aa, qq, ZZ, Z, δ, u, h, vE, b] at *); source_arith)
  have haa : aa < Q k := by simpa only [abs_of_pos hapos] using hasmall
  have hcycle := (ZeroSumSubsets.source_cycle (by ((try dsimp only [f, n, q, zpen, W, W0, P, D, aa, qq, ZZ, Z, δ, u, h, vE, b] at *); source_arith) : 0 < k) t).2.2
  have hqeq : qq = 2 * aa := by
    have he := hcycle a
    change 2 * aa - qq = N k *
      (if N k < 4 * aa then 1 else if 4 * aa < -N k then -1 else 0) at he
    rw [if_neg (by ((try dsimp only [f, n, q, zpen, W, W0, P, D, aa, qq, ZZ, Z, δ, u, h, vE, b] at *); source_arith)), if_neg (by ((try dsimp only [f, n, q, zpen, W, W0, P, D, aa, qq, ZZ, Z, δ, u, h, vE, b] at *); source_arith))] at he
    ((try dsimp only [f, n, q, zpen, W, W0, P, D, aa, qq, ZZ, Z, δ, u, h, vE, b] at *); source_arith)
  have hqpos : 0 < qq := by ((try dsimp only [f, n, q, zpen, W, W0, P, D, aa, qq, ZZ, Z, δ, u, h, vE, b] at *); source_arith)
  have hqLarge' : Q k ≤ qq := by
    change C k + 1 < 3 * aa at hcrossSize
    ((try dsimp only [f, n, q, zpen, W, W0, P, D, aa, qq, ZZ, Z, δ, u, h, vE, b] at *); source_arith)
  have hzpeq : ZZ = N k - 2 * qq := by
    have he := hcycle q
    change 2 * qq - f zpen = N k *
      (if N k < 4 * qq then 1 else if 4 * qq < -N k then -1 else 0) at he
    rw [if_pos (by ((try dsimp only [f, n, q, zpen, W, W0, P, D, aa, qq, ZZ, Z, δ, u, h, vE, b] at *); source_arith))] at he
    dsimp only [ZZ]
    ((try dsimp only [f, n, q, zpen, W, W0, P, D, aa, qq, ZZ, Z, δ, u, h, vE, b] at *); source_arith)
  have hqP : qq < P := hqsmaller
  have hqD : D < qq := by ((try dsimp only [f, n, q, zpen, W, W0, P, D, aa, qq, ZZ, Z, δ, u, h, vE, b] at *); source_arith)
  have hZZD : D < ZZ := by ((try dsimp only [f, n, q, zpen, W, W0, P, D, aa, qq, ZZ, Z, δ, u, h, vE, b] at *); source_arith)
  have hδeq : δ = 2 * P - 4 * aa := by dsimp [δ]; ((try dsimp only [f, n, q, zpen, W, W0, P, D, aa, qq, ZZ, Z, δ, u, h, vE, b] at *); source_arith)
  have hδpos : 0 < δ := by dsimp [δ]; ((try dsimp only [f, n, q, zpen, W, W0, P, D, aa, qq, ZZ, Z, δ, u, h, vE, b] at *); source_arith)
  have hδaa : δ < aa := by
    change C k + 1 < 3 * aa at hcrossSize
    ((try dsimp only [f, n, q, zpen, W, W0, P, D, aa, qq, ZZ, Z, δ, u, h, vE, b] at *); source_arith)
  have hnL : Large k t n := geo.nLarge
  have hqL : Large k t q := by unfold Large; change Q k ≤ |qq|; rw [abs_of_pos hqpos]; exact hqLarge'
  have hzpL : Large k t zpen := by
    unfold Large
    have hh : f zpen < 0 := by dsimp [ZZ] at hZZD; ((try dsimp only [f, n, q, zpen, W, W0, P, D, aa, qq, ZZ, Z, δ, u, h, vE, b] at *); source_arith)
    change Q k ≤ |f zpen|
    rw [abs_of_neg hh]
    ((try dsimp only [f, n, q, zpen, W, W0, P, D, aa, qq, ZZ, Z, δ, u, h, vE, b] at *); source_arith)
  have haNotL : ¬ Large k t a := by unfold Large; change ¬ Q k ≤ |aa|; ((try dsimp only [f, n, q, zpen, W, W0, P, D, aa, qq, ZZ, Z, δ, u, h, vE, b] at *); source_arith)
  have hzpos : 0 < Z := by change Q k ≤ Z at hzlarge; ((try dsimp only [f, n, q, zpen, W, W0, P, D, aa, qq, ZZ, Z, δ, u, h, vE, b] at *); source_arith)
  have hzL : Large k t z := by
    unfold Large
    change Q k ≤ |f z|
    have hneg : f z < 0 := by dsimp [Z] at hzpos; ((try dsimp only [f, n, q, zpen, W, W0, P, D, aa, qq, ZZ, Z, δ, u, h, vE, b] at *); source_arith)
    rw [abs_of_neg hneg]
    exact hzlarge
  have hzval : f z = -Z := by dsimp [Z]; ((try dsimp only [f, n, q, zpen, W, W0, P, D, aa, qq, ZZ, Z, δ, u, h, vE, b] at *); source_arith)
  have hZbound : Z ≤ D := hzupper
  have hZZcap : ZZ ≤ C k := by
    have hb := habound zpen
    dsimp only [ZZ]
    ((try dsimp only [f, n, q, zpen, W, W0, P, D, aa, qq, ZZ, Z, δ, u, h, vE, b] at *); source_arith)
  have hsmallPart (T : List (Fin k))
      (hT : ∀ i ∈ T, i ∈ Tpre ++ [a] ++ Tpost ++ E0 ++ E1) :
      ∀ i ∈ T, |f i| < Q k := by intro i hi; exact hsmall i (hT i hi)
  have hTpre := hsmallPart Tpre (by intro i hi; simp [hi])
  have hTpostE := hsmallPart (Tpost ++ E0 ++ E1) (by
    intro i hi
    simp only [List.mem_append] at hi ⊢
    tauto)
  have hTprepostE0 := hsmallPart (Tpre ++ Tpost ++ E0) (by
    intro i hi
    simp only [List.mem_append] at hi ⊢
    tauto)
  have hE1 := hsmallPart E1 (by intro i hi; simp [hi])
  have hsW : InStrip f (C k) 0 W := strip_of_legal hW
  have hsF : InStrip f (C k) 0 F :=
    (strip_split F ([zpen] ++ Tpre ++ [a] ++ Tpost ++ [z] ++ E0 ++ E1)
      (by simpa [W, oldWord, List.append_assoc] using hsW)).1
  have hsFz : InStrip f (C k) 0 (F ++ [zpen]) :=
    (strip_split (F ++ [zpen]) (Tpre ++ [a] ++ Tpost ++ [z] ++ E0 ++ E1)
      (by simpa [W, oldWord, List.append_assoc] using hsW)).1
  have hsU : InStrip f (C k) 0 (F ++ [zpen] ++ Tpre) :=
    (strip_split (F ++ [zpen] ++ Tpre) ([a] ++ Tpost ++ [z] ++ E0 ++ E1)
      (by simpa [W, oldWord, List.append_assoc] using hsW)).1
  have hsplitW0 := strip_split W0 E1 (by simpa [W, W0, oldWord, List.append_assoc] using hsW)
  have hWW0 : (W0 ++ E1).Nodup := by
    have hnd : W.Nodup := hW.1
    simpa only [W, W0, oldWord, List.append_assoc] using hnd
  have hnW0 : W0.Nodup := hWW0.of_append_left
  have hW0 : Legal k t W0 := legal_of_strip hnW0 hsplitW0.1
  have hnunused0 : n ∉ W0 := by
    intro hi
    have hnot : n ∉ W := hnunused
    apply hnot
    have : n ∈ W0 ++ E1 := List.mem_append_left E1 hi
    simpa only [W, W0, oldWord, List.append_assoc] using this
  have holdEnd := TerminalLargeSubstitution.blocked_gate hW hnunused hblockEnd
  have holdPrefix := TerminalLargeSubstitution.blocked_gate hW0 hnunused0 hblockPrefix
  have hFbounds : 0 ≤ mass f F ∧ mass f F ≤ C k := by
    simpa only [mass, List.take_length, zero_add] using inStrip_prefix hsF F.length
  have hFzbounds : 0 ≤ mass f F - ZZ ∧ mass f F - ZZ ≤ C k := by
    have hend := inStrip_prefix hsFz (F ++ [zpen]).length
    simp only [List.take_length, zero_add, List.map_append, List.map_cons,
      List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, add_zero] at hend
    dsimp only [mass, ZZ]
    ((try dsimp only [f, n, q, zpen, W, W0, P, D, aa, qq, ZZ, Z, δ, u, h, vE, b] at *); source_arith)
  have hubounds : 0 ≤ u ∧ u ≤ C k := by
    simpa only [u, mass, List.take_length, zero_add] using
      inStrip_prefix hsU (F ++ [zpen] ++ Tpre).length
  have hh : 0 ≤ h ∧ h ≤ C k := by
    simpa only [h, mass, List.take_length, zero_add] using inStrip_prefix hsW W.length
  have hvE : 0 ≤ vE ∧ vE ≤ C k := by
    simpa only [vE, mass, List.take_length, zero_add] using inStrip_prefix hsplitW0.1 W0.length
  have hhD : h < D := by change ¬ (0 ≤ h + f n ∧ h + f n ≤ C k) at holdEnd; rw [hnval] at holdEnd; ((try dsimp only [f, n, q, zpen, W, W0, P, D, aa, qq, ZZ, Z, δ, u, h, vE, b] at *); source_arith)
  have hvED : vE < D := by change ¬ (0 ≤ vE + f n ∧ vE + f n ≤ C k) at holdPrefix; rw [hnval] at holdPrefix; ((try dsimp only [f, n, q, zpen, W, W0, P, D, aa, qq, ZZ, Z, δ, u, h, vE, b] at *); source_arith)
  have huD : u < D := hprelow
  have hb : 0 ≤ b ∧ b ≤ C k := by dsimp [b]; ((try dsimp only [f, n, q, zpen, W, W0, P, D, aa, qq, ZZ, Z, δ, u, h, vE, b] at *); source_arith)
  have hFnMass : mass f (F ++ [n]) = b := by
    dsimp only [b]
    simp only [mass, List.map_append, List.map_cons, List.map_nil,
      List.sum_append, List.sum_cons, List.sum_nil, add_zero, hnval, sub_eq_add_neg]
  have hsN : InStrip f (C k) (mass f F) [n] := by
    change 0 ≤ mass f F ∧ mass f F ≤ C k ∧
      0 ≤ mass f F + f n ∧ mass f F + f n ≤ C k
    rw [hnval]
    dsimp only [b] at hb
    exact ⟨hFbounds.1, hFbounds.2, by ((try dsimp only [f, n, q, zpen, W, W0, P, D, aa, qq, ZZ, Z, δ, u, h, vE, b] at *); source_arith), by ((try dsimp only [f, n, q, zpen, W, W0, P, D, aa, qq, ZZ, Z, δ, u, h, vE, b] at *); source_arith)⟩
  have hsFn : InStrip f (C k) 0 (F ++ [n]) :=
    inStrip_append hsF (by simpa only [zero_add, mass] using hsN)
  have hfinal (v : ℤ) (hv : 0 ≤ v) (hvD : v < D) :
      0 ≤ v + 2 * P - 3 * aa ∧ v + 2 * P - 3 * aa ≤ C k := by
    change C k + 1 < 3 * aa at hcrossSize
    ((try dsimp only [f, n, q, zpen, W, W0, P, D, aa, qq, ZZ, Z, δ, u, h, vE, b] at *); source_arith)
  have hnq : n ≠ q := by intro he; have hv : f n = f q := congrArg f he; rw [hnval] at hv; change -D = qq at hv; ((try dsimp only [f, n, q, zpen, W, W0, P, D, aa, qq, ZZ, Z, δ, u, h, vE, b] at *); source_arith)
  have hI : [n,q].Nodup := by simp [hnq]
  have hIW : ∀ i ∈ [n,q], i ∉ W := by
    intro i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · exact hnunused
    · exact hqunused
  have hIL : ∀ i ∈ [n,q], Large k t i := by
    intro i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · exact hnL
    · exact hqL
  let caseA := firstBranch t p zpen z F Tpre
  have hcase : ∃ L M : List (Fin k),
      (if caseA then L.Perm Tpre ∧ M.Perm (Tpost ++ E0 ++ E1)
       else L.Perm (Tpre ++ Tpost ++ E0) ∧ M = []) ∧
      InStrip f (C k) 0 (candidate t p q zpen z F Tpre L M) := by
    by_cases hc : firstBranch t p zpen z F Tpre
    · have hgate : Z ≤ u + δ := hc
      have hmid : 0 ≤ u + δ ∧ u + δ ≤ C k := by dsimp [δ]; ((try dsimp only [f, n, q, zpen, W, W0, P, D, aa, qq, ZZ, Z, δ, u, h, vE, b] at *); source_arith)
      have hsumL : u + δ = b + mass f Tpre := by
        dsimp [u, δ, b, ZZ]
        simp only [mass, List.map_append, List.map_cons, List.map_nil,
          List.sum_append, List.sum_cons, List.sum_nil, add_zero]
        ((try dsimp only [f, n, q, zpen, W, W0, P, D, aa, qq, ZZ, Z, δ, u, h, vE, b] at *); source_arith)
      obtain ⟨L, hL, hsL⟩ := order_small hk t Tpre b (u + δ) hTpre hb hmid hsumL
      let j := u + δ - Z + qq
      have hj : 0 ≤ j ∧ j ≤ C k := by dsimp [j, δ]; ((try dsimp only [f, n, q, zpen, W, W0, P, D, aa, qq, ZZ, Z, δ, u, h, vE, b] at *); source_arith)
      have hpair : InStrip f (C k) (u + δ) [z,q] := by
        change 0 ≤ u + δ ∧ u + δ ≤ C k ∧
          0 ≤ u + δ + f z ∧ u + δ + f z ≤ C k ∧
          0 ≤ u + δ + f z + f q ∧ u + δ + f z + f q ≤ C k
        rw [hzval]
        change 0 ≤ u + δ ∧ u + δ ≤ C k ∧
          0 ≤ u + δ + -Z ∧ u + δ + -Z ≤ C k ∧
          0 ≤ u + δ + -Z + qq ∧ u + δ + -Z + qq ≤ C k
        dsimp only [j] at hj
        exact ⟨hmid.1, hmid.2, by ((try dsimp only [f, n, q, zpen, W, W0, P, D, aa, qq, ZZ, Z, δ, u, h, vE, b] at *); source_arith), by ((try dsimp only [f, n, q, zpen, W, W0, P, D, aa, qq, ZZ, Z, δ, u, h, vE, b] at *); source_arith), by ((try dsimp only [f, n, q, zpen, W, W0, P, D, aa, qq, ZZ, Z, δ, u, h, vE, b] at *); source_arith), by ((try dsimp only [f, n, q, zpen, W, W0, P, D, aa, qq, ZZ, Z, δ, u, h, vE, b] at *); source_arith)⟩
      have hsumM : h + 2 * P - 3 * aa = j + mass f (Tpost ++ E0 ++ E1) := by
        dsimp [h, W, oldWord, j, u, δ, ZZ, Z, qq, aa]
        simp only [mass, List.map_append, List.map_cons, List.map_nil,
          List.sum_append, List.sum_cons, List.sum_nil, add_zero]
        ((try dsimp only [f, n, q, zpen, W, W0, P, D, aa, qq, ZZ, Z, δ, u, h, vE, b] at *); source_arith)
      obtain ⟨M, hM, hsM⟩ := order_small hk t (Tpost ++ E0 ++ E1) j
        (h + 2 * P - 3 * aa) hTpostE hj (hfinal h hh.1 hhD) hsumM
      have hsFnL : InStrip f (C k) 0 (F ++ [n] ++ L) := by
        apply inStrip_append hsFn
        change InStrip f (C k) (0 + mass f (F ++ [n])) L
        rw [zero_add, hFnMass]
        exact hsL
      have hsPrefix : InStrip f (C k) 0 (F ++ [n] ++ L ++ [z,q]) := by
        apply inStrip_append hsFnL
        have hm := (hL.map f).sum_eq
        have hhstart : mass f (F ++ [n] ++ L) = u + δ := by
          simp only [mass, List.map_append, List.map_cons, List.map_nil,
            List.sum_append, List.sum_cons, List.sum_nil, add_zero]
          change (L.map f).sum = _ at hm
          dsimp [u, δ, b, ZZ, mass] at hsumL
          rw [hnval]
          ((try dsimp only [f, n, q, zpen, W, W0, P, D, aa, qq, ZZ, Z, δ, u, h, vE, b] at *); source_arith)
        change InStrip f (C k) (0 + mass f (F ++ [n] ++ L)) [z, q]
        rw [zero_add, hhstart]
        exact hpair
      have hsV : InStrip f (C k) 0 (F ++ [n] ++ L ++ [z,q] ++ M) := by
        apply inStrip_append hsPrefix
        have hm := (hL.map f).sum_eq
        have hhstart : mass f (F ++ [n] ++ L ++ [z,q]) = j := by
          simp only [mass, List.map_append, List.map_cons, List.map_nil,
            List.sum_append, List.sum_cons, List.sum_nil, add_zero]
          dsimp only [j]
          dsimp only [b, mass] at hsumL
          rw [hnval]
          rw [hzval]
          ((try dsimp only [f, n, q, zpen, W, W0, P, D, aa, qq, ZZ, Z, δ, u, h, vE, b] at *); source_arith)
        change InStrip f (C k) (0 + mass f (F ++ [n] ++ L ++ [z, q])) M
        rw [zero_add, hhstart]
        exact hsM
      refine ⟨L, M, by simp only [caseA, if_pos hc]; exact ⟨hL, hM⟩, ?_⟩
      simpa [candidate, caseA, hc, n, List.append_assoc] using hsV
    · have hvchoice : aa - δ ≤ vE := by
        rcases hchoice with hA | hB
        · exact False.elim (hc hA)
        · exact hB
      let η := vE + δ - aa
      let finish := vE + 2 * P - 3 * aa
      have hη : 0 ≤ η := by dsimp [η]; ((try dsimp only [f, n, q, zpen, W, W0, P, D, aa, qq, ZZ, Z, δ, u, h, vE, b] at *); source_arith)
      have hfinish := hfinal vE hvE.1 hvED
      have hfinishEq : finish = η + qq := by dsimp [finish, η]; ((try dsimp only [f, n, q, zpen, W, W0, P, D, aa, qq, ZZ, Z, δ, u, h, vE, b] at *); source_arith)
      have htarget : 0 ≤ η + Z ∧ η + Z ≤ C k := by
        dsimp only [finish] at hfinishEq
        ((try dsimp only [f, n, q, zpen, W, W0, P, D, aa, qq, ZZ, Z, δ, u, h, vE, b] at *); source_arith)
      have hsumL : η + Z = b + mass f (Tpre ++ Tpost ++ E0) := by
        dsimp [η, vE, W0, oldWord, b, δ, ZZ, Z, aa]
        simp only [mass, List.map_append, List.map_cons, List.map_nil,
          List.sum_append, List.sum_cons, List.sum_nil, add_zero]
        ((try dsimp only [f, n, q, zpen, W, W0, P, D, aa, qq, ZZ, Z, δ, u, h, vE, b] at *); source_arith)
      obtain ⟨L, hL, hsL⟩ := order_small hk t (Tpre ++ Tpost ++ E0) b
        (η + Z) hTprepostE0 hb htarget hsumL
      have hsFnL : InStrip f (C k) 0 (F ++ [n] ++ L) := by
        apply inStrip_append hsFn
        change InStrip f (C k) (0 + mass f (F ++ [n])) L
        rw [zero_add, hFnMass]
        exact hsL
      have hpair : InStrip f (C k) (η + Z) [z,q] := by
        change 0 ≤ η + Z ∧ η + Z ≤ C k ∧
          0 ≤ η + Z + f z ∧ η + Z + f z ≤ C k ∧
          0 ≤ η + Z + f z + f q ∧ η + Z + f z + f q ≤ C k
        rw [hzval]
        change 0 ≤ η + Z ∧ η + Z ≤ C k ∧
          0 ≤ η + Z + -Z ∧ η + Z + -Z ≤ C k ∧
          0 ≤ η + Z + -Z + qq ∧ η + Z + -Z + qq ≤ C k
        dsimp only [finish] at hfinishEq
        exact ⟨htarget.1, htarget.2, by ((try dsimp only [f, n, q, zpen, W, W0, P, D, aa, qq, ZZ, Z, δ, u, h, vE, b] at *); source_arith), by ((try dsimp only [f, n, q, zpen, W, W0, P, D, aa, qq, ZZ, Z, δ, u, h, vE, b] at *); source_arith), by ((try dsimp only [f, n, q, zpen, W, W0, P, D, aa, qq, ZZ, Z, δ, u, h, vE, b] at *); source_arith), by ((try dsimp only [f, n, q, zpen, W, W0, P, D, aa, qq, ZZ, Z, δ, u, h, vE, b] at *); source_arith)⟩
      have hsV : InStrip f (C k) 0 (F ++ [n] ++ L ++ [z,q]) := by
        apply inStrip_append hsFnL
        have hm := (hL.map f).sum_eq
        have hhstart : mass f (F ++ [n] ++ L) = η + Z := by
          simp only [mass, List.map_append, List.map_cons, List.map_nil,
            List.sum_append, List.sum_cons, List.sum_nil, add_zero]
          dsimp [b, mass] at hsumL
          rw [hnval]
          ((try dsimp only [f, n, q, zpen, W, W0, P, D, aa, qq, ZZ, Z, δ, u, h, vE, b] at *); source_arith)
        change InStrip f (C k) (0 + mass f (F ++ [n] ++ L)) [z, q]
        rw [zero_add, hhstart]
        exact hpair
      refine ⟨L, [], by simp only [caseA, if_neg hc]; exact ⟨hL, True.intro⟩, ?_⟩
      simpa [candidate, caseA, hc, n, List.append_assoc] using hsV
  obtain ⟨L, M, hLM, hsV⟩ := hcase
  let V := candidate t p q zpen z F Tpre L M
  let R := returned t p zpen a z F Tpre E1
  have hperm : (V ++ R).Perm (W ++ [n,q]) := by
    apply List.perm_iff_count.mpr
    intro i
    by_cases hc : firstBranch t p zpen z F Tpre
    · obtain ⟨hL, hM⟩ := (show L.Perm Tpre ∧ M.Perm (Tpost ++ E0 ++ E1) by simpa only [caseA, if_pos hc] using hLM)
      have hl := hL.count_eq i
      have hm := hM.count_eq i
      simp only [V, R, W, candidate, returned, oldWord, caseA, if_pos hc, List.count_append,
        List.count_cons, List.count_nil] at hl hm ⊢
      ((try dsimp only [f, n, q, zpen, W, W0, P, D, aa, qq, ZZ, Z, δ, u, h, vE, b] at *); source_arith)
    · obtain ⟨hL, hM⟩ := (show L.Perm (Tpre ++ Tpost ++ E0) ∧ M = [] by simpa only [caseA, if_neg hc] using hLM)
      have hl := hL.count_eq i
      simp only [V, R, W, candidate, returned, oldWord, caseA, if_neg hc, List.count_append,
        List.count_cons, List.count_nil] at hl ⊢
      ((try dsimp only [f, n, q, zpen, W, W0, P, D, aa, qq, ZZ, Z, δ, u, h, vE, b] at *); source_arith)
  have hRsub : ∀ i ∈ R, i ∈ W := by
    intro i hi
    by_cases hc : firstBranch t p zpen z F Tpre
    · simp only [R, returned, caseA, if_pos hc, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl <;> simp [W, oldWord]
    · simp only [R, returned, caseA, if_neg hc, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with (rfl | rfl) | hi
      · simp [W, oldWord]
      · simp [W, oldWord]
      · simp [W, oldWord, hi]
  have inv : Inventory k t W V [n,q] R :=
    inventory_of_perm hk t W V [n,q] R hW.1 hI hIW hRsub hIL hperm
  have hRlarge : largeUsed k t R = 1 := by
    have hE := (small_weights t E1 hE1).1
    by_cases hc : firstBranch t p zpen z F Tpre <;>
      simp [R, returned, hc, largeWeight, hzpL, haNotL, hE]
  have hRenergy : H k t R = 3 ^ (f zpen).natAbs := by
    have hE := (small_weights t E1 hE1).2
    by_cases hc : firstBranch t p zpen z F Tpre <;>
      simp [R, returned, hc, energyWeight, hzpL, haNotL, hE, f, s]
  have hIlarge : largeUsed k t [n,q] = 2 := by simp [largeUsed, mass, largeWeight, hnL, hqL]
  have hIenergy : H k t [n,q] = 3 ^ (f n).natAbs + 3 ^ (f q).natAbs := by
    simp [H, mass, energyWeight, hnL, hqL, f, s]
  have hG : G k t V + 1 = G k t W := by
    have hbalance := inv.largeBalance
    rw [hRlarge, hIlarge] at hbalance
    ((try dsimp only [f, n, q, zpen, W, W0, P, D, aa, qq, ZZ, Z, δ, u, h, vE, b] at *); source_arith)
  have hU : U V = U W + (if caseA then 0 else E1.length) := by
    have hbalance := inv.countBalance
    by_cases hc : firstBranch t p zpen z F Tpre <;> simp [R, returned, caseA, hc] at hbalance ⊢ <;> ((try dsimp only [f, n, q, zpen, W, W0, P, D, aa, qq, ZZ, Z, δ, u, h, vE, b] at *); source_arith)
  have hH : H k t V + 3 ^ (f zpen).natAbs =
      H k t W + 3 ^ (f n).natAbs + 3 ^ (f q).natAbs := by
    have hbalance := inv.energyBalance
    rw [hRenergy, hIenergy] at hbalance
    ((try dsimp only [f, n, q, zpen, W, W0, P, D, aa, qq, ZZ, Z, δ, u, h, vE, b] at *); source_arith)
  have hJ : J k t V < J k t W := by
    apply Prod.Lex.toLex_lt_toLex.mpr
    exact Or.inl (by ((try dsimp only [f, n, q, zpen, W, W0, P, D, aa, qq, ZZ, Z, δ, u, h, vE, b] at *); source_arith))
  have hEnd : mass f V = (if caseA then h else vE) + 2 * P - 3 * aa := by
    have hRmass : mass f R =
        if caseA then -ZZ + aa else -ZZ + aa + mass f E1 := by
      by_cases hc : firstBranch t p zpen z F Tpre
      · simp only [R, returned, caseA, if_pos hc, mass, List.map_cons,
          List.map_nil, List.sum_cons, List.sum_nil, add_zero]
        dsimp only [ZZ, aa]
        ((try dsimp only [f, n, q, zpen, W, W0, P, D, aa, qq, ZZ, Z, δ, u, h, vE, b] at *); source_arith)
      · simp only [R, returned, caseA, if_neg hc, mass, List.map_append,
          List.map_cons, List.map_nil, List.sum_append, List.sum_cons,
          List.sum_nil, add_zero]
        dsimp only [ZZ, aa]
        ((try dsimp only [f, n, q, zpen, W, W0, P, D, aa, qq, ZZ, Z, δ, u, h, vE, b] at *); source_arith)
    have hImass : mass f [n,q] = -D + qq := by
      simp only [mass, List.map_cons, List.map_nil, List.sum_cons,
        List.sum_nil, add_zero, hnval, qq]
    have hbalance := inv.sourceBalance
    change mass f V + mass f R = h + mass f [n,q] at hbalance
    rw [hRmass, hImass] at hbalance
    by_cases hc : firstBranch t p zpen z F Tpre
    · simp only [caseA, if_pos hc] at hbalance ⊢
      ((try dsimp only [f, n, q, zpen, W, W0, P, D, aa, qq, ZZ, Z, δ, u, h, vE, b] at *); source_arith)
    · simp only [caseA, if_neg hc] at hbalance ⊢
      have hWsplit : h = vE + mass f E1 := by
        dsimp [h, vE, W, W0, oldWord]
        simp only [mass, List.map_append, List.map_cons, List.map_nil,
          List.sum_append, List.sum_cons, List.sum_nil, add_zero]
        ((try dsimp only [f, n, q, zpen, W, W0, P, D, aa, qq, ZZ, Z, δ, u, h, vE, b] at *); source_arith)
      ((try dsimp only [f, n, q, zpen, W, W0, P, D, aa, qq, ZZ, Z, δ, u, h, vE, b] at *); source_arith)
  have hlegal : Legal k t V := legal_of_strip inv.nodup hsV
  refine ⟨L, M, hLM, hlegal, hsV, ?_, inv, hG, hU, hH, hJ, hEnd⟩
  intro j
  simpa [mass, f, n, q, zpen] using inStrip_prefix hsV j

#print axioms actualSource_odd_penultimate_positive_exchange_full

end D5.S3.Combinatorics.Circle.OddPenultimateExchange
