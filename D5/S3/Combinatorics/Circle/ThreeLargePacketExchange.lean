/- GID: D5/S3/Combinatorics/Circle/ThreeLargePacketExchange
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/ThreeLargePacketExchange
   mirror-E: none(waiver:audit-open-22063)
   anchors: [mathlib/module/Mathlib.Logic.Equiv.Fin.Rotate]
   utility: none
   digest: An actual positive SMALL doubling packet supplies a complete strict-H three-LARGE exchange. -/
module
public import D5.S3.Combinatorics.Circle.PositiveSmallReturnExchange
public import Mathlib.Logic.Equiv.Fin.Rotate

/-! Actual packet selection closes the complete exchange with three later negative LARGE labels. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
namespace D5.S3.Combinatorics.Circle.ThreeLargePacketExchange
open SourceWidth ExpandingSourcePath MixedSuffixEnergy SmallStepOrdering
open TwoOppositeLargeExchange
open scoped BigOperators

def smallWord {k : ℕ} (T0 T1 T2 E : List (Fin k)) : List (Fin k) :=
  T0 ++ T1 ++ T2 ++ E

def positive {k : ℕ} (t : ℕ) (S : List (Fin k)) : List (Fin k) :=
  S.filter (fun i => decide (0 < s k t i))

def oldWord {k : ℕ} (p y zpen z : Fin k)
    (A T0 T1 T2 E : List (Fin k)) : List (Fin k) :=
  A ++ [hit k 2 p] ++ T0 ++ [y] ++ T1 ++ [zpen] ++ T2 ++ [z] ++ E

def prospective (k t : ℕ) (p q y zpen : Fin k) (W : List (Fin k)) : ℤ :=
  mass (s k t) W - s k t y - s k t zpen + s k t q - s k t p

local macro "source_arith" : tactic =>
  `(tactic| ((try simp only [s, N, C, Q, Large, mass, List.cons_append,
    List.nil_append, List.map_append, List.map_cons, List.map_nil,
    List.sum_append, List.sum_cons, List.sum_nil, add_zero, zero_add] at *) <;> omega))

theorem positive_mass_dominates {α : Type*} (f : α → ℤ) (X : List α) :
    mass f X ≤ mass f (X.filter (fun i => decide (0 < f i))) := by
  induction X with
  | nil => simp [mass]
  | cons i X ih =>
    by_cases hi : 0 < f i
    · simpa [mass, hi] using add_le_add_left ih (f i)
    · simp [mass, hi]
      have hn : f i ≤ 0 := by omega
      dsimp only [mass] at ih
      omega

private theorem packet_select {α : Type*} [DecidableEq α]
    (f : α → ℤ) (Pos : List α) (b c : α) (β B low : ℤ)
    (hb : b ∈ Pos) (hc : c ∈ Pos) (hne : b ≠ c)
    (hbval : f b = β) (hcval : f c = 2 * β)
    (hβ : 0 < β) (hB : β ≤ B) (hlow : 0 < low)
    (hentry : ∀ i ∈ Pos, 0 < f i ∧ f i ≤ 3 * β + B)
    (htotal : low ≤ mass f Pos) :
    ∃ R : List α, R.Subperm Pos ∧ low ≤ mass f R ∧ mass f R ≤ low + B := by
  classical
  let O := (Pos.erase b).erase c
  have hc' : c ∈ Pos.erase b := (List.mem_erase_of_ne hne.symm).mpr hc
  have hp1 := List.perm_cons_erase hb
  have hp2 := List.perm_cons_erase hc'
  have hpbc : (b :: c :: O).Perm Pos := (hp2.cons b).symm.trans hp1.symm
  have hpart : (O ++ [b,c]).Perm Pos := List.perm_append_comm.trans hpbc
  have hmass : mass f O + 3 * β = mass f Pos := by
    have hh := (hpart.map f).sum_eq
    simp only [List.map_append, List.map_cons, List.map_nil,
      List.sum_append, List.sum_cons, List.sum_nil, add_zero, hbval, hcval] at hh
    dsimp only [mass]
    omega
  have hO (i : α) (hi : i ∈ O) : i ∈ Pos :=
    List.mem_of_mem_erase (List.mem_of_mem_erase hi)
  obtain ⟨U, hU, hUlo, hUhi⟩ : ∃ U : List α,
      U.Sublist O ∧ low - 3 * β ≤ mass f U ∧ mass f U ≤ low + B - 1 := by
    by_cases hl : low ≤ 3 * β
    · refine ⟨[], List.nil_sublist _, ?_, ?_⟩ <;> simp only [mass, List.map_nil, List.sum_nil] <;> omega
    · have hbase : 0 ≤ 3 * β + B - 1 := by omega
      have htarget : 0 < low - 3 * β := by omega
      have hsize : low - 3 * β ≤ mass f O := by omega
      obtain ⟨U,hU,hlo,hhi⟩ := PositiveSmallReturnExchange.first_crossing f O (3 * β + B - 1)
        hbase (low - 3 * β) htarget (by
          intro i hi
          have hh := hentry i (hO i hi)
          exact ⟨hh.1, by omega⟩) hsize
      exact ⟨U,hU,hlo,by omega⟩
  obtain ⟨K, hK, hlo, hhi⟩ : ∃ K : List α,
      K.Sublist [b,c] ∧ low ≤ mass f U + mass f K ∧
        mass f U + mass f K ≤ low + B := by
    by_cases hu : low ≤ mass f U
    · refine ⟨[], List.nil_sublist _, ?_, ?_⟩ <;> simp only [mass, List.map_nil, List.sum_nil, add_zero] <;> dsimp only [mass] at * <;> omega
    · by_cases hb' : low ≤ mass f U + β
      · refine ⟨[b], List.singleton_sublist.mpr (by simp), ?_, ?_⟩ <;>
          simp only [mass, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, hbval] <;>
          dsimp only [mass] at * <;> omega
      · by_cases hc' : low ≤ mass f U + 2 * β
        · refine ⟨[c], List.singleton_sublist.mpr (by simp), ?_, ?_⟩ <;>
            simp only [mass, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, hcval] <;>
            dsimp only [mass] at * <;> omega
        · refine ⟨[b,c], List.Sublist.refl _, ?_, ?_⟩ <;>
            simp only [mass, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, hbval, hcval] <;>
            dsimp only [mass] at * <;> omega
  refine ⟨U ++ K, (hU.append hK).subperm.trans hpart.subperm, ?_, ?_⟩
  · simpa only [mass, List.map_append, List.sum_append] using hlo
  · simpa only [mass, List.map_append, List.sum_append] using hhi

set_option maxHeartbeats 1200000 in
/-- The shared physical exchange preserves a selector tag on the actual returned SMALL labels. -/
theorem actualSource_threeLarge_tagged_exchange_full
    (k t : ℕ) (tag : List (Fin k) → Prop)
    (hk : 3 ≤ k) (p q y zpen z : Fin k)
    (A T0 T1 T2 E : List (Fin k))
    (hpositive : 0 < s k t p)
    (hnlarge : Q k ≤ |s k t (hit k 1 p)|)
    (hexpand : N k < 3 * |s k t p|)
    (hW : Legal k t (oldWord p y zpen z A T0 T1 T2 E))
    (hpunused : p ∉ oldWord p y zpen z A T0 T1 T2 E)
    (hnunused : hit k 1 p ∉ oldWord p y zpen z A T0 T1 T2 E)
    (hqunused : q ∉ oldWord p y zpen z A T0 T1 T2 E)
    (hsmall : ∀ i ∈ smallWord T0 T1 T2 E,
      |s k t i| < Q k)
    (hylarge : Q k ≤ -s k t y)
    (hzpenlarge : Q k ≤ -s k t zpen)
    (hzlarge : Q k ≤ -s k t z)
    (hzupper : -s k t z ≤ s k t q)
    (hqlarge : Q k ≤ s k t q)
    (hqsmaller : s k t q < s k t p)
    (htagNil : tag [])
    (hselect : ∀ low : ℤ, 0 < low →
      low ≤ mass (s k t)
        (positive t
          (smallWord T0 T1 T2 E)) →
      ∃ R : List (Fin k),
        R.Subperm (smallWord T0 T1 T2 E) ∧
        tag R ∧ low ≤ mass (s k t) R ∧
          mass (s k t) R ≤ low +
            (C k - s k t q)) :
    let n := hit k 1 p
    let x := hit k 2 p
    let W := oldWord p y zpen z A T0 T1 T2 E
    let S := smallWord T0 T1 T2 E
    let e0 := prospective k t p q y zpen W
    ∃ R L : List (Fin k), R.Subperm S ∧ (L ++ R).Perm S ∧ tag R ∧
      (∀ i ∈ R, |s k t i| < Q k) ∧
      (let V := A ++ [p, n] ++ L ++ [z, q]
       let returned := [x, y, zpen] ++ R
       let e := e0 - mass (s k t) R
       Legal k t V ∧ InStrip (s k t) (C k) 0 V ∧
       (∀ j : ℕ, 0 ≤ mass (s k t) (V.take j) ∧
         mass (s k t) (V.take j) ≤ C k) ∧
       Inventory k t W V [p, n, q] returned ∧
       G k t V = G k t W ∧ U V = U W + R.length ∧
       H k t V + 3 ^ (s k t x).natAbs + 3 ^ (s k t y).natAbs +
           3 ^ (s k t zpen).natAbs =
         H k t W + 3 ^ (s k t p).natAbs + 3 ^ (s k t n).natAbs +
           3 ^ (s k t q).natAbs ∧
       H k t V < H k t W ∧ J k t V < J k t W ∧
       mass (s k t) V = e ∧ s k t q ≤ e ∧ e ≤ C k) := by
  classical
  dsimp only
  let f := s k t
  let n := hit k 1 p
  let x := hit k 2 p
  let W := oldWord p y zpen z A T0 T1 T2 E
  let S := smallWord T0 T1 T2 E
  let Pos := positive t S
  let P := f p
  let D := |f n|
  let r := |f x|
  let qq := f q
  let Y := -f y
  let ZZ := -f zpen
  let Z := -f z
  let B := C k - qq
  let a0 := mass f A
  let b0 := a0 + P - D
  let h := mass f W
  let e0 := prospective k t p q y zpen W
  have geo := native_geometry hk t p hnlarge hexpand
  obtain ⟨hQ, hN, hC, hNpos, hNodd⟩ := source_geometry hk
  change 2 ≤ Q k at hQ
  change N k = 4 * Q k - 1 at hN
  change C k = 2 * Q k - 1 at hC
  have hpabs : |f p| = P := abs_of_pos hpositive
  have hnval : f n = -D := by
    have hh := geo.nValue
    simpa [n, D, f, orient, show ¬ s k t p < 0 by omega] using hh
  have hxval : f x = r := by
    have hh := geo.xValue
    simpa [x, r, f, orient, show ¬ s k t p < 0 by omega] using hh
  have hDP : D < P := by simpa [D,P,f,n,abs_of_pos hpositive] using geo.strictOrder.1
  have hPr : P < r := by simpa [P,r,f,x,abs_of_pos hpositive] using geo.strictOrder.2
  have hr : r = 2 * P - D := by
    have h1 : D = N k - 2 * P := by
      simpa [D,P,f,n,abs_of_pos hpositive] using geo.firstEquation
    have h2 : r = 4 * P - N k := by
      simpa [r,P,f,x,abs_of_pos hpositive] using geo.secondEquation
    ((try dsimp only [f,n,x,W,S,Pos,P,D,r,qq,Y,ZZ,Z,B,a0,b0,h,e0] at *); source_arith)
  have hDbound : Q k ≤ D := hnlarge
  have hqpos : 0 < qq := by ((try dsimp only [f,n,x,W,S,Pos,P,D,r,qq,Y,ZZ,Z,B,a0,b0,h,e0] at *); source_arith)
  have hqP : qq < P := hqsmaller
  have hbound (i : Fin k) : |f i| ≤ C k :=
    abs_le.mpr (centered_bounds hNpos hNodd _)
  have hPcap : P ≤ C k := by simpa only [hpabs] using hbound p
  have hY : 0 < Y ∧ Q k ≤ Y := by ((try dsimp only [f,n,x,W,S,Pos,P,D,r,qq,Y,ZZ,Z,B,a0,b0,h,e0] at *); source_arith)
  have hZZ : 0 < ZZ ∧ Q k ≤ ZZ := by ((try dsimp only [f,n,x,W,S,Pos,P,D,r,qq,Y,ZZ,Z,B,a0,b0,h,e0] at *); source_arith)
  have hZ : 0 < Z ∧ Z ≤ qq := by ((try dsimp only [f,n,x,W,S,Pos,P,D,r,qq,Y,ZZ,Z,B,a0,b0,h,e0] at *); source_arith)
  have hpn : p ≠ n := by intro hh; have he := congrArg f hh; ((try dsimp only [f,n,x,W,S,Pos,P,D,r,qq,Y,ZZ,Z,B,a0,b0,h,e0] at *); source_arith)
  have hpq : p ≠ q := by intro hh; have he := congrArg f hh; ((try dsimp only [f,n,x,W,S,Pos,P,D,r,qq,Y,ZZ,Z,B,a0,b0,h,e0] at *); source_arith)
  have hnq : n ≠ q := by intro hh; have he := congrArg f hh; ((try dsimp only [f,n,x,W,S,Pos,P,D,r,qq,Y,ZZ,Z,B,a0,b0,h,e0] at *); source_arith)
  have hpL : Large k t p := geo.pLarge
  have hnL : Large k t n := geo.nLarge
  have hxL : Large k t x := geo.xLarge
  have hqL : Large k t q := by
    change Q k ≤ |qq|
    rw [abs_of_pos hqpos]
    exact hqlarge
  have hyL : Large k t y := by
    change Q k ≤ |f y|
    rw [abs_of_neg (show f y < 0 by ((try dsimp only [f,n,x,W,S,Pos,P,D,r,qq,Y,ZZ,Z,B,a0,b0,h,e0] at *); source_arith))]
    exact hylarge
  have hzpL : Large k t zpen := by
    change Q k ≤ |f zpen|
    rw [abs_of_neg (show f zpen < 0 by ((try dsimp only [f,n,x,W,S,Pos,P,D,r,qq,Y,ZZ,Z,B,a0,b0,h,e0] at *); source_arith))]
    exact hzpenlarge
  have hsW : InStrip f (C k) 0 W := strip_of_legal hW
  have hsA : InStrip f (C k) 0 A :=
    (strip_split A ([x] ++ T0 ++ [y] ++ T1 ++ [zpen] ++ T2 ++ [z] ++ E)
      (by simpa only [W, oldWord, x, List.append_assoc] using hsW)).1
  have hsAx : InStrip f (C k) 0 (A ++ [x]) :=
    (strip_split (A ++ [x]) (T0 ++ [y] ++ T1 ++ [zpen] ++ T2 ++ [z] ++ E)
      (by simpa only [W, oldWord, x, List.append_assoc] using hsW)).1
  have ha0 : 0 ≤ a0 ∧ a0 ≤ C k := by
    simpa only [a0, mass, List.take_length, zero_add] using inStrip_prefix hsA A.length
  have hax : a0 + r ≤ C k := by
    have hh := (inStrip_prefix hsAx (A ++ [x]).length).2
    simp only [List.take_length, zero_add, List.map_append, List.map_cons,
      List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, add_zero] at hh
    change a0 + f x ≤ C k at hh
    rwa [hxval] at hh
  have hh : 0 ≤ h := by
    have ht := (inStrip_prefix hsW W.length).1
    simpa only [h, mass, List.take_length, zero_add] using ht
  have hb0 : 0 ≤ b0 ∧ b0 ≤ C k - P := by ((try dsimp only [f,n,x,W,S,Pos,P,D,r,qq,Y,ZZ,Z,B,a0,b0,h,e0] at *); source_arith)
  have he0 : e0 = h + Y + ZZ + qq - P := rfl
  have he0Eq : e0 = b0 + mass f S - Z + qq := by
    dsimp only [e0, prospective, b0, a0, W, oldWord, S, smallWord, Y, ZZ, Z, qq, P]
    simp only [mass, List.map_append, List.map_cons, List.map_nil,
      List.sum_append, List.sum_cons, List.sum_nil, add_zero]
    have hxr : f (hit k 2 p) = 2 * f p - D := by
      change f x = 2 * P - D
      rw [hxval, hr]
    dsimp only [f] at hxr ⊢
    rw [hxr]
    ring
  have he0lo : qq < e0 := by ((try dsimp only [f,n,x,W,S,Pos,P,D,r,qq,Y,ZZ,Z,B,a0,b0,h,e0] at *); source_arith)
  have hmassPos : mass f S ≤ mass f Pos := positive_mass_dominates f S
  have hsupply : e0 - C k ≤ mass f Pos := by ((try dsimp only [f,n,x,W,S,Pos,P,D,r,qq,Y,ZZ,Z,B,a0,b0,h,e0] at *); source_arith)
  obtain ⟨R, hRsub, hRtag, hRlo, hRhi⟩ : ∃ R : List (Fin k),
      R.Subperm S ∧ tag R ∧ e0 - C k ≤ mass f R ∧ mass f R ≤ e0 - qq := by
    by_cases hl : e0 - C k ≤ 0
    · refine ⟨[], List.nil_subperm, htagNil, ?_, ?_⟩
      · simp only [mass, List.map_nil, List.sum_nil]
        omega
      · simp only [mass, List.map_nil, List.sum_nil]
        omega
    · obtain ⟨R,hR,hTag,hlo,hhi⟩ := hselect (e0 - C k) (by omega) hsupply
      exact ⟨R,hR,hTag,hlo,by
        change mass f R ≤ (e0 - C k) + (C k - qq) at hhi
        omega⟩
  let Rem := S.diff R
  have hpart : (Rem ++ R).Perm S := by
    have hp := List.subperm_append_diff_self_of_count_le (fun i _ => hRsub.count_le i)
    exact List.perm_append_comm.trans hp
  have hmasspart : mass f Rem + mass f R = mass f S := by
    simpa only [mass, List.map_append, List.sum_append] using (hpart.map f).sum_eq
  have hsmallRem (i : Fin k) (hi : i ∈ Rem) : |f i| < Q k :=
    hsmall i ((List.diff_sublist _ _).subset hi)
  have hsmallR (i : Fin k) (hi : i ∈ R) : |f i| < Q k :=
    hsmall i (hRsub.subset hi)
  let e := e0 - mass f R
  let η := e - qq
  let c := η + Z
  have he : qq ≤ e ∧ e ≤ C k := by dsimp only [e]; omega
  have hη : 0 ≤ η ∧ η ≤ C k := by dsimp only [η]; omega
  have hc : 0 ≤ c ∧ c ≤ C k := by dsimp only [c, η]; omega
  have hsum : b0 + mass f Rem = c := by dsimp only [c, η, e]; omega
  have hcompat : ∀ i ∈ Rem, ∀ j ∈ Rem,
      0 < f i → f j < 0 → f i - f j ≤ C k := by
    intro i hi j hj hip hjn
    have hi' := hsmallRem i hi
    have hj' := hsmallRem j hj
    rw [abs_of_pos hip] at hi'
    rw [abs_of_neg hjn] at hj'
    omega
  have hb0cap : 0 ≤ b0 ∧ b0 ≤ C k := by ((try dsimp only [f,n,x,W,S,Pos,P,D,r,qq,Y,ZZ,Z,B,a0,b0,h,e0] at *); source_arith)
  have hend : 0 ≤ b0 + mass f Rem ∧ b0 + mass f Rem ≤ C k := by
    rw [hsum]
    exact hc
  obtain ⟨L,hL,hsL⟩ := exists_order_between f Rem (C k) b0 hb0cap
    (by simpa only [mass] using hend) hcompat
  have hLR : (L ++ R).Perm S := (hL.append_right R).trans hpart
  have hmassL : mass f L = mass f Rem := by simpa only [mass] using (hL.map f).sum_eq
  have hpairPN : InStrip f (C k) a0 [p,n] := by
    change 0 ≤ a0 ∧ a0 ≤ C k ∧ 0 ≤ a0 + f p ∧ a0 + f p ≤ C k ∧
      0 ≤ a0 + f p + f n ∧ a0 + f p + f n ≤ C k
    rw [hnval]
    change 0 ≤ a0 ∧ a0 ≤ C k ∧ 0 ≤ a0 + P ∧ a0 + P ≤ C k ∧
      0 ≤ a0 + P + -D ∧ a0 + P + -D ≤ C k
    exact ⟨ha0.1,ha0.2,by ((try dsimp only [f,n,x,W,S,Pos,P,D,r,qq,Y,ZZ,Z,B,a0,b0,h,e0] at *); source_arith),by ((try dsimp only [f,n,x,W,S,Pos,P,D,r,qq,Y,ZZ,Z,B,a0,b0,h,e0] at *); source_arith),by ((try dsimp only [f,n,x,W,S,Pos,P,D,r,qq,Y,ZZ,Z,B,a0,b0,h,e0] at *); source_arith),by ((try dsimp only [f,n,x,W,S,Pos,P,D,r,qq,Y,ZZ,Z,B,a0,b0,h,e0] at *); source_arith)⟩
  have hsApn : InStrip f (C k) 0 (A ++ [p,n]) :=
    inStrip_append hsA (by simpa only [zero_add, a0, mass] using hpairPN)
  have hApn : mass f (A ++ [p,n]) = b0 := by
    simp only [mass, List.map_append, List.map_cons, List.map_nil,
      List.sum_append, List.sum_cons, List.sum_nil, add_zero, hnval]
    dsimp only [b0, a0, P, mass]
    ring
  have hsApnL : InStrip f (C k) 0 (A ++ [p,n] ++ L) := by
    apply inStrip_append hsApn
    change InStrip f (C k) (0 + mass f (A ++ [p,n])) L
    rw [zero_add,hApn]
    exact hsL
  have hApnL : mass f (A ++ [p,n] ++ L) = c := by
    calc
      _ = mass f (A ++ [p,n]) + mass f L := by simp only [mass,List.map_append,List.sum_append]
      _ = c := by rw [hApn,hmassL]; exact hsum
  have hpairZQ : InStrip f (C k) c [z,q] := by
    change 0 ≤ c ∧ c ≤ C k ∧ 0 ≤ c + f z ∧ c + f z ≤ C k ∧
      0 ≤ c + f z + f q ∧ c + f z + f q ≤ C k
    have hcz : c + f z = η := by dsimp only [c,Z]; ring
    have hczq : c + f z + f q = e := by rw [hcz]; dsimp only [η,qq]; ring
    rw [hczq,hcz]
    exact ⟨hc.1,hc.2,hη.1,hη.2,by omega,he.2⟩
  let V := A ++ [p,n] ++ L ++ [z,q]
  let Ret := [x,y,zpen] ++ R
  have hsV : InStrip f (C k) 0 V := by
    apply inStrip_append hsApnL
    change InStrip f (C k) (0 + mass f (A ++ [p,n] ++ L)) [z,q]
    rw [zero_add,hApnL]
    exact hpairZQ
  have hI : [p,n,q].Nodup := by simp [hpn,hpq,hnq]
  have hIW (i : Fin k) (hi : i ∈ [p,n,q]) : i ∉ W := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl | rfl | rfl
    · exact hpunused
    · exact hnunused
    · exact hqunused
  have hIL (i : Fin k) (hi : i ∈ [p,n,q]) : Large k t i := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl | rfl | rfl
    · exact hpL
    · exact hnL
    · exact hqL
  have hperm : (V ++ Ret).Perm (W ++ [p,n,q]) := by
    apply List.perm_iff_count.mpr
    intro i
    have hh := hLR.count_eq i
    simp only [S,smallWord,List.count_append] at hh
    simp only [V,Ret,W,oldWord,x,List.count_append,List.count_cons,List.count_nil]
    omega
  have hRold (i : Fin k) (hi : i ∈ Ret) : i ∈ W := by
    simp only [Ret,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with (rfl | rfl | rfl) | hi
    · simp [W,oldWord,x]
    · simp [W,oldWord]
    · simp [W,oldWord]
    · have hm := hRsub.subset hi
      simp only [S,smallWord,List.mem_append] at hm
      simp only [W,oldWord,List.mem_append,List.mem_cons,List.not_mem_nil,or_false]
      tauto
  have inv : Inventory k t W V [p,n,q] Ret :=
    inventory_of_perm hk t W V [p,n,q] Ret hW.1 hI hIW hRold hIL hperm
  have hRweights := small_weights t R hsmallR
  have hRetLarge : largeUsed k t Ret = 3 := by
    simp [Ret,largeWeight,hxL,hyL,hzpL,hRweights.1]
  have hRetEnergy : H k t Ret = 3 ^ (f x).natAbs + 3 ^ (f y).natAbs + 3 ^ (f zpen).natAbs := by
    simp [Ret,energyWeight,hxL,hyL,hzpL,hRweights.2,f,s,Nat.add_assoc]
  have hILarge : largeUsed k t [p,n,q] = 3 := by simp [largeWeight,hpL,hnL,hqL]
  have hIEnergy : H k t [p,n,q] = 3 ^ (f p).natAbs + 3 ^ (f n).natAbs + 3 ^ (f q).natAbs := by
    simp [energyWeight,hpL,hnL,hqL,f,s,Nat.add_assoc]
  have hG : G k t V = G k t W := by
    have ht := inv.largeBalance
    rw [hRetLarge,hILarge] at ht
    omega
  have hU : U V = U W + R.length := by
    have ht := inv.countBalance
    simp only [Ret,List.length_append,List.length_cons,List.length_nil] at ht
    omega
  have hH : H k t V + 3 ^ (f x).natAbs + 3 ^ (f y).natAbs + 3 ^ (f zpen).natAbs =
      H k t W + 3 ^ (f p).natAbs + 3 ^ (f n).natAbs + 3 ^ (f q).natAbs := by
    have ht := inv.energyBalance
    rw [hRetEnergy,hIEnergy] at ht
    omega
  have hDn : (f n).natAbs < (f p).natAbs := by
    exact_mod_cast (show ((f n).natAbs : ℤ) < ((f p).natAbs : ℤ) by
      simpa only [Int.natCast_natAbs] using geo.strictOrder.1)
  have hQn : (f q).natAbs < (f p).natAbs := by
    exact_mod_cast (show ((f q).natAbs : ℤ) < ((f p).natAbs : ℤ) by
      simp only [Int.natCast_natAbs]
      rw [abs_of_pos (show 0 < f q from hqpos),hpabs]
      exact hqP)
  have hPn : (f p).natAbs < (f x).natAbs := by
    exact_mod_cast (show ((f p).natAbs : ℤ) < ((f x).natAbs : ℤ) by
      simpa only [Int.natCast_natAbs] using geo.strictOrder.2)
  have hEnergy : 3 ^ (f p).natAbs + 3 ^ (f n).natAbs + 3 ^ (f q).natAbs <
      (3 : ℕ) ^ (f x).natAbs := by
    have hd := pow_lt_pow_right₀ (by decide : 1 < (3 : ℕ)) hDn
    have hq := pow_lt_pow_right₀ (by decide : 1 < (3 : ℕ)) hQn
    have htop : 3 ^ (f p).natAbs + 3 ^ (f n).natAbs + 3 ^ (f q).natAbs <
        (3 : ℕ) ^ ((f p).natAbs + 1) := by
      rw [pow_succ]
      omega
    exact htop.trans_le (pow_le_pow_right₀ (by decide : 1 ≤ (3 : ℕ)) (by omega))
  have hHstrict : H k t V < H k t W := by
    have hle : H k t V + 3 ^ (f x).natAbs ≤ H k t W +
        (3 ^ (f p).natAbs + 3 ^ (f n).natAbs + 3 ^ (f q).natAbs) := by
      calc
        H k t V + 3 ^ (f x).natAbs ≤
            H k t V + 3 ^ (f x).natAbs + 3 ^ (f y).natAbs + 3 ^ (f zpen).natAbs :=
          (Nat.le_add_right _ _).trans (Nat.le_add_right _ _)
        _ = _ := by simpa only [Nat.add_assoc] using hH
    exact (Nat.add_lt_add_iff_right).mp
      (hle.trans_lt (Nat.add_lt_add_left hEnergy (H k t W)))
  have hJ : J k t V < J k t W := by
    apply Prod.Lex.toLex_lt_toLex.mpr
    exact Or.inr ⟨hG,Prod.Lex.toLex_lt_toLex.mpr (Or.inl hHstrict)⟩
  have hEnd : mass f V = e := by
    calc
      _ = mass f (A ++ [p,n] ++ L) + mass f [z,q] := by
        simp only [V,mass,List.map_append,List.sum_append]
      _ = e := by
        rw [hApnL]
        simp only [mass,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero]
        dsimp only [c,η,Z,qq]
        ring
  refine ⟨R,L,hRsub,hLR,hRtag,?_,legal_of_strip inv.nodup hsV,hsV,?_,
    inv,hG,hU,hH,hHstrict,hJ,hEnd,he.1,he.2⟩
  · intro i hi
    exact hsmallR i hi
  · intro j
    simpa [mass,f,V,n] using inStrip_prefix hsV j

set_option maxHeartbeats 1200000 in
/-- A selector on the actual positive inventory supplies a complete physical
three-LARGE exchange, including every original-zero-start prefix and exact costs. -/
theorem actualSource_threeLarge_return_exchange_full
    (k t : ℕ) (hk : 3 ≤ k) (p q y zpen z : Fin k)
    (A T0 T1 T2 E : List (Fin k))
    (hpositive : 0 < s k t p)
    (hnlarge : Q k ≤ |s k t (hit k 1 p)|)
    (hexpand : N k < 3 * |s k t p|)
    (hW : Legal k t (oldWord p y zpen z A T0 T1 T2 E))
    (hpunused : p ∉ oldWord p y zpen z A T0 T1 T2 E)
    (hnunused : hit k 1 p ∉ oldWord p y zpen z A T0 T1 T2 E)
    (hqunused : q ∉ oldWord p y zpen z A T0 T1 T2 E)
    (hsmall : ∀ i ∈ smallWord T0 T1 T2 E, |s k t i| < Q k)
    (hylarge : Q k ≤ -s k t y)
    (hzpenlarge : Q k ≤ -s k t zpen)
    (hzlarge : Q k ≤ -s k t z)
    (hzupper : -s k t z ≤ s k t q)
    (hqlarge : Q k ≤ s k t q)
    (hqsmaller : s k t q < s k t p)
    (hselect : ∀ low : ℤ, 0 < low →
      low ≤ mass (s k t) (positive t (smallWord T0 T1 T2 E)) →
      ∃ R : List (Fin k), R.Subperm (positive t (smallWord T0 T1 T2 E)) ∧
        low ≤ mass (s k t) R ∧ mass (s k t) R ≤ low + (C k - s k t q)) :
    let n := hit k 1 p
    let x := hit k 2 p
    let W := oldWord p y zpen z A T0 T1 T2 E
    let S := smallWord T0 T1 T2 E
    let e0 := prospective k t p q y zpen W
    ∃ R L : List (Fin k),
      R.Subperm (positive t S) ∧ (L ++ R).Perm S ∧
      (∀ i ∈ R, 0 < s k t i ∧ |s k t i| < Q k) ∧
      (let V := A ++ [p, n] ++ L ++ [z, q]
       let returned := [x, y, zpen] ++ R
       let e := e0 - mass (s k t) R
       Legal k t V ∧ InStrip (s k t) (C k) 0 V ∧
       (∀ j : ℕ, 0 ≤ mass (s k t) (V.take j) ∧
         mass (s k t) (V.take j) ≤ C k) ∧
       Inventory k t W V [p, n, q] returned ∧
       G k t V = G k t W ∧ U V = U W + R.length ∧
       H k t V + 3 ^ (s k t x).natAbs + 3 ^ (s k t y).natAbs +
         3 ^ (s k t zpen).natAbs =
         H k t W + 3 ^ (s k t p).natAbs + 3 ^ (s k t n).natAbs +
           3 ^ (s k t q).natAbs ∧
       H k t V < H k t W ∧ J k t V < J k t W ∧
       mass (s k t) V = e ∧ s k t q ≤ e ∧ e ≤ C k) := by
  classical
  let S := smallWord T0 T1 T2 E
  let Pos := positive t S
  obtain ⟨R, L, hRS, hLR, hRPos, hsmallR, hfull⟩ :=
    actualSource_threeLarge_tagged_exchange_full k t (fun R => R.Subperm Pos)
      hk p q y zpen z A T0 T1 T2 E hpositive hnlarge hexpand hW
      hpunused hnunused hqunused hsmall hylarge hzpenlarge hzlarge
      hzupper hqlarge hqsmaller List.nil_subperm (by
        intro low hlow hsupply
        obtain ⟨R, hR, hlo, hhi⟩ := hselect low hlow hsupply
        exact ⟨R, hR.trans List.filter_sublist.subperm, hR, hlo, hhi⟩)
  refine ⟨R, L, hRPos, hLR, ?_, hfull⟩
  intro i hi
  have hipos : 0 < s k t i := by
    exact of_decide_eq_true (List.mem_filter.mp (hRPos.subset hi)).2
  exact ⟨hipos, hsmallR i hi⟩

set_option maxHeartbeats 1200000 in
/-- A real SMALL doubling packet supplies the returned positive labels.
The literal exchange checks every natural prefix, preserves G and strictly
lowers H, with its entire physical inventory and exact endpoint exposed. -/
theorem actualSource_threeLarge_packet_exchange_full
    (k t : ℕ) (hk : 3 ≤ k) (p q y zpen z b : Fin k)
    (A T0 T1 T2 E : List (Fin k))
    (hpositive : 0 < s k t p)
    (hnlarge : Q k ≤ |s k t (hit k 1 p)|)
    (hexpand : N k < 3 * |s k t p|)
    (hW : Legal k t (oldWord p y zpen z A T0 T1 T2 E))
    (hpunused : p ∉ oldWord p y zpen z A T0 T1 T2 E)
    (hnunused : hit k 1 p ∉ oldWord p y zpen z A T0 T1 T2 E)
    (hqunused : q ∉ oldWord p y zpen z A T0 T1 T2 E)
    (hsmall : ∀ i ∈ smallWord T0 T1 T2 E, |s k t i| < Q k)
    (hylarge : Q k ≤ -s k t y)
    (hzpenlarge : Q k ≤ -s k t zpen)
    (hzlarge : Q k ≤ -s k t z)
    (hzupper : -s k t z ≤ s k t q)
    (hqlarge : Q k ≤ s k t q)
    (hqsmaller : s k t q < s k t p)
    (hb : b ∈ smallWord T0 T1 T2 E)
    (hcb : finRotate k b ∈ smallWord T0 T1 T2 E)
    (hβpositive : 0 < s k t b)
    (hpacketCover : ∀ i ∈ smallWord T0 T1 T2 E,
        0 < s k t i → s k t i ≤ 3 * s k t b + (C k - s k t q)) :
    let n := hit k 1 p
    let x := hit k 2 p
    let W := oldWord p y zpen z A T0 T1 T2 E
    let S := smallWord T0 T1 T2 E
    let e0 := prospective k t p q y zpen W
    ∃ R L : List (Fin k),
      s k t (finRotate k b) = 2 * s k t b ∧
      R.Subperm (positive t S) ∧ (L ++ R).Perm S ∧
      (∀ i ∈ R, 0 < s k t i ∧ |s k t i| < Q k) ∧
      (let V := A ++ [p, n] ++ L ++ [z, q]
       let returned := [x, y, zpen] ++ R
       let e := e0 - mass (s k t) R
       Legal k t V ∧ InStrip (s k t) (C k) 0 V ∧
       (∀ j : ℕ, 0 ≤ mass (s k t) (V.take j) ∧
         mass (s k t) (V.take j) ≤ C k) ∧
       Inventory k t W V [p, n, q] returned ∧
       G k t V = G k t W ∧ U V = U W + R.length ∧
       H k t V + 3 ^ (s k t x).natAbs + 3 ^ (s k t y).natAbs +
         3 ^ (s k t zpen).natAbs =
         H k t W + 3 ^ (s k t p).natAbs + 3 ^ (s k t n).natAbs +
           3 ^ (s k t q).natAbs ∧
       H k t V < H k t W ∧ J k t V < J k t W ∧
       mass (s k t) V = e ∧ s k t q ≤ e ∧ e ≤ C k) := by
  classical
  dsimp only
  let f := s k t
  let β := f b
  let B := C k - f q
  let S := smallWord T0 T1 T2 E
  let Pos := positive t S
  have geo := native_geometry hk t p hnlarge hexpand
  obtain ⟨hQ, hN, hC, hNpos, hNodd⟩ := source_geometry hk
  change 2 ≤ Q k at hQ
  change N k = 4 * Q k - 1 at hN
  change C k = 2 * Q k - 1 at hC
  have hβpos : 0 < β := hβpositive
  have hcycle := (ZeroSumSubsets.source_cycle (by omega : 0 < k) t).2.2
  have hbsmall : |β| < Q k := hsmall b hb
  have hcval : f (finRotate k b) = 2 * β := by
    have he := hcycle b
    change 2 * β - f (finRotate k b) = N k *
      (if N k < 4 * β then 1 else if 4 * β < -N k then -1 else 0) at he
    have hba := abs_lt.mp hbsmall
    rw [ite_eq_right (by ((try dsimp only [f,S,Pos,β,B] at *); source_arith)), ite_eq_right (by ((try dsimp only [f,S,Pos,β,B] at *); source_arith))] at he
    ((try dsimp only [f,S,Pos,β,B] at *); source_arith)
  have hβB : β ≤ B := by
    have hbudget := geo.budget
    change 2 * |f p| ≤ C k + Q k at hbudget
    rw [abs_of_pos hpositive] at hbudget
    have hcbsmall : |f (finRotate k b)| < Q k := hsmall _ hcb
    rw [hcval, abs_of_pos (by omega : 0 < 2 * β)] at hcbsmall
    dsimp only [B, f] at *
    omega
  have hbc : b ≠ finRotate k b := by
    intro hh
    have he := congrArg f hh
    rw [hcval] at he
    ((try dsimp only [f,S,Pos,β,B] at *); source_arith)
  have hbPos : b ∈ Pos := by
    simp only [Pos, positive, List.mem_filter, decide_eq_true_eq]
    exact ⟨hb, hβpos⟩
  have hcPos : finRotate k b ∈ Pos := by
    simp only [Pos, positive, List.mem_filter, decide_eq_true_eq]
    exact ⟨hcb, by change 0 < f (finRotate k b); rw [hcval]; omega⟩
  have hentry (i : Fin k) (hi : i ∈ Pos) :
      0 < f i ∧ f i ≤ 3 * β + B := by
    have hm : i ∈ S ∧ 0 < f i := by
      simpa only [Pos, positive, List.mem_filter, decide_eq_true_eq] using hi
    exact ⟨hm.2, hpacketCover i hm.1 hm.2⟩
  obtain ⟨R,L,hR,hLR,hpos,hV⟩ := actualSource_threeLarge_return_exchange_full
    k t hk p q y zpen z A T0 T1 T2 E hpositive hnlarge hexpand hW
    hpunused hnunused hqunused hsmall hylarge hzpenlarge hzlarge hzupper
    hqlarge hqsmaller (by
      intro low hlow htotal
      exact packet_select f Pos b (finRotate k b) β B low hbPos hcPos hbc
        rfl hcval hβpos hβB hlow hentry htotal)
  exact ⟨R,L,hcval,hR,hLR,hpos,hV⟩

#print axioms actualSource_threeLarge_packet_exchange_full

end D5.S3.Combinatorics.Circle.ThreeLargePacketExchange
