/- GID: D5/S3/Combinatorics/Circle/PositiveSmallReturnExchange
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/PositiveSmallReturnExchange
   mirror-E: none(waiver:audit-open-22063)
   anchors: [mathlib/module/Mathlib.Data.List.Perm.Basic]
   utility: none
   digest: Greedy selection of actual short positive SMALL returns yields a physical strict-G exchange. -/
module
public import D5.S3.Combinatorics.Circle.TerminalLargeSubstitution
public import Mathlib.Data.List.Perm.Basic

/-! A greedy physical SMALL return selection gives a literal strict-G exchange. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
namespace D5.S3.Combinatorics.Circle.PositiveSmallReturnExchange
open SourceWidth ExpandingSourcePath MixedSuffixEnergy SmallStepOrdering
open TwoOppositeLargeExchange
open scoped BigOperators

def oldWord {k : ℕ} (zpen z : Fin k) (F T E : List (Fin k)) : List (Fin k) :=
  F ++ [zpen] ++ T ++ [z] ++ E

def correction (k t : ℕ) (n zpen : Fin k) : ℤ :=
  -s k t zpen - |s k t n|

def eligible {k : ℕ} (t : ℕ) (q : Fin k) (T : List (Fin k)) : List (Fin k) :=
  T.filter (fun i => decide (0 < s k t i ∧ s k t i ≤ C k - s k t q + 1))

local macro "source_arith" : tactic =>
  `(tactic| ((try simp only [s, N, C, Q, Large, mass, List.cons_append,
    List.nil_append, List.map_append, List.map_cons, List.map_nil,
    List.sum_append, List.sum_cons, List.sum_nil, add_zero, zero_add] at *) <;> omega))

/-- A positive bounded physical list has an actual first-crossing sublist. -/
theorem first_crossing {α : Type*} (f : α → ℤ) (S : List α) (B : ℤ)
    (hB : 0 ≤ B) : ∀ low : ℤ, 0 < low →
    (∀ i ∈ S, 0 < f i ∧ f i ≤ B + 1) → low ≤ mass f S →
    ∃ R : List α, R.Sublist S ∧ low ≤ mass f R ∧ mass f R ≤ low + B := by
  induction S with
  | nil =>
    intro low hlow _ htotal
    simp only [mass, List.map_nil, List.sum_nil] at htotal
    omega
  | cons x S ih =>
    intro low hlow hentry htotal
    have hx := hentry x (by simp)
    have ht : ∀ i ∈ S, 0 < f i ∧ f i ≤ B + 1 := by
      intro i hi
      exact hentry i (by simp [hi])
    by_cases hhead : low ≤ f x
    · refine ⟨[x], List.singleton_sublist.mpr (by simp), ?_, ?_⟩
      · simpa [mass] using hhead
      · simp only [mass, List.map_cons, List.map_nil, List.sum_cons,
          List.sum_nil, add_zero]
        omega
    · have hlow' : 0 < low - f x := by omega
      have htail : low - f x ≤ mass f S := by
        simp only [mass, List.map_cons, List.sum_cons] at htotal ⊢
        omega
      obtain ⟨R, hR, hLo, hHi⟩ := ih (low - f x) hlow' ht htail
      refine ⟨x :: R, hR.cons₂ x, ?_, ?_⟩
      · simp only [mass, List.map_cons, List.sum_cons] at hLo ⊢
        omega
      · simp only [mass, List.map_cons, List.sum_cons] at hHi ⊢
        omega

set_option maxHeartbeats 800000 in
/-- Actual short positive SMALL labels are selected constructively. The resulting
literal exchange retains the entire specified remaining SMALL batch and strictly
lowers G, with complete physical inventory, all natural takes and exact balances. -/
theorem actualSource_positiveSmall_return_exchange_full
    (k t : ℕ) (hk : 3 ≤ k) (n q zpen z : Fin k)
    (F T E0 E1 : List (Fin k))
    (hW : Legal k t (oldWord zpen z F T (E0 ++ E1)))
    (hsmall : ∀ i ∈ T ++ E0 ++ E1, |s k t i| < Q k)
    (hnnegative : s k t n < 0)
    (hnlarge : Q k ≤ |s k t n|)
    (hpen : s k t zpen < s k t n)
    (hqpositive : 0 < s k t q)
    (hqlarge : Q k ≤ s k t q)
    (hznegative : s k t z < 0)
    (hzlarge : Q k ≤ -s k t z)
    (hzupper : -s k t z ≤ s k t q)
    (hnunused : n ∉ oldWord zpen z F T (E0 ++ E1))
    (hqunused : q ∉ oldWord zpen z F T (E0 ++ E1))
    (hcover : max 0 (mass (s k t) (oldWord zpen z F T E0) +
        correction k t n zpen - (C k - s k t q)) ≤
      mass (s k t) (eligible t q (T ++ E0))) :
    let W := oldWord zpen z F T (E0 ++ E1)
    let W0 := oldWord zpen z F T E0
    let elig := eligible t q (T ++ E0)
    ∃ Rplus L : List (Fin k), Rplus.Sublist elig ∧
      (L ++ Rplus).Perm (T ++ E0) ∧
      (∀ i ∈ Rplus, 0 < s k t i ∧ s k t i ≤ C k - s k t q + 1) ∧
      max 0 (mass (s k t) W0 + correction k t n zpen -
        (C k - s k t q)) ≤ mass (s k t) Rplus ∧
      mass (s k t) Rplus ≤ mass (s k t) W0 + correction k t n zpen ∧
      (let V := F ++ [n] ++ L ++ [z, q]
       let R := [zpen] ++ Rplus ++ E1
       Legal k t V ∧ InStrip (s k t) (C k) 0 V ∧
       (∀ j : ℕ, 0 ≤ mass (s k t) (V.take j) ∧
         mass (s k t) (V.take j) ≤ C k) ∧
       Inventory k t W V [n, q] R ∧
       G k t V + 1 = G k t W ∧
       U V + 1 = U W + Rplus.length + E1.length ∧
       H k t V + 3 ^ (s k t zpen).natAbs =
         H k t W + 3 ^ (s k t n).natAbs + 3 ^ (s k t q).natAbs ∧
       J k t V < J k t W ∧
       mass (s k t) V = mass (s k t) W0 + correction k t n zpen +
         s k t q - mass (s k t) Rplus) := by
  classical
  dsimp only
  let f := s k t
  let W := oldWord zpen z F T (E0 ++ E1)
  let W0 := oldWord zpen z F T E0
  let D := |f n|
  let ZZ := -f zpen
  let Z := -f z
  let qq := f q
  let δ := ZZ - D
  let v := mass f W0
  let B := C k - qq
  let H0 := v + δ
  let low := H0 - B
  let b0 := mass f F - D
  let S := T ++ E0
  let elig := eligible t q S
  obtain ⟨hQ, hN, hC, hNpos, hNodd⟩ := source_geometry hk
  have hbound (i : Fin k) : |f i| ≤ C k :=
    abs_le.mpr (centered_bounds hNpos hNodd _)
  have hnval : f n = -D := by
    change s k t n = -|s k t n|
    rw [abs_of_neg hnnegative]
    omega
  have hDpos : 0 < D := by ((try dsimp only [f, W, W0, D, ZZ, Z, qq, δ, v, B, H0, low, b0, S, elig] at *); source_arith)
  have hZZD : D < ZZ := by ((try dsimp only [f, W, W0, D, ZZ, Z, qq, δ, v, B, H0, low, b0, S, elig] at *); source_arith)
  have hδpos : 0 < δ := by ((try dsimp only [f, W, W0, D, ZZ, Z, qq, δ, v, B, H0, low, b0, S, elig] at *); source_arith)
  have hqcap : qq ≤ C k := by
    have hb := hbound q
    change |s k t q| ≤ C k at hb
    rw [abs_of_pos hqpositive] at hb
    exact hb
  have hB : 0 ≤ B := by ((try dsimp only [f, W, W0, D, ZZ, Z, qq, δ, v, B, H0, low, b0, S, elig] at *); source_arith)
  have hZ : 0 < Z ∧ Z ≤ qq := by ((try dsimp only [f, W, W0, D, ZZ, Z, qq, δ, v, B, H0, low, b0, S, elig] at *); source_arith)
  have hnL : Large k t n := hnlarge
  have hqL : Large k t q := by
    change Q k ≤ |s k t q|
    rw [abs_of_pos hqpositive]
    exact hqlarge
  have hzpenL : Large k t zpen := by
    have hzpenneg : s k t zpen < 0 := hpen.trans hnnegative
    change Q k ≤ |s k t zpen|
    rw [abs_of_neg hzpenneg]
    have hn := hnlarge
    rw [abs_of_neg hnnegative] at hn
    omega
  have hsW : InStrip f (C k) 0 W := strip_of_legal hW
  have hsF : InStrip f (C k) 0 F :=
    (strip_split F ([zpen] ++ T ++ [z] ++ E0 ++ E1)
      (by simpa only [W, oldWord, List.append_assoc] using hsW)).1
  have hsFpen : InStrip f (C k) 0 (F ++ [zpen]) :=
    (strip_split (F ++ [zpen]) (T ++ [z] ++ E0 ++ E1)
      (by simpa only [W, oldWord, List.append_assoc] using hsW)).1
  have hsW0 : InStrip f (C k) 0 W0 :=
    (strip_split W0 E1 (by simpa only [W, W0, oldWord, List.append_assoc] using hsW)).1
  have hF : 0 ≤ mass f F ∧ mass f F ≤ C k := by
    simpa [mass] using inStrip_prefix hsF F.length
  have hFpen : 0 ≤ mass f F - ZZ := by
    have hh := (inStrip_prefix hsFpen (F ++ [zpen]).length).1
    simp only [List.take_length, zero_add, List.map_append, List.map_cons,
      List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, add_zero] at hh
    ((try dsimp only [f, W, W0, D, ZZ, Z, qq, δ, v, B, H0, low, b0, S, elig] at *); source_arith)
  have hv : 0 ≤ v ∧ v ≤ C k := by
    simpa [v, mass] using inStrip_prefix hsW0 W0.length
  have hH0 : 0 ≤ H0 := by ((try dsimp only [f, W, W0, D, ZZ, Z, qq, δ, v, B, H0, low, b0, S, elig] at *); source_arith)
  have hb0 : 0 ≤ b0 ∧ b0 ≤ C k := by ((try dsimp only [f, W, W0, D, ZZ, Z, qq, δ, v, B, H0, low, b0, S, elig] at *); source_arith)
  have hentry (i : Fin k) (hi : i ∈ elig) :
      i ∈ S ∧ 0 < f i ∧ f i ≤ B + 1 := by
    simpa only [elig, eligible, List.mem_filter, decide_eq_true_eq, f, B, qq] using hi
  have heSub : elig.Sublist S := List.filter_sublist
  have htotal : max 0 low ≤ mass f elig := hcover
  obtain ⟨Rplus, hRplus, hRlo, hRhi⟩ : ∃ Rplus : List (Fin k),
      Rplus.Sublist elig ∧ max 0 low ≤ mass f Rplus ∧ mass f Rplus ≤ H0 := by
    by_cases hlo : low ≤ 0
    · refine ⟨[], List.nil_sublist _, ?_, ?_⟩
      · simp [mass, max_eq_left hlo]
      · simpa [mass] using hH0
    · have hlo' : 0 < low := by omega
      have hsum : low ≤ mass f elig := (le_max_right 0 low).trans htotal
      obtain ⟨R, hR, hLo, hHi⟩ := first_crossing f elig B hB low hlo'
        (fun i hi => (hentry i hi).2) hsum
      refine ⟨R, hR, ?_, ?_⟩
      · rw [max_eq_right (le_of_lt hlo')]
        exact hLo
      · dsimp only [low] at hHi
        omega
  have hRsub : Rplus.Sublist S := hRplus.trans heSub
  let A0 := S.diff Rplus
  have hpart : (A0 ++ Rplus).Perm S := by
    have hp := List.subperm_append_diff_self_of_count_le
      (fun i _ => hRsub.subperm.count_le i)
    exact List.perm_append_comm.trans hp
  have hmasspart : mass f A0 + mass f Rplus = mass f S := by
    simpa [mass] using (hpart.map f).sum_eq
  have hA0sub : A0.Sublist S := List.diff_sublist _ _
  have hsmallS (i : Fin k) (hi : i ∈ S) : |f i| < Q k := by
    apply hsmall i
    exact List.mem_append_left E1 hi
  have hsmallA0 (i : Fin k) (hi : i ∈ A0) : |f i| < Q k :=
    hsmallS i (hA0sub.subset hi)
  have hsmallR (i : Fin k) (hi : i ∈ Rplus) : |f i| < Q k :=
    hsmallS i (hRsub.subset hi)
  have hsmallE1 (i : Fin k) (hi : i ∈ E1) : |s k t i| < Q k := by
    apply hsmall i
    simp [hi]
  let μ := mass f Rplus
  let η := H0 - μ
  let c := η + Z
  let e := η + qq
  have hη : 0 ≤ η ∧ η ≤ B := by
    dsimp only [η, μ]
    dsimp only [low] at hRlo
    omega
  have hc : 0 ≤ c ∧ c ≤ C k := by
    dsimp only [c]
    ((try dsimp only [f, W, W0, D, ZZ, Z, qq, δ, v, B, H0, low, b0, S, elig] at *); source_arith)
  have he : 0 ≤ e ∧ e ≤ C k := by
    dsimp only [e]
    ((try dsimp only [f, W, W0, D, ZZ, Z, qq, δ, v, B, H0, low, b0, S, elig] at *); source_arith)
  have hsum : b0 + mass f A0 = c := by
    dsimp only [c, η, μ]
    dsimp [S, mass] at hmasspart
    dsimp [v, W0, oldWord, b0, H0, δ, ZZ, Z]
    simp only [mass, List.map_append, List.map_cons, List.map_nil,
      List.sum_append, List.sum_cons, List.sum_nil, add_zero]
    ((try dsimp only [f, W, W0, D, ZZ, Z, qq, δ, v, B, H0, low, b0, S, elig] at *); source_arith)
  have hcompat : ∀ p ∈ A0, ∀ m ∈ A0,
      0 < f p → f m < 0 → f p - f m ≤ C k := by
    intro p hp m hm hpp hmm
    have hp' := hsmallA0 p hp
    have hm' := hsmallA0 m hm
    rw [abs_of_pos hpp] at hp'
    rw [abs_of_neg hmm] at hm'
    ((try dsimp only [f, W, W0, D, ZZ, Z, qq, δ, v, B, H0, low, b0, S, elig] at *); source_arith)
  have hend : 0 ≤ b0 + mass f A0 ∧ b0 + mass f A0 ≤ C k := by
    rw [hsum]
    exact hc
  obtain ⟨L, hL, hsL⟩ := exists_order_between f A0 (C k) b0 hb0
    (by simpa only [mass] using hend) hcompat
  have hLR : (L ++ Rplus).Perm S := (hL.append_right Rplus).trans hpart
  have hmassL : mass f L = mass f A0 := by simpa [mass] using (hL.map f).sum_eq
  have hsN : InStrip f (C k) (mass f F) [n] := by
    change 0 ≤ mass f F ∧ mass f F ≤ C k ∧
      0 ≤ mass f F + f n ∧ mass f F + f n ≤ C k
    rw [hnval]
    exact ⟨hF.1, hF.2, by ((try dsimp only [f, W, W0, D, ZZ, Z, qq, δ, v, B, H0, low, b0, S, elig] at *); source_arith), by ((try dsimp only [f, W, W0, D, ZZ, Z, qq, δ, v, B, H0, low, b0, S, elig] at *); source_arith)⟩
  have hsFn : InStrip f (C k) 0 (F ++ [n]) :=
    inStrip_append hsF (by simpa [mass] using hsN)
  have hFn : mass f (F ++ [n]) = b0 := by
    simp [b0, mass, hnval, sub_eq_add_neg]
  have hsFnL : InStrip f (C k) 0 (F ++ [n] ++ L) := by
    apply inStrip_append hsFn
    change InStrip f (C k) (0 + mass f (F ++ [n])) L
    rw [zero_add, hFn]
    exact hsL
  have hFnL : mass f (F ++ [n] ++ L) = c := by
    have hh : mass f (F ++ [n] ++ L) = b0 + mass f L := by
      calc
        mass f (F ++ [n] ++ L) = mass f (F ++ [n]) + mass f L := by
          simp only [mass, List.map_append, List.sum_append]
        _ = b0 + mass f L := congrArg (fun x => x + mass f L) hFn
    rw [hh, hmassL]
    exact hsum
  have hpair : InStrip f (C k) c [z, q] := by
    change 0 ≤ c ∧ c ≤ C k ∧ 0 ≤ c + f z ∧ c + f z ≤ C k ∧
      0 ≤ c + f z + f q ∧ c + f z + f q ≤ C k
    have hcz : c + f z = η := by dsimp [c, Z]; ring
    have hczq : c + f z + f q = e := by dsimp only [e, qq]; rw [hcz]
    rw [hczq, hcz]
    exact ⟨hc.1, hc.2, hη.1, by have hh := he.2; ((try dsimp only [f, W, W0, D, ZZ, Z, qq, δ, v, B, H0, low, b0, S, elig] at *); source_arith), he.1, he.2⟩
  let V := F ++ [n] ++ L ++ [z, q]
  let R := [zpen] ++ Rplus ++ E1
  have hsV : InStrip f (C k) 0 V := by
    apply inStrip_append hsFnL
    change InStrip f (C k) (0 + mass f (F ++ [n] ++ L)) [z, q]
    rw [zero_add, hFnL]
    exact hpair
  have hI : [n, q].Nodup := by
    have hnq : n ≠ q := by intro h; have heq := congrArg f h; ((try dsimp only [f, W, W0, D, ZZ, Z, qq, δ, v, B, H0, low, b0, S, elig] at *); source_arith)
    simp [hnq]
  have hIW (i : Fin k) (hi : i ∈ [n, q]) : i ∉ W := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · exact hnunused
    · exact hqunused
  have hIL (i : Fin k) (hi : i ∈ [n, q]) : Large k t i := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · exact hnL
    · exact hqL
  have hperm : (V ++ R).Perm (W ++ [n, q]) := by
    apply List.perm_iff_count.mpr
    intro i
    have hh := hLR.count_eq i
    simp only [S, List.count_append] at hh
    simp only [V, R, W, oldWord, List.count_append, List.count_cons, List.count_nil]
    omega
  have hRold (i : Fin k) (hi : i ∈ R) : i ∈ W := by
    simp only [R, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with (rfl | hi) | hi
    · simp [W, oldWord]
    · have hb := hRsub.subset hi
      rcases List.mem_append.mp hb with ht | he0
      · simp [W, oldWord, ht]
      · simp [W, oldWord, he0]
    · simp [W, oldWord, hi]
  have inv : Inventory k t W V [n, q] R :=
    inventory_of_perm hk t W V [n, q] R hW.1 hI hIW hRold hIL hperm
  have hrweights := small_weights t Rplus hsmallR
  have heweights := small_weights t E1 hsmallE1
  have hRlarge : largeUsed k t R = 1 := by
    simp [R, largeWeight, hzpenL, hrweights.1, heweights.1]
  have hRenergy : H k t R = 3 ^ (f zpen).natAbs := by
    simp [R, energyWeight, hzpenL, hrweights.2, heweights.2, f, s]
  have hIlarge : largeUsed k t [n, q] = 2 := by
    simp [largeWeight, hnL, hqL]
  have hIenergy : H k t [n, q] = 3 ^ (f n).natAbs + 3 ^ (f q).natAbs := by
    simp [energyWeight, hnL, hqL, f, s]
  have hG : G k t V + 1 = G k t W := by
    have hh := inv.largeBalance
    rw [hRlarge, hIlarge] at hh
    omega
  have hU : U V + 1 = U W + Rplus.length + E1.length := by
    have hh := inv.countBalance
    simp only [R, List.length_append, List.length_cons, List.length_nil] at hh
    omega
  have hH : H k t V + 3 ^ (f zpen).natAbs =
      H k t W + 3 ^ (f n).natAbs + 3 ^ (f q).natAbs := by
    have hh := inv.energyBalance
    rw [hRenergy, hIenergy] at hh
    omega
  have hJ : J k t V < J k t W := by
    apply Prod.Lex.toLex_lt_toLex.mpr
    exact Or.inl (by omega)
  have hEnd : mass f V = v + δ + qq - mass f Rplus := by
    have hp := (hperm.map f).sum_eq
    simp only [V, R, W, oldWord, List.map_append, List.map_cons, List.map_nil,
      List.sum_append, List.sum_cons, List.sum_nil, add_zero] at hp
    dsimp [V, v, W0, oldWord]
    simp only [mass, List.map_append, List.map_cons, List.map_nil,
      List.sum_append, List.sum_cons, List.sum_nil, add_zero]
    ((try dsimp only [f, W, W0, D, ZZ, Z, qq, δ, v, B, H0, low, b0, S, elig] at *); source_arith)
  refine ⟨Rplus, L, hRplus, hLR, ?_, hRlo, hRhi,
    legal_of_strip inv.nodup hsV, hsV, ?_, inv, hG, hU, hH, hJ, hEnd⟩
  · intro i hi
    exact (hentry i (hRplus.subset hi)).2
  · intro j
    simpa [mass, f, V] using inStrip_prefix hsV j

#print axioms actualSource_positiveSmall_return_exchange_full

end D5.S3.Combinatorics.Circle.PositiveSmallReturnExchange
