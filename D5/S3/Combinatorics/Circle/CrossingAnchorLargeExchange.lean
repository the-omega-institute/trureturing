/- GID: D5/S3/Combinatorics/Circle/CrossingAnchorLargeExchange
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/CrossingAnchorLargeExchange
   mirror-E: none(waiver:audit-open-22063)
   anchors: [mathlib/module/Mathlib.Logic.Equiv.Fin.Rotate]
   utility: none
   digest: A native crossing anchor closes the three-negative residual with all SMALL retained. -/
module
public import D5.S3.Combinatorics.Circle.CrossingAnchorOrdering

/-! A full physical exchange from native crossing data, with unchanged SMALL inventory. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
namespace D5.S3.Combinatorics.Circle.CrossingAnchorLargeExchange
open SourceWidth ExpandingSourcePath MixedSuffixEnergy SmallStepOrdering
open TwoOppositeLargeExchange ThreeLargePacketExchange CrossingAnchorOrdering
open scoped BigOperators

set_option maxHeartbeats 1800000 in
/-- In the native q≤P three-negative residual, the actual crossing
anchor orders both retained negative LARGE and every SMALL occurrence,
with arbitrary old q status and no q-to-zpen source edge.
The theorem constructs the full word; it assumes no packet or new Legal word. -/
theorem actualSource_threeNegative_crossingAnchor_exchange_full
    (k t : ℕ) (hk : 3 ≤ k) (p q y zpen z a : Fin k)
    (A T0 T1 T2 E : List (Fin k))
    (hpositive : 0 < s k t p)
    (hnlarge : Q k ≤ |s k t (hit k 1 p)|)
    (hexpand : N k < 3 * |s k t p|)
    (hW : Legal k t (oldWord p y zpen z A T0 T1 T2 E))
    (hpunused : p ∉ oldWord p y zpen z A T0 T1 T2 E)
    (hnunused : hit k 1 p ∉ oldWord p y zpen z A T0 T1 T2 E)
    (hsmall : ∀ i ∈ smallWord T0 T1 T2 E, |s k t i| < Q k)
    (hylarge : Q k ≤ -s k t y)
    (hzpenlarge : Q k ≤ -s k t zpen)
    (hzlarge : Q k ≤ -s k t z)
    (hzupper : -s k t z ≤ |s k t (hit k 1 p)|)
    (ha : a ∈ smallWord T0 T1 T2 E) (hapositive : 0 < s k t a)
    (hq : hit k 1 a = q)
    (hqnobigger : s k t q ≤ s k t p)
    (hcrosslo : C k - s k t q < mass (s k t) (oldWord p y zpen z A T0 T1 T2 E))
    (hcrosshi : mass (s k t) (oldWord p y zpen z A T0 T1 T2 E) <
      s k t a - (-s k t zpen - |s k t (hit k 1 p)|))
    (hblocklo : C k - s k t p < mass (s k t) (oldWord p y zpen z A T0 T1 T2 E))
    (hblockhi : mass (s k t) (oldWord p y zpen z A T0 T1 T2 E) <
      |s k t (hit k 1 p)|) :
    let n := hit k 1 p
    let x := hit k 2 p
    let W := oldWord p y zpen z A T0 T1 T2 E
    let S := smallWord T0 T1 T2 E
    let Btail := T0 ++ [y] ++ T1 ++ [zpen] ++ T2 ++ [z] ++ E
    ∃ j : Fin k, ∃ L : List (Fin k),
      j ∈ [y, zpen, z] ∧ (∀ i ∈ [y, zpen, z], -s k t i ≤ -s k t j) ∧
      (L ++ [j]).Perm Btail ∧ (∀ i ∈ S, i ∈ L) ∧
      (let V := A ++ [p, n] ++ L
       let e0 := mass (s k t) W - s k t j - s k t p
       Legal k t V ∧ V.Nodup ∧ InStrip (s k t) (C k) 0 V ∧
       (∀ d : ℕ, 0 ≤ mass (s k t) (V.take d) ∧ mass (s k t) (V.take d) ≤ C k) ∧
       Inventory k t W V [p, n] [x, j] ∧
       (V ++ [x, j]).Perm (W ++ [p, n]) ∧
       (∀ i ∈ W, |s k t i| < Q k → i ∈ V) ∧
       G k t V = G k t W ∧ U V = U W ∧
       remainingSmall t V = remainingSmall t W ∧
       H k t V + 3 ^ (s k t x).natAbs + 3 ^ (s k t j).natAbs =
         H k t W + 3 ^ (s k t p).natAbs + 3 ^ (s k t n).natAbs ∧
       H k t V < H k t W ∧ J k t V < J k t W ∧
       (q ∈ V ↔ q ∈ W ∨ q = p) ∧ mass (s k t) V = e0 ∧ 0 < e0 ∧ e0 < C k ∧
       remainingMass (s k t) V = -e0) := by
  classical
  dsimp only
  let f := s k t
  let n := hit k 1 p
  let x := hit k 2 p
  let W := oldWord p y zpen z A T0 T1 T2 E
  let S := smallWord T0 T1 T2 E
  let Btail := T0 ++ [y] ++ T1 ++ [zpen] ++ T2 ++ [z] ++ E
  let P := f p
  let D := |f n|
  let r := |f x|
  let aa := f a
  let qq := f q
  let ZZ := -f zpen
  let Z := -f z
  let Y := -f y
  let δ := ZZ - D
  let h := mass f W
  let a0 := mass f A
  let b := a0 + P - D
  have geo := native_geometry hk t p hnlarge hexpand
  obtain ⟨hQ, hN, hC, hNpos, hodd⟩ := source_geometry hk
  change 2 ≤ Q k at hQ
  change N k = 4 * Q k - 1 at hN
  change C k = 2 * Q k - 1 at hC
  have hpabs : |f p| = P := abs_of_pos hpositive
  have hnval : f n = -D := by
    simpa [f, n, D, orient, show ¬ s k t p < 0 by omega] using geo.nValue
  have hxval : f x = r := by
    simpa [f, x, r, orient, show ¬ s k t p < 0 by omega] using geo.xValue
  have hDP : D < P := by
    have hh := geo.strictOrder.1
    change D < |f p| at hh
    simpa only [hpabs] using hh
  have hPr : P < r := by
    have hh := geo.strictOrder.2
    change |f p| < r at hh
    simpa only [hpabs] using hh
  have hD : Q k ≤ D := hnlarge
  have hDeq : D = N k - 2 * P := by
    have hh := geo.firstEquation
    change D = N k - 2 * |f p| at hh
    simpa only [hpabs] using hh
  have hreq : r = 2 * P - D := by
    have hh := geo.secondEquation
    rw [hpabs] at hh
    change r = 4 * P - N k at hh
    omega
  have hbudget : 2 * P ≤ C k + Q k := by
    have hh := geo.budget
    change 2 * |f p| ≤ C k + Q k at hh
    simpa only [hpabs] using hh
  have hbound (i : Fin k) : |f i| ≤ C k :=
    abs_le.mpr (centered_bounds hNpos hodd _)
  have hrC : r ≤ C k := hbound x
  have ha0 : 0 < aa := hapositive
  have haa : aa < Q k := by
    have hh := hsmall a ha
    change |aa| < Q k at hh
    rw [abs_of_pos ha0] at hh
    exact hh
  have hqrot : finRotate k a = q := by simpa [hit] using hq
  have hcycle := (ZeroSumSubsets.source_cycle (by omega : 0 < k) t).2.2
  have hqeq : qq = 2 * aa := by
    have hh := hcycle a
    rw [hqrot] at hh
    change 2 * aa - qq = N k *
      (if N k < 4 * aa then 1 else if 4 * aa < -N k then -1 else 0) at hh
    rw [ite_eq_right (by omega), ite_eq_right (by omega)] at hh
    omega
  have hqpos : 0 < qq := by omega
  have hZZQ : Q k ≤ ZZ := hzpenlarge
  have hqP : qq ≤ P := hqnobigger
  have hDaa : D ≤ N k - 4 * aa := by omega
  have hZQ : Q k ≤ Z := hzlarge
  have hZD : Z ≤ D := hzupper
  have hZZC : ZZ ≤ C k := le_trans (neg_le_abs _) (hbound zpen)
  have hYC : Y ≤ C k := le_trans (neg_le_abs _) (hbound y)
  have hYQ : Q k ≤ Y := hylarge
  have hZC : Z ≤ C k := le_trans (neg_le_abs _) (hbound z)
  have hclo : C k - qq < h := hcrosslo
  have hchi : h < aa - δ := hcrosshi
  have haa3 : 2 * Q k + δ + 1 ≤ 3 * aa := by omega
  have h3P : 4 * Q k ≤ 3 * P := by
    have hh : N k < 3 * P := by simpa [← hpabs] using hexpand
    omega
  have h3D : 3 * D ≤ 4 * Q k - 3 := by omega
  obtain ⟨j, v1, v2, hj, hjmax, htriple, hv1, hv2, hM, hsum⟩ :
      ∃ j v1 v2 : Fin k, j ∈ [y, zpen, z] ∧
        (∀ i ∈ [y, zpen, z], -f i ≤ -f j) ∧
        [v1, v2, j].Perm [y, zpen, z] ∧
        (Q k ≤ -f v1 ∧ -f v1 ≤ C k) ∧
        (Q k ≤ -f v2 ∧ -f v2 ≤ C k) ∧
        max (-f v1) (-f v2) ≤ max D ZZ ∧
        -f v1 + -f v2 ≤ ZZ + Z := by
    by_cases hY : ZZ ≤ Y
    · by_cases hYZ : Z ≤ Y
      · refine ⟨y, zpen, z, by simp, ?_, ?_, ⟨hZZQ, hZZC⟩, ⟨hZQ, hZC⟩, ?_, ?_⟩
        · intro i hi
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
          rcases hi with rfl | rfl | rfl <;> change _ ≤ Y <;> omega
        · exact List.perm_append_comm (l₁ := [zpen, z]) (l₂ := [y])
        · change max ZZ Z ≤ max D ZZ
          exact max_le (le_max_right _ _) (le_trans hZD (le_max_left _ _))
        · change ZZ + Z ≤ ZZ + Z; rfl
      · refine ⟨z, y, zpen, by simp, ?_, ?_, ⟨hYQ, hYC⟩, ⟨hZZQ, hZZC⟩, ?_, ?_⟩
        · intro i hi
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
          rcases hi with rfl | rfl | rfl <;> change _ ≤ Z <;> omega
        · exact List.Perm.refl _
        · change max Y ZZ ≤ max D ZZ
          exact max_le (le_trans (by omega : Y ≤ D) (le_max_left _ _)) (le_max_right _ _)
        · change Y + ZZ ≤ ZZ + Z; omega
    · by_cases hZZ : Z ≤ ZZ
      · refine ⟨zpen, y, z, by simp, ?_, ?_, ⟨hYQ, hYC⟩, ⟨hZQ, hZC⟩, ?_, ?_⟩
        · intro i hi
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
          rcases hi with rfl | rfl | rfl <;> change _ ≤ ZZ <;> omega
        · exact (List.Perm.swap zpen z []).cons y
        · change max Y Z ≤ max D ZZ
          exact max_le (le_trans (by omega : Y ≤ ZZ) (le_max_right _ _))
            (le_trans hZD (le_max_left _ _))
        · change Y + Z ≤ ZZ + Z; omega
      · refine ⟨z, y, zpen, by simp, ?_, ?_, ⟨hYQ, hYC⟩, ⟨hZZQ, hZZC⟩, ?_, ?_⟩
        · intro i hi
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
          rcases hi with rfl | rfl | rfl <;> change _ ≤ Z <;> omega
        · exact List.Perm.refl _
        · change max Y ZZ ≤ max D ZZ
          exact max_le (le_trans (by omega : Y ≤ ZZ) (le_max_right _ _)) (le_max_right _ _)
        · change Y + ZZ ≤ ZZ + Z; omega
  let M := max (-f v1) (-f v2)
  let c := C k - M
  let e0 := h - f j - P
  have hMQ : Q k ≤ M := le_trans hv1.1 (le_max_left _ _)
  have hMC : M ≤ C k := max_le hv1.2 hv2.2
  have hanchorscalar : aa ≤ C k - max D ZZ ∧ 2 * D + δ < aa + C k := by
    by_cases hδ : δ ≤ 0
    · have hmax : max D ZZ = D := max_eq_left (by dsimp only [δ] at hδ; omega)
      rw [hmax]
      constructor <;> omega
    · have hmax : max D ZZ = ZZ := max_eq_right (by dsimp only [δ] at hδ; omega)
      have hZZupper : ZZ ≤ 2 * Q k - aa - 2 := by
        dsimp only [δ] at haa3
        omega
      rw [hmax]
      constructor <;> omega
  have hanchor : 0 < aa ∧ aa ≤ c ∧ min (-f v1) (-f v2) < aa + c := by
    change M ≤ max D ZZ at hM
    have hsum' : -f v1 + -f v2 ≤ 2 * D + δ := by dsimp only [δ]; omega
    have hsplit := max_add_min (-f v1) (-f v2)
    change M + min (-f v1) (-f v2) = _ at hsplit
    dsimp only [c]
    exact ⟨ha0, by omega, by omega⟩
  have hjQ : Q k ≤ -f j := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl | rfl <;> assumption
  have hjC : -f j ≤ C k := le_trans (neg_le_abs _) (hbound j)
  have htailpart : (S ++ [y, zpen, z]).Perm Btail := by
    apply List.perm_iff_count.mpr
    intro i
    simp only [S, smallWord, Btail, List.count_append, List.count_cons, List.count_nil]
    omega
  have htailj : (S ++ [v1, v2] ++ [j]).Perm Btail := by
    have hp : (S ++ [v1, v2] ++ [j]).Perm (S ++ [y, zpen, z]) := by
      simpa only [List.append_assoc, List.cons_append, List.nil_append] using htriple.append_left S
    exact hp.trans htailpart
  have hWshape : W = A ++ [x] ++ Btail := by simp [W, oldWord, Btail, x, List.append_assoc]
  have hBnd : Btail.Nodup := by
    have hw : (A ++ [x] ++ Btail).Nodup := by
      simpa only [← hWshape] using hW.1
    exact (List.nodup_append.mp hw).2.1
  have hSnd : (S ++ [v1, v2]).Nodup :=
    (List.nodup_append.mp (htailj.nodup_iff.mpr hBnd)).1
  have hsW : InStrip f (C k) 0 W := strip_of_legal hW
  obtain ⟨hsA, hsTail⟩ := strip_split A ([x] ++ Btail)
    (by simpa only [hWshape, List.append_assoc] using hsW)
  have hAheight : 0 ≤ a0 ∧ a0 ≤ C k := by
    simpa [a0, mass] using inStrip_prefix hsTail 0
  have hAx : 0 ≤ a0 + r ∧ a0 + r ≤ C k := by
    simpa [a0, mass, hxval] using inStrip_prefix hsTail 1
  have hb : 0 ≤ b ∧ b ≤ Q k - 1 := by dsimp only [b]; omega
  have he0 : 0 < e0 ∧ e0 < C k := by
    have hlo : C k - P < h := hblocklo
    have hhi : h < D := hblockhi
    dsimp only [e0]
    omega
  have heq : b + mass f S + f v1 + f v2 = e0 := by
    have ht : mass f S + f v1 + f v2 + f j = mass f Btail := by
      have hh := (htailj.map f).sum_eq
      simp only [List.map_append, List.map_cons, List.map_nil,
        List.sum_append, List.sum_cons, List.sum_nil, add_zero] at hh
      dsimp only [mass]
      omega
    have hw : h = a0 + r + mass f Btail := by
      simp [h, hWshape, mass, a0, hxval, add_assoc]
    dsimp only [b, e0]
    omega
  obtain ⟨L, hL, hsL, hLend, _⟩ := exists_order_two_negative f S v1 v2 a (Q k) (C k) b e0
    hQ hC hSnd hsmall hv1 hv2 ha hanchor.1 hanchor.2.1
    (le_of_lt hanchor.2.2) hb ⟨by omega, by omega⟩ heq
  have hLj : (L ++ [j]).Perm Btail := (hL.append_right _).trans htailj
  have hSretained (i : Fin k) (hi : i ∈ S) : i ∈ L :=
    hL.mem_iff.mpr (List.mem_append_left _ hi)
  have hsPN : InStrip f (C k) a0 [p, n] := by
    change 0 ≤ a0 ∧ a0 ≤ C k ∧ 0 ≤ a0 + f p ∧ a0 + f p ≤ C k ∧
      0 ≤ a0 + f p + f n ∧ a0 + f p + f n ≤ C k
    rw [hnval]
    change 0 ≤ a0 ∧ a0 ≤ C k ∧ 0 ≤ a0 + P ∧ a0 + P ≤ C k ∧
      0 ≤ a0 + P + -D ∧ a0 + P + -D ≤ C k
    dsimp only [b] at hb
    omega
  have hsAPN : InStrip f (C k) 0 (A ++ [p, n]) :=
    inStrip_append hsA (by simpa [a0, mass] using hsPN)
  have hAPN : mass f (A ++ [p, n]) = b := by
    simp only [mass, List.map_append, List.map_cons, List.map_nil,
      List.sum_append, List.sum_cons, List.sum_nil, add_zero, hnval]
    dsimp only [b, a0, P, mass]
    ring
  let V := A ++ [p, n] ++ L
  have hsV : InStrip f (C k) 0 V := by
    apply inStrip_append hsAPN
    change InStrip f (C k) (0 + mass f (A ++ [p, n])) L
    rw [zero_add, hAPN]
    exact hsL
  have hEnd : mass f V = e0 := by
    have hm : mass f V = mass f (A ++ [p, n]) + mass f L := by
      simp [V, mass, add_assoc]
    rw [hm, hAPN]
    exact hLend
  have hI : [p, n].Nodup := by
    have hpn : p ≠ n := by intro hh; have hv := congrArg f hh; omega
    simp [hpn]
  have hIW (i : Fin k) (hi : i ∈ [p, n]) : i ∉ W := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · exact hpunused
    · exact hnunused
  have hIL (i : Fin k) (hi : i ∈ [p, n]) : Large k t i := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · exact geo.pLarge
    · exact geo.nLarge
  have hperm : (V ++ [x, j]).Perm (W ++ [p, n]) := by
    apply List.perm_iff_count.mpr
    intro i
    have hp := hLj.count_eq i
    simp only [List.count_append, List.count_cons, List.count_nil] at hp
    simp only [V, hWshape, List.count_append, List.count_cons, List.count_nil]
    omega
  have hRold (i : Fin k) (hi : i ∈ [x, j]) : i ∈ W := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with hix | hij
    · subst i; simp [hWshape]
    · subst i
      have hjB : j ∈ Btail := hLj.mem_iff.mp (by simp)
      simp [hWshape, hjB]
  have inv : Inventory k t W V [p, n] [x, j] :=
    inventory_of_perm hk t W V [p, n] [x, j] hW.1 hI hIW hRold hIL hperm
  have hxLarge : Large k t x := geo.xLarge
  have hjLarge : Large k t j := by
    have hh := neg_le_abs (f j)
    unfold Large
    change Q k ≤ |f j|
    omega
  have hRlarge : largeUsed k t [x, j] = 2 := by
    simp [largeUsed, mass, largeWeight, hxLarge, hjLarge]
  have hIlarge : largeUsed k t [p, n] = 2 := by
    simp [largeUsed, mass, largeWeight, geo.pLarge, show Large k t n from geo.nLarge]
  have hRenergy : H k t [x, j] = 3 ^ (f x).natAbs + 3 ^ (f j).natAbs := by
    simp [H, mass, energyWeight, hxLarge, hjLarge, f, s]
  have hIenergy : H k t [p, n] = 3 ^ (f p).natAbs + 3 ^ (f n).natAbs := by
    simp [H, mass, energyWeight, geo.pLarge, show Large k t n from geo.nLarge, f, s]
  have hG : G k t V = G k t W := by
    have hh := inv.largeBalance
    rw [hRlarge, hIlarge] at hh
    omega
  have hU : U V = U W := by
    have hh := inv.countBalance
    simp only [List.length_cons, List.length_nil] at hh
    omega
  have hH : H k t V + 3 ^ (f x).natAbs + 3 ^ (f j).natAbs =
      H k t W + 3 ^ (f p).natAbs + 3 ^ (f n).natAbs := by
    have hh := inv.energyBalance
    rw [hRenergy, hIenergy] at hh
    omega
  have hHstrict : H k t V < H k t W := by
    have hh := geo.energy
    change 3 ^ (f p).natAbs + 3 ^ (f n).natAbs < 3 ^ (f x).natAbs at hh
    have hright := Nat.add_lt_add_left hh (H k t W)
    have hleft : (H k t V + 3 ^ (f j).natAbs) + 3 ^ (f x).natAbs <
        H k t W + 3 ^ (f x).natAbs := by
      calc
        _ = H k t W + (3 ^ (f p).natAbs + 3 ^ (f n).natAbs) := by
          simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hH
        _ < _ := hright
    exact lt_of_le_of_lt (Nat.le_add_right _ _) (Nat.lt_of_add_lt_add_right hleft)
  have hJ : J k t V < J k t W := by
    apply Prod.Lex.toLex_lt_toLex.mpr
    exact Or.inr ⟨hG, Prod.Lex.toLex_lt_toLex.mpr (Or.inl hHstrict)⟩
  have hRfilter : ([x, j] : List (Fin k)).toFinset.filter (fun i => ¬ Large k t i) = ∅ := by
    ext i
    simp only [Finset.mem_filter, List.mem_toFinset, List.mem_cons,
      List.not_mem_nil, or_false, Finset.notMem_empty, iff_false, not_and]
    rintro (rfl | rfl) hn
    · exact hn hxLarge
    · exact hn hjLarge
  have hSmall : remainingSmall t V = remainingSmall t W := by
    simpa only [hRfilter, Finset.union_empty] using inv.smallPartition
  have hretain (i : Fin k) (hi : i ∈ W) (his : |s k t i| < Q k) : i ∈ V := by
    have hiR : i ∉ [x, j] := by
      intro him
      simp only [List.mem_cons, List.not_mem_nil, or_false] at him
      rcases him with rfl | rfl
      · exact (not_lt_of_ge (show Q k ≤ |s k t x| from hxLarge)) his
      · exact (not_lt_of_ge (show Q k ≤ |s k t i| from hjLarge)) his
    apply List.mem_toFinset.mp
    rw [inv.used]
    exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr
      ⟨List.mem_toFinset.mpr hi, by simpa using hiR⟩)
  have hqstatus : q ∈ V ↔ q ∈ W ∨ q = p := by
    have hqx : q ≠ x := by intro hh; have hv := congrArg f hh; omega
    have hqj : q ≠ j := by intro hh; have hv := congrArg f hh; omega
    have hqn : q ≠ n := by intro hh; have hv := congrArg f hh; omega
    have hh : q ∈ V ++ [x, j] ↔ q ∈ W ++ [p, n] := hperm.mem_iff
    simpa [hqx, hqj, hqn] using hh
  refine ⟨j, L, hj, hjmax, hLj, hSretained, legal_of_strip inv.nodup hsV,
    inv.nodup, hsV, ?_, inv, hperm, hretain, hG, hU, hSmall, hH, hHstrict, hJ,
    hqstatus, hEnd, he0.1, he0.2, ?_⟩
  · intro d
    simpa only [mass, f, zero_add] using inStrip_prefix hsV d
  · rw [inv.complementSum, hEnd]

#print axioms actualSource_threeNegative_crossingAnchor_exchange_full
end D5.S3.Combinatorics.Circle.CrossingAnchorLargeExchange
