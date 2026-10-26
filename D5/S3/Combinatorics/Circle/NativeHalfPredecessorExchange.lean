/- GID: D5/S3/Combinatorics/Circle/NativeHalfPredecessorExchange
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/NativeHalfPredecessorExchange
   mirror-E: none(waiver:audit-open-22063)
   anchors: [mathlib/module/Mathlib.Logic.Equiv.Fin.Rotate]
   utility: none
   digest: Returning the actual SMALL source half yields a full strict-G exchange. -/
module
public import D5.S3.Combinatorics.Circle.TwoOppositeLargeExchange
public import Mathlib.Logic.Equiv.Fin.Rotate

/-! The actual source half can be returned by reordering its entire SMALL batch. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
namespace D5.S3.Combinatorics.Circle.NativeHalfPredecessorExchange
open SourceWidth ExpandingSourcePath MixedSuffixEnergy SmallStepOrdering
open TwoOppositeLargeExchange
open scoped BigOperators

def oldWord {k : ℕ} (zpen z : Fin k) (A S T E : List (Fin k)) : List (Fin k) :=
  A ++ S ++ [zpen] ++ T ++ [z] ++ E

def correction (k t : ℕ) (p zpen : Fin k) : ℤ :=
  -s k t zpen - |s k t (hit k 1 p)|

local macro "source_arith" : tactic =>
  `(tactic| ((try simp only [s, N, C, Q, Large, mass, List.cons_append,
    List.nil_append, List.map_append, List.map_cons, List.map_nil,
    List.sum_append, List.sum_cons, List.sum_nil, add_zero, zero_add] at *) <;> omega))

set_option maxHeartbeats 800000 in
/-- The actual SMALL predecessor of a is derived to be its positive half.
Returning it from the last pre-boundary SMALL batch gives a literal full
exchange, with every new gate and the complete physical inventory proved. -/
theorem actualSource_half_predecessor_exchange_full
    (k t : ℕ) (hk : 3 ≤ k) (p a z : Fin k)
    (A S T E0 E1 : List (Fin k))
    (hpositive : 0 < s k t p)
    (hnlarge : Q k ≤ |s k t (hit k 1 p)|)
    (hexpand : N k < 3 * |s k t p|)
    (hW : Legal k t (oldWord (finRotate k (finRotate k a)) z
      A S T (E0 ++ E1)))
    (hnunused : hit k 1 p ∉ oldWord (finRotate k (finRotate k a)) z
      A S T (E0 ++ E1))
    (hqunused : finRotate k a ∉ oldWord (finRotate k (finRotate k a)) z
      A S T (E0 ++ E1))
    (hsmall : ∀ i ∈ S ++ T ++ E0 ++ E1, |s k t i| < Q k)
    (ha : a ∈ T)
    (hb : (finRotate k).symm a ∈ S)
    (hcrossSize : C k + 1 < 3 * s k t a)
    (hqsmaller : s k t (finRotate k a) < s k t p)
    (hzlarge : Q k ≤ -s k t z)
    (hzupper : -s k t z ≤ |s k t (hit k 1 p)|)
    (hpenlow : C k - s k t p <
      mass (s k t) (A ++ S ++ [finRotate k (finRotate k a)]))
    (hendlo : C k - s k t p < mass (s k t)
      (oldWord (finRotate k (finRotate k a)) z A S T E0))
    (hendhi : mass (s k t)
      (oldWord (finRotate k (finRotate k a)) z A S T E0) <
      s k t a - correction k t p (finRotate k (finRotate k a))) :
    let n := hit k 1 p
    let q := finRotate k a
    let zpen := finRotate k q
    let b := (finRotate k).symm a
    let W := oldWord zpen z A S T (E0 ++ E1)
    let W0 := oldWord zpen z A S T E0
    ∃ S' L : List (Fin k),
      2 * s k t b = s k t a ∧ 0 < s k t b ∧
      S'.Perm (S.erase b) ∧ L.Perm (T ++ E0) ∧
      (let V := A ++ S' ++ [n] ++ L ++ [z, q]
       let R := [zpen, b] ++ E1
       Legal k t V ∧ InStrip (s k t) (C k) 0 V ∧
       (∀ j : ℕ, 0 ≤ mass (s k t) (V.take j) ∧
         mass (s k t) (V.take j) ≤ C k) ∧
       Inventory k t W V [n, q] R ∧
       G k t V + 1 = G k t W ∧
       U V = U W + E1.length ∧
       H k t V + 3 ^ (s k t zpen).natAbs =
         H k t W + 3 ^ (s k t n).natAbs + 3 ^ (s k t q).natAbs ∧
       J k t V < J k t W ∧
       mass (s k t) V = mass (s k t) W0 + correction k t p zpen +
         s k t q - s k t b) := by
  classical
  dsimp only
  let f := s k t
  let n := hit k 1 p
  let q := finRotate k a
  let zpen := finRotate k q
  let b := (finRotate k).symm a
  let W := oldWord zpen z A S T (E0 ++ E1)
  let W0 := oldWord zpen z A S T E0
  let P := f p
  let D := |f n|
  let aa := f a
  let qq := f q
  let ZZ := -f zpen
  let Z := -f z
  let δ := ZZ - D
  let β := f b
  let B0 := C k - P
  let wpen := mass f (A ++ S ++ [zpen])
  let v := mass f W0
  let fprime := mass f (A ++ S) - β
  let b0 := fprime - D
  let η := v + δ - β
  let c := η + Z
  let e := η + qq
  have geo := native_geometry hk t p hnlarge hexpand
  obtain ⟨hQ, hN, hC, hNpos, hNodd⟩ := source_geometry hk
  change 2 ≤ Q k at hQ
  change N k = 4 * Q k - 1 at hN
  change C k = 2 * Q k - 1 at hC
  change 0 < N k at hNpos
  change N k % 2 = 1 at hNodd
  have hpabs : |s k t p| = P := abs_of_pos hpositive
  have hnval : f n = -D := by
    have hh := geo.nValue
    simpa [n, D, f, orient, show ¬ s k t p < 0 by omega] using hh
  have hD : D = N k - 2 * P := by
    simpa [D, P, f, n, hpabs] using geo.firstEquation
  have hDbound : Q k ≤ D := hnlarge
  have hbudget : 2 * P ≤ C k + Q k := by
    simpa [P, f, hpabs] using geo.budget
  have hDpos : 0 < D := by ((try dsimp only [f, n, q, zpen, b, W, W0, P, D, aa, qq, ZZ, Z, δ, β, B0, wpen, v, fprime, b0, η, c, e] at *); source_arith)
  have hasmall : |aa| < Q k := hsmall a (by simp [ha])
  have hapos : 0 < aa := by ((try dsimp only [f, n, q, zpen, b, W, W0, P, D, aa, qq, ZZ, Z, δ, β, B0, wpen, v, fprime, b0, η, c, e] at *); source_arith)
  have haa : aa < Q k := by simpa only [abs_of_pos hapos] using hasmall
  have hcycle := (ZeroSumSubsets.source_cycle (by omega : 0 < k) t).2.2
  have hqeq : qq = 2 * aa := by
    have he := hcycle a
    change 2 * aa - qq = N k *
      (if N k < 4 * aa then 1 else if 4 * aa < -N k then -1 else 0) at he
    rw [ite_eq_right (by ((try dsimp only [f, n, q, zpen, b, W, W0, P, D, aa, qq, ZZ, Z, δ, β, B0, wpen, v, fprime, b0, η, c, e] at *); source_arith)), ite_eq_right (by ((try dsimp only [f, n, q, zpen, b, W, W0, P, D, aa, qq, ZZ, Z, δ, β, B0, wpen, v, fprime, b0, η, c, e] at *); source_arith))] at he
    ((try dsimp only [f, n, q, zpen, b, W, W0, P, D, aa, qq, ZZ, Z, δ, β, B0, wpen, v, fprime, b0, η, c, e] at *); source_arith)
  have hqpos : 0 < qq := by ((try dsimp only [f, n, q, zpen, b, W, W0, P, D, aa, qq, ZZ, Z, δ, β, B0, wpen, v, fprime, b0, η, c, e] at *); source_arith)
  have hqLarge : Q k ≤ qq := by ((try dsimp only [f, n, q, zpen, b, W, W0, P, D, aa, qq, ZZ, Z, δ, β, B0, wpen, v, fprime, b0, η, c, e] at *); source_arith)
  have hzpeq : ZZ = N k - 2 * qq := by
    have he := hcycle q
    change 2 * qq - f zpen = N k *
      (if N k < 4 * qq then 1 else if 4 * qq < -N k then -1 else 0) at he
    rw [ite_eq_left (by ((try dsimp only [f, n, q, zpen, b, W, W0, P, D, aa, qq, ZZ, Z, δ, β, B0, wpen, v, fprime, b0, η, c, e] at *); source_arith))] at he
    ((try dsimp only [f, n, q, zpen, b, W, W0, P, D, aa, qq, ZZ, Z, δ, β, B0, wpen, v, fprime, b0, η, c, e] at *); source_arith)
  have hqP : qq < P := hqsmaller
  have hqD : D < qq := by ((try dsimp only [f, n, q, zpen, b, W, W0, P, D, aa, qq, ZZ, Z, δ, β, B0, wpen, v, fprime, b0, η, c, e] at *); source_arith)
  have hZZD : D < ZZ := by ((try dsimp only [f, n, q, zpen, b, W, W0, P, D, aa, qq, ZZ, Z, δ, β, B0, wpen, v, fprime, b0, η, c, e] at *); source_arith)
  have hδpos : 0 < δ := by ((try dsimp only [f, n, q, zpen, b, W, W0, P, D, aa, qq, ZZ, Z, δ, β, B0, wpen, v, fprime, b0, η, c, e] at *); source_arith)
  have hbS : b ∈ S := hb
  have hbsmall : |β| < Q k :=
    hsmall b (List.mem_append_left E1 (List.mem_append_left E0 (List.mem_append_left T hbS)))
  have hbr : finRotate k b = a := (finRotate k).apply_symm_apply a
  have hhalf : 2 * β = aa := by
    have he := hcycle b
    rw [hbr] at he
    change 2 * β - aa = N k *
      (if N k < 4 * β then 1 else if 4 * β < -N k then -1 else 0) at he
    have hbabs := abs_lt.mp hbsmall
    rw [ite_eq_right (by ((try dsimp only [f, n, q, zpen, b, W, W0, P, D, aa, qq, ZZ, Z, δ, β, B0, wpen, v, fprime, b0, η, c, e] at *); source_arith)), ite_eq_right (by ((try dsimp only [f, n, q, zpen, b, W, W0, P, D, aa, qq, ZZ, Z, δ, β, B0, wpen, v, fprime, b0, η, c, e] at *); source_arith))] at he
    ((try dsimp only [f, n, q, zpen, b, W, W0, P, D, aa, qq, ZZ, Z, δ, β, B0, wpen, v, fprime, b0, η, c, e] at *); source_arith)
  have hβpos : 0 < β := by ((try dsimp only [f, n, q, zpen, b, W, W0, P, D, aa, qq, ZZ, Z, δ, β, B0, wpen, v, fprime, b0, η, c, e] at *); source_arith)
  have hβB0 : β ≤ B0 := by ((try dsimp only [f, n, q, zpen, b, W, W0, P, D, aa, qq, ZZ, Z, δ, β, B0, wpen, v, fprime, b0, η, c, e] at *); source_arith)
  have h5aa : 5 * aa ≤ 2 * C k - 1 := by ((try dsimp only [f, n, q, zpen, b, W, W0, P, D, aa, qq, ZZ, Z, δ, β, B0, wpen, v, fprime, b0, η, c, e] at *); source_arith)
  have hZpos : 0 < Z := by ((try dsimp only [f, n, q, zpen, b, W, W0, P, D, aa, qq, ZZ, Z, δ, β, B0, wpen, v, fprime, b0, η, c, e] at *); source_arith)
  have hZbound : Z ≤ D := hzupper
  have hnL : Large k t n := geo.nLarge
  have hqL : Large k t q := by
    change Q k ≤ |qq|
    rw [abs_of_pos hqpos]
    exact hqLarge
  have hzpL : Large k t zpen := by
    have hneg : f zpen < 0 := by ((try dsimp only [f, n, q, zpen, b, W, W0, P, D, aa, qq, ZZ, Z, δ, β, B0, wpen, v, fprime, b0, η, c, e] at *); source_arith)
    change Q k ≤ |f zpen|
    rw [abs_of_neg hneg]
    ((try dsimp only [f, n, q, zpen, b, W, W0, P, D, aa, qq, ZZ, Z, δ, β, B0, wpen, v, fprime, b0, η, c, e] at *); source_arith)
  have hbNotL : ¬ Large k t b := by
    change ¬ Q k ≤ |β|
    omega
  have hsmallS (i : Fin k) (hi : i ∈ S) : |f i| < Q k :=
    hsmall i (by simp [hi])
  have hsmallSE (i : Fin k) (hi : i ∈ S.erase b) : |f i| < Q k :=
    hsmallS i (List.mem_of_mem_erase hi)
  have hsmallT (i : Fin k) (hi : i ∈ T ++ E0) : |f i| < Q k := by
    apply hsmall i
    simp only [List.mem_append] at hi ⊢
    tauto
  have hsmallE1 (i : Fin k) (hi : i ∈ E1) : |f i| < Q k :=
    hsmall i (by simp [hi])
  have hsW : InStrip f (C k) 0 W := strip_of_legal hW
  have hsA : InStrip f (C k) 0 A :=
    (strip_split A (S ++ [zpen] ++ T ++ [z] ++ E0 ++ E1)
      (by simpa only [W, oldWord, List.append_assoc] using hsW)).1
  have hsF : InStrip f (C k) 0 (A ++ S) :=
    (strip_split (A ++ S) ([zpen] ++ T ++ [z] ++ E0 ++ E1)
      (by simpa only [W, oldWord, List.append_assoc] using hsW)).1
  have hA : 0 ≤ mass f A ∧ mass f A ≤ C k := by
    simpa [mass] using inStrip_prefix hsA A.length
  have hF : 0 ≤ mass f (A ++ S) ∧ mass f (A ++ S) ≤ C k := by
    simpa only [List.take_length, zero_add, mass] using inStrip_prefix hsF (A ++ S).length
  have hwpen : mass f (A ++ S) = wpen + ZZ := by
    dsimp only [wpen, ZZ, mass]
    simp only [List.map_append, List.map_cons, List.map_nil,
      List.sum_append, List.sum_cons, List.sum_nil, add_zero]
    ring
  have hpenlow' : B0 < wpen := hpenlow
  have hvlo : B0 < v := hendlo
  have hvhi : v < aa - δ := hendhi
  have hfprime : 0 ≤ fprime ∧ fprime ≤ C k := by ((try dsimp only [f, n, q, zpen, b, W, W0, P, D, aa, qq, ZZ, Z, δ, β, B0, wpen, v, fprime, b0, η, c, e] at *); source_arith)
  have hb0 : 0 ≤ b0 ∧ b0 ≤ C k := by ((try dsimp only [f, n, q, zpen, b, W, W0, P, D, aa, qq, ZZ, Z, δ, β, B0, wpen, v, fprime, b0, η, c, e] at *); source_arith)
  have hη : 0 ≤ η := by ((try dsimp only [f, n, q, zpen, b, W, W0, P, D, aa, qq, ZZ, Z, δ, β, B0, wpen, v, fprime, b0, η, c, e] at *); source_arith)
  have he : 0 ≤ e ∧ e ≤ C k := by ((try dsimp only [f, n, q, zpen, b, W, W0, P, D, aa, qq, ZZ, Z, δ, β, B0, wpen, v, fprime, b0, η, c, e] at *); source_arith)
  have hc : 0 ≤ c ∧ c ≤ C k := by ((try dsimp only [f, n, q, zpen, b, W, W0, P, D, aa, qq, ZZ, Z, δ, β, B0, wpen, v, fprime, b0, η, c, e] at *); source_arith)
  have hSper : (S.erase b ++ [b]).Perm S :=
    List.perm_append_comm.trans (List.perm_cons_erase hb).symm
  have hmassS : mass f (S.erase b) + β = mass f S := by
    simpa [mass, β] using (hSper.map f).sum_eq
  have hsumS : mass f A + mass f (S.erase b) = fprime := by
    dsimp only [fprime]
    simp only [mass, List.map_append, List.sum_append] at hmassS ⊢
    omega
  have hsumT : b0 + mass f (T ++ E0) = c := by
    dsimp only [b0, fprime, c, η, v, W0, oldWord, δ, ZZ, Z]
    simp only [mass, List.map_append, List.map_cons, List.map_nil,
      List.sum_append, List.sum_cons, List.sum_nil, add_zero]
    ring
  have orderBatch (X : List (Fin k)) (u v : ℤ)
      (hx : ∀ i ∈ X, |f i| < Q k)
      (hu : 0 ≤ u ∧ u ≤ C k) (hv : 0 ≤ v ∧ v ≤ C k)
      (hm : u + mass f X = v) :
      ∃ Y : List (Fin k), Y.Perm X ∧ InStrip f (C k) u Y := by
    apply exists_order_between f X (C k) u hu
    · have hh : 0 ≤ u + mass f X ∧ u + mass f X ≤ C k := by
        rw [hm]
        exact hv
      simpa only [mass] using hh
    · intro i hi j hj hip hjn
      have hi' := hx i hi
      have hj' := hx j hj
      rw [abs_of_pos hip] at hi'
      rw [abs_of_neg hjn] at hj'
      omega
  obtain ⟨S', hS', hsS'⟩ := orderBatch (S.erase b) (mass f A) fprime
    hsmallSE hA hfprime hsumS
  obtain ⟨L, hL, hsL⟩ := orderBatch (T ++ E0) b0 c hsmallT hb0 hc hsumT
  have hmassS' : mass f S' = mass f (S.erase b) := by
    simpa only [mass] using (hS'.map f).sum_eq
  have hmassL : mass f L = mass f (T ++ E0) := by
    simpa only [mass] using (hL.map f).sum_eq
  have hsAS : InStrip f (C k) 0 (A ++ S') :=
    inStrip_append hsA (by simpa only [zero_add, mass] using hsS')
  have hAS : mass f (A ++ S') = fprime := by
    calc
      mass f (A ++ S') = mass f A + mass f S' := by
        simp only [mass, List.map_append, List.sum_append]
      _ = fprime := by rw [hmassS']; exact hsumS
  have hsN : InStrip f (C k) fprime [n] := by
    change 0 ≤ fprime ∧ fprime ≤ C k ∧
      0 ≤ fprime + f n ∧ fprime + f n ≤ C k
    rw [hnval]
    exact ⟨hfprime.1, hfprime.2, by ((try dsimp only [f, n, q, zpen, b, W, W0, P, D, aa, qq, ZZ, Z, δ, β, B0, wpen, v, fprime, b0, η, c, e] at *); source_arith), by ((try dsimp only [f, n, q, zpen, b, W, W0, P, D, aa, qq, ZZ, Z, δ, β, B0, wpen, v, fprime, b0, η, c, e] at *); source_arith)⟩
  have hsASn : InStrip f (C k) 0 (A ++ S' ++ [n]) := by
    apply inStrip_append hsAS
    change InStrip f (C k) (0 + mass f (A ++ S')) [n]
    rw [zero_add, hAS]
    exact hsN
  have hASn : mass f (A ++ S' ++ [n]) = b0 := by
    calc
      mass f (A ++ S' ++ [n]) = mass f (A ++ S') + f n := by
        simp only [mass, List.map_append, List.map_cons, List.map_nil,
          List.sum_append, List.sum_cons, List.sum_nil, add_zero]
      _ = b0 := by rw [hAS, hnval]; rfl
  have hsASnL : InStrip f (C k) 0 (A ++ S' ++ [n] ++ L) := by
    apply inStrip_append hsASn
    change InStrip f (C k) (0 + mass f (A ++ S' ++ [n])) L
    rw [zero_add, hASn]
    exact hsL
  have hASnL : mass f (A ++ S' ++ [n] ++ L) = c := by
    calc
      mass f (A ++ S' ++ [n] ++ L) = mass f (A ++ S' ++ [n]) + mass f L := by
        simp only [mass, List.map_append, List.sum_append]
      _ = c := by rw [hASn, hmassL]; exact hsumT
  have hpair : InStrip f (C k) c [z, q] := by
    change 0 ≤ c ∧ c ≤ C k ∧ 0 ≤ c + f z ∧ c + f z ≤ C k ∧
      0 ≤ c + f z + f q ∧ c + f z + f q ≤ C k
    have hcz : c + f z = η := by dsimp [c, Z]; ring
    have hczq : c + f z + f q = e := by dsimp only [e, qq]; rw [hcz]
    rw [hczq, hcz]
    exact ⟨hc.1, hc.2, hη, by ((try dsimp only [f, n, q, zpen, b, W, W0, P, D, aa, qq, ZZ, Z, δ, β, B0, wpen, v, fprime, b0, η, c, e] at *); source_arith), he.1, he.2⟩
  let V := A ++ S' ++ [n] ++ L ++ [z, q]
  let R := [zpen, b] ++ E1
  have hsV : InStrip f (C k) 0 V := by
    apply inStrip_append hsASnL
    change InStrip f (C k) (0 + mass f (A ++ S' ++ [n] ++ L)) [z, q]
    rw [zero_add, hASnL]
    exact hpair
  have hSret : (S' ++ [b]).Perm S := (hS'.append_right [b]).trans hSper
  have hI : [n, q].Nodup := by
    have hnq : n ≠ q := by
      intro h
      have heq := congrArg f h
      ((try dsimp only [f, n, q, zpen, b, W, W0, P, D, aa, qq, ZZ, Z, δ, β, B0, wpen, v, fprime, b0, η, c, e] at *); source_arith)
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
    have hh := hSret.count_eq i
    have hl := hL.count_eq i
    simp only [List.count_append, List.count_cons, List.count_nil] at hh hl
    simp only [V, R, W, oldWord, List.count_append, List.count_cons, List.count_nil]
    omega
  have hRold (i : Fin k) (hi : i ∈ R) : i ∈ W := by
    simp only [R, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with (rfl | rfl) | hi
    · simp [W, oldWord]
    · simp only [W, oldWord, List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
      tauto
    · simp [W, oldWord, hi]
  have inv : Inventory k t W V [n, q] R :=
    inventory_of_perm hk t W V [n, q] R hW.1 hI hIW hRold hIL hperm
  have heweights := small_weights t E1 hsmallE1
  have hRlarge : largeUsed k t R = 1 := by
    simp [R, largeWeight, hzpL, hbNotL, heweights.1]
  have hRenergy : H k t R = 3 ^ (f zpen).natAbs := by
    simp [R, energyWeight, hzpL, hbNotL, heweights.2, f, s]
  have hIlarge : largeUsed k t [n, q] = 2 := by
    simp [largeWeight, hnL, hqL]
  have hIenergy : H k t [n, q] = 3 ^ (f n).natAbs + 3 ^ (f q).natAbs := by
    simp [energyWeight, hnL, hqL, f, s]
  have hG : G k t V + 1 = G k t W := by
    have hh := inv.largeBalance
    rw [hRlarge, hIlarge] at hh
    omega
  have hU : U V = U W + E1.length := by
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
  have hEnd : mass f V = v + δ + qq - β := by
    calc
      mass f V = mass f (A ++ S' ++ [n] ++ L) + mass f [z, q] := by
        simp only [V, mass, List.map_append, List.sum_append]
      _ = v + δ + qq - β := by
        rw [hASnL]
        simp only [mass, List.map_cons, List.map_nil, List.sum_cons,
          List.sum_nil, add_zero]
        dsimp only [c, η, Z, qq]
        ring
  refine ⟨S', L, hhalf, hβpos, hS', hL,
    legal_of_strip inv.nodup hsV, hsV, ?_, inv, hG, hU, hH, hJ, hEnd⟩
  intro j
  simpa [mass, f, V, n, q] using inStrip_prefix hsV j

#print axioms actualSource_half_predecessor_exchange_full

end D5.S3.Combinatorics.Circle.NativeHalfPredecessorExchange
