/- GID: D5/S3/Combinatorics/Circle/OddFirstNegativePlacement
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/OddFirstNegativePlacement
   mirror-E: none(waiver:audit-open-22063)
   anchors: [mathlib/module/Mathlib.Logic.Equiv.Fin.Rotate]
   utility: none
   digest: Complete SMALL-prefix normalization forces a LARGE prefix occurrence or a strict physical competitor in the odd first-negative branch. -/
module
public import D5.S3.Combinatorics.Circle.SingleAnchorLargeExchange
public import D5.S3.Combinatorics.Circle.FirstNegativeShiftExchange

/-! # Odd first-negative placement

Complete SMALL-prefix reordering and physical parent exchanges yield strict
lexicographic descent or necessary placement and energy bounds. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
namespace D5.S3.Combinatorics.Circle.OddFirstNegativePlacement
open SourceWidth ExpandingSourcePath MixedSuffixEnergy SmallStepOrdering
open TwoOppositeLargeExchange ThreeLargePacketExchange SingleAnchorLargeExchange
open scoped BigOperators

/-- Invert the actual physical source edge, using centered representative
uniqueness. Equal values at different physical labels are never identified. -/
private theorem positive_parent {k : ℕ} (hk : 3 ≤ k) (t : ℕ) (i : Fin k)
    (hpos : 0 < s k t i) :
    let z := s k t i
    s k t ((finRotate k).symm i) =
      if z % 2 = 0 then z / 2
      else (z - N k) / 2 := by
  dsimp only
  let b := (finRotate k).symm i
  obtain ⟨_, _, _, hN, ho⟩ := source_geometry hk
  change 0 < N k at hN
  change N k % 2 = 1 at ho
  have hb : -(N k / 2) ≤ s k t b ∧ s k t b ≤ N k / 2 :=
    centered_bounds hN ho _
  have hi : -(N k / 2) ≤ s k t i ∧ s k t i ≤ N k / 2 :=
    centered_bounds hN ho _
  have hedge := (ZeroSumSubsets.source_cycle (by omega : 0 < k) t).2.2 b
  have hrot : finRotate k b = i := Equiv.apply_symm_apply _ _
  change 2 * s k t b - s k t (finRotate k b) = N k *
    (if N k < 4 * s k t b then 1 else if 4 * s k t b < -N k then -1 else 0) at hedge
  rw [hrot] at hedge
  have hmod : (2 * s k t b) % N k = s k t i % N k := by
    have he : 2 * s k t b = s k t i + N k *
        (if N k < 4 * s k t b then 1 else if 4 * s k t b < -N k then -1 else 0) := by
      omega
    rw [he, Int.add_mul_emod_self_left]
  have hc : centered (N k) (2 * s k t b) = s k t i :=
    centered_unique hN ho (centered_bounds hN ho _) hi
      ((centered_mod _ _).trans hmod)
  have hself : centered (N k) (s k t b) = s k t b :=
    centered_unique hN ho (centered_bounds hN ho _) hb (centered_mod _ _)
  rw [centered_double hN ho, hself] at hc
  change s k t b = _
  split_ifs <;> unfold doubleStep at hc <;> split_ifs at hc <;> omega

/-- A short LARGE insertion into a literal old prefix. Its entire discarded
suffix, including every discarded SMALL occurrence, enters Inventory. -/
private theorem prefix_insert {k : ℕ} (hk : 3 ≤ k) (t : ℕ)
    (F R I : List (Fin k)) (hW : Legal k t (F ++ R))
    (hI : I.Nodup) (hfresh : ∀ i ∈ I, i ∉ F ++ R)
    (hlarge : ∀ i ∈ I, Large k t i)
    (hstrip : InStrip (s k t) (C k) (mass (s k t) F) I) :
    Legal k t (F ++ I) ∧ InStrip (s k t) (C k) 0 (F ++ I) ∧
    (∀ j : ℕ, 0 ≤ mass (s k t) ((F ++ I).take j) ∧
      mass (s k t) ((F ++ I).take j) ≤ C k) ∧
    Inventory k t (F ++ R) (F ++ I) I R ∧
    ((F ++ I) ++ R).Perm ((F ++ R) ++ I) := by
  have hp : ((F ++ I) ++ R).Perm ((F ++ R) ++ I) := by
    simpa only [List.append_assoc] using
      (List.perm_append_comm : (I ++ R).Perm (R ++ I)).append_left F
  have inv := inventory_of_perm hk t (F ++ R) (F ++ I) I R hW.1 hI hfresh
    (fun i hi => List.mem_append_right F hi) hlarge hp
  have hsF := (strip_split F R (strip_of_legal hW)).1
  have hsV : InStrip (s k t) (C k) 0 (F ++ I) :=
    inStrip_append hsF (by simpa only [mass, zero_add] using hstrip)
  exact ⟨legal_of_strip inv.nodup hsV, hsV,
    fun j => by simpa only [mass, zero_add] using inStrip_prefix hsV j, inv, hp⟩

theorem two_energy_threshold (D L Z1 Z2 : ℕ) (hDL : D < L)
    (h : L < max Z1 Z2 ∨ max Z1 Z2 = L ∧ D < min Z1 Z2) :
    (3 : ℕ) ^ L + 3 ^ D < 3 ^ Z1 + 3 ^ Z2 := by
  have hD := pow_lt_pow_right₀ (by decide : 1 < (3 : ℕ)) hDL
  have hnext : (3 : ℕ) ^ L + 3 ^ D < 3 ^ (L + 1) := by
    rw [pow_succ]
    omega
  by_cases h12 : Z1 ≤ Z2
  · simp only [max_eq_right h12, min_eq_left h12] at h
    rcases h with h | ⟨rfl, h⟩
    · have hh := pow_le_pow_right₀ (by decide : 1 ≤ (3 : ℕ))
        (show L + 1 ≤ Z2 by omega)
      exact lt_of_lt_of_le hnext (le_trans hh (Nat.le_add_left _ _))
    · have hh := pow_lt_pow_right₀ (by decide : 1 < (3 : ℕ)) h
      omega
  · have h21 : Z2 ≤ Z1 := by omega
    simp only [max_eq_left h21, min_eq_right h21] at h
    rcases h with h | ⟨rfl, h⟩
    · have hh := pow_le_pow_right₀ (by decide : 1 ≤ (3 : ℕ))
        (show L + 1 ≤ Z1 by omega)
      exact lt_of_lt_of_le hnext (le_trans hh (Nat.le_add_right _ _))
    · have hh := pow_lt_pow_right₀ (by decide : 1 < (3 : ℕ)) h
      omega

/-- A fresh SMALL append removes that label from the unused SMALL set.
The all-LARGE insertion formula in Inventory is deliberately inapplicable. -/
private theorem small_append {k : ℕ} (hk : 3 ≤ k) (t : ℕ)
    (W : List (Fin k)) (a : Fin k) (hW : Legal k t W) (ha : a ∉ W)
    (hsmall : |s k t a| < Q k) (hpos : 0 < s k t a)
    (hcap : mass (s k t) W + s k t a ≤ C k) :
    let V := W ++ [a]
    Legal k t V ∧ InStrip (s k t) (C k) 0 V ∧
    (∀ j : ℕ, 0 ≤ mass (s k t) (V.take j) ∧ mass (s k t) (V.take j) ≤ C k) ∧
    V.toFinset = W.toFinset ∪ {a} ∧ Disjoint W.toFinset {a} ∧
    V.toFinsetᶜ = W.toFinsetᶜ \ {a} ∧
    remainingSmall t V = remainingSmall t W \ {a} ∧
    G k t V = G k t W ∧ H k t V = H k t W ∧ U V + 1 = U W ∧
    mass (s k t) V = mass (s k t) W + s k t a ∧
    remainingMass (s k t) V = -mass (s k t) V ∧ J k t V < J k t W := by
  classical
  dsimp only
  let V := W ++ [a]
  have haL : ¬ Large k t a := by change ¬ Q k ≤ |s k t a|; omega
  have hn : V.Nodup := hW.1.append (by simp) (List.disjoint_left.mpr (by
    intro i hiW hiA
    have hi : i = a := by simpa using hiA
    subst i
    exact ha hiW))
  have hw := (hW.2 W.length).1
  rw [List.take_length] at hw
  have hsA : InStrip (s k t) (C k) (mass (s k t) W) [a] := by
    change 0 ≤ mass (s k t) W ∧ mass (s k t) W ≤ C k ∧
      0 ≤ mass (s k t) W + s k t a ∧ mass (s k t) W + s k t a ≤ C k
    exact ⟨hw, (by simpa using (hW.2 W.length).2), by omega, hcap⟩
  have hs : InStrip (s k t) (C k) 0 V :=
    inStrip_append (strip_of_legal hW) (by simpa only [mass, zero_add] using hsA)
  have hu : V.toFinset = W.toFinset ∪ {a} := by simp [V]
  have hd : Disjoint W.toFinset {a} := by simpa using ha
  have hc : V.toFinsetᶜ = W.toFinsetᶜ \ {a} := by
    ext i
    simp only [hu, Finset.mem_compl, Finset.mem_union, Finset.mem_sdiff,
      Finset.mem_singleton]
    tauto
  have hsm : remainingSmall t V = remainingSmall t W \ {a} := by
    ext i
    simp only [remainingSmall, hc, Finset.mem_filter, Finset.mem_sdiff]
    tauto
  have hused : largeUsed k t V = largeUsed k t W := by
    simp [V, largeUsed, mass, largeWeight, haL]
  have hg : G k t V = G k t W := by
    have h1 := physical_balance (largeWeight k t) V hn
    have h2 := physical_balance (largeWeight k t) W hW.1
    change G k t V + largeUsed k t V = _ at h1
    change G k t W + largeUsed k t W = _ at h2
    omega
  have hh : H k t V = H k t W := by simp [V, H, mass, energyWeight, haL]
  have hcount : U V + 1 = U W := by
    have h1 : U V + V.length = k := by
      simpa [U, mass, List.map_const'] using physical_balance (fun _ : Fin k => (1 : ℕ)) V hn
    have h2 : U W + W.length = k := by
      simpa [U, mass, List.map_const'] using physical_balance (fun _ : Fin k => (1 : ℕ)) W hW.1
    have hlen : V.length = W.length + 1 := by simp [V]
    omega
  have hm : mass (s k t) V = mass (s k t) W + s k t a := by simp [V, mass]
  have hzero := physical_balance (s k t) V hn
  rw [(ZeroSumSubsets.source_cycle (by omega : 0 < k) t).2.1] at hzero
  have hj : J k t V < J k t W := by
    apply Prod.Lex.toLex_lt_toLex.mpr
    exact Or.inr ⟨hg, Prod.Lex.toLex_lt_toLex.mpr (Or.inr ⟨hh, by omega⟩)⟩
  exact ⟨legal_of_strip hn hs, hs,
    fun j => by simpa only [mass, zero_add] using inStrip_prefix hs j,
    hu, hd, hc, hsm, hg, hh, hcount, hm,
    by change remainingMass (s k t) V = -mass (s k t) V; omega, hj⟩

set_option maxHeartbeats 8000000 in
/-- For the original three-negative word with odd first magnitude Y>P,
either the actual parent is already in A, a concrete strict-J competitor
exists, or the unused parent and used grandparent occupy the stated narrow
strip. Neither inverse-label availability is a hypothesis. -/
private theorem two_generation_placement
    (k t : ℕ) (hk : 3 ≤ k) (p y zpen z : Fin k)
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
    (hblocklo : C k - s k t p < mass (s k t) (oldWord p y zpen z A T0 T1 T2 E))
    (hblockhi : mass (s k t) (oldWord p y zpen z A T0 T1 T2 E) < |s k t (hit k 1 p)|)
    (hyP : s k t p < -s k t y) (hyodd : (-s k t y) % 2 = 1) :
    let f := s k t
    let n := hit k 1 p
    let x := hit k 2 p
    let W := oldWord p y zpen z A T0 T1 T2 E
    let S := smallWord T0 T1 T2 E
    let F := A ++ [x] ++ T0 ++ [y]
    let R := T1 ++ [zpen] ++ T2 ++ [z] ++ E
    let beta := (finRotate k).symm y
    let gamma := (finRotate k).symm beta
    let P := f p
    let D := |f n|
    let Y := -f y
    let Z1 := -f zpen
    let Z2 := -f z
    let L := (N k - Y) / 2
    let d := P - D
    let delta := Y - P
    let v := mass f F
    (beta ∈ A ∧ max Z1 Z2 ≤ P ∧ (max Z1 Z2 = P → min Z1 Z2 ≤ D)) ∨
    (∃ V I Ret : List (Fin k),
      Legal k t V ∧ V.Nodup ∧ InStrip f (C k) 0 V ∧
      (∀ j : ℕ, 0 ≤ mass f (V.take j) ∧ mass f (V.take j) ≤ C k) ∧
      (V ++ Ret).Perm (W ++ I) ∧ J k t V < J k t W ∧
      ((Inventory k t W V I Ret ∧
        ((V = F ++ [p,n] ∧ I = [p,n] ∧ Ret = R ∧
          G k t V = G k t W ∧ H k t V < H k t W) ∨
         (V = F ++ [p,n,beta] ∧ I = [p,n,beta] ∧ Ret = R ∧
          2 * (v + d) ≤ Y - 1 ∧ G k t V + 1 = G k t W) ∨
         (V = F ++ [beta,n] ∧ I = [beta,n] ∧ Ret = R ∧
          G k t V = G k t W ∧ H k t V < H k t W) ∨
         (V = F ++ [beta,gamma,p,n] ∧ I = [beta,gamma,p,n] ∧ Ret = R ∧
          L % 2 = 1 ∧ G k t V + 2 = G k t W) ∨
         (∃ K B : List (Fin k),
          L % 2 = 0 ∧ gamma ∈ S ∧ B.Subperm (positive t S) ∧ (K ++ B).Perm S ∧
          (∀ i ∈ B, 0 < f i ∧ |f i| < Q k) ∧
          V = A ++ [p,n] ++ K ++ [z,beta] ∧ I = [p,n,beta] ∧
          Ret = [x,y,zpen] ++ B ∧ G k t V = G k t W ∧
          U V = U W + B.length ∧ H k t V < H k t W))) ∨
       (V = W ++ [gamma] ∧ I = [gamma] ∧ Ret = [] ∧
        L % 2 = 0 ∧ gamma ∉ W ∧
        V.toFinset = W.toFinset ∪ {gamma} ∧ Disjoint W.toFinset {gamma} ∧
        V.toFinsetᶜ = W.toFinsetᶜ \ {gamma} ∧
        remainingSmall t V = remainingSmall t W \ {gamma} ∧
        G k t V = G k t W ∧ H k t V = H k t W ∧ U V + 1 = U W ∧
        mass f V = mass f W + f gamma ∧
        remainingMass f V = -mass f V))) ∨
    (beta ∉ W ∧ gamma ∈ A ∧ f beta = L ∧
      1 ≤ delta ∧ 3 * delta ≤ d - 2 ∧ (Y + 1) / 2 - d ≤ v ∧ v ≤ C k - Y ∧
      Q k ≤ D ∧ D < L ∧ L < P ∧ 2 * d ≤ Q k - 1 ∧
      max Z1 Z2 ≤ L ∧ (max Z1 Z2 = L → min Z1 Z2 ≤ D) ∧
      (L % 2 = 0 → f gamma = L / 2 ∧ 0 < f gamma ∧ |f gamma| < Q k) ∧
      (L % 2 = 1 → f gamma = -((N k - L) / 2) ∧
        D < L ∧ L < (N k - L) / 2 ∧ (N k - L) / 2 < P ∧ P < Y)) := by
  classical
  dsimp only
  let f := s k t
  let n := hit k 1 p
  let x := hit k 2 p
  let W := oldWord p y zpen z A T0 T1 T2 E
  let S := smallWord T0 T1 T2 E
  let F := A ++ [x] ++ T0 ++ [y]
  let R := T1 ++ [zpen] ++ T2 ++ [z] ++ E
  let beta := (finRotate k).symm y
  let gamma := (finRotate k).symm beta
  let P := f p
  let D := |f n|
  let r := |f x|
  let Y := -f y
  let Z1 := -f zpen
  let Z2 := -f z
  let L := (N k - Y) / 2
  let d := P - D
  let delta := Y - P
  let v := mass f F
  change Legal k t W at hW
  change p ∉ W at hpunused
  change n ∉ W at hnunused
  change ∀ i ∈ S, |f i| < Q k at hsmall
  change C k - P < mass f W at hblocklo
  change mass f W < D at hblockhi
  have hdEq : d = P - D := rfl
  have hdeltaEq : delta = Y - P := rfl
  have hPval : f p = P := rfl
  have hYval : f y = -Y := by dsimp only [Y]; omega
  have hZ1val : f zpen = -Z1 := by dsimp only [Z1]; omega
  have hZ2val : f z = -Z2 := by dsimp only [Z2]; omega
  have geo := native_geometry hk t p hnlarge hexpand
  obtain ⟨hQ, hN, hC, hNpos, hNodd⟩ := source_geometry hk
  change 2 ≤ Q k at hQ
  change N k = 4 * Q k - 1 at hN
  change C k = 2 * Q k - 1 at hC
  change 0 < N k at hNpos
  change N k % 2 = 1 at hNodd
  have hP : 0 < P := hpositive
  have hnval : f n = -D := by
    simpa [f, n, D, orient, show ¬ s k t p < 0 by omega] using geo.nValue
  have hxval : f x = r := by
    simpa [f, x, r, orient, show ¬ s k t p < 0 by omega] using geo.xValue
  have hD : Q k ≤ D := hnlarge
  have hDP : D < P := by simpa only [abs_of_pos hpositive] using geo.strictOrder.1
  have hPr : P < r := by simpa only [abs_of_pos hpositive] using geo.strictOrder.2
  have hDeq : D = N k - 2 * P := by
    simpa only [abs_of_pos hpositive] using geo.firstEquation
  have hreq : r = 2 * P - D := by
    have hr := geo.secondEquation
    rw [abs_of_pos hpositive] at hr
    change r = 4 * P - N k at hr
    omega
  have hbound (i : Fin k) : -C k ≤ f i ∧ f i ≤ C k :=
    centered_bounds hNpos hNodd _
  have hrC : r ≤ C k := by have hh := hbound x; omega
  have hY : P < Y := hyP
  have hYodd : Y % 2 = 1 := hyodd
  have hYQ : Q k ≤ Y := hylarge
  have hZ1 : Q k ≤ Z1 := hzpenlarge
  have hZ2 : Q k ≤ Z2 := hzlarge
  have hYC : Y ≤ C k := by have hh := hbound y; dsimp only [Y]; omega
  have hZ1C : Z1 ≤ C k := by have hh := hbound zpen; dsimp only [Z1]; omega
  have hZ2C : Z2 ≤ C k := by have hh := hbound z; dsimp only [Z2]; omega
  have hoddHalf : 2 * L = N k - Y := by dsimp only [L]; omega
  have hLQ : Q k ≤ L := by omega
  have hLP : L < P := by omega
  have hLpos : 0 < L := by omega
  have hLN : 3 * L < N k := by omega
  have h2d : 2 * d ≤ Q k - 1 := by dsimp only [d]; omega
  have hdpos : 0 < d := by dsimp only [d]; omega
  have hbval : f beta = L := by
    have hh := FirstNegativeShiftExchange.negative_parent k t hk y
      (show f y < 0 by omega)
    dsimp only at hh
    rcases hh with he | ho
    · omega
    · change _ ∧ 2 * f beta = N k - Y ∧ _ at ho
      omega
  have hgformula := positive_parent hk t beta (by change 0 < f beta; omega)
  change f gamma = if f beta % 2 = 0 then f beta / 2
    else (f beta - N k) / 2 at hgformula
  rw [hbval] at hgformula
  have hWshape : W = F ++ R := by
    simp only [W, oldWord, F, R, x, List.append_assoc]
  have hsplit (i : Fin k) :
      i ∈ W ↔ i ∈ A ∨ i = x ∨ i = y ∨ i = zpen ∨ i = z ∨ i ∈ S := by
    simp only [W, oldWord, S, smallWord, x, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false]
    tauto
  have hsF : InStrip f (C k) 0 F :=
    (strip_split F R (by simpa only [hWshape] using strip_of_legal hW)).1
  have hv0 : 0 ≤ v := by simpa only [v, mass, zero_add, List.take_length] using
    (inStrip_prefix hsF F.length).1
  have hvY : v ≤ C k - Y := by
    have hsBefore := (strip_split (A ++ [x] ++ T0) ([y] ++ R)
      (by simpa only [hWshape, F, List.append_assoc] using strip_of_legal hW)).2
    have hh := (inStrip_prefix hsBefore 0).2
    have heq : v = mass f (A ++ [x] ++ T0) - Y := by
      simp only [v, F, mass, List.map_append, List.map_cons, List.map_nil,
        List.sum_append, List.sum_cons, List.sum_nil, add_zero, Y]
      ring
    simp only [List.take_zero, List.map_nil, List.sum_nil, add_zero, zero_add] at hh
    change mass f (A ++ [x] ++ T0) ≤ C k at hh
    omega
  have hpn : p ≠ n := by intro he; have hh := congrArg f he; change P = f n at hh; omega
  have hpb : p ≠ beta := by intro he; have hh := congrArg f he; change P = f beta at hh; omega
  have hnb : n ≠ beta := by intro he; have hh := congrArg f he; omega
  have hbL : Large k t beta := by change Q k ≤ |f beta|; rw [hbval, abs_of_pos hLpos]; exact hLQ
  have hzpL : Large k t zpen := by change Q k ≤ |f zpen|; have := neg_le_abs (f zpen); dsimp only [Z1] at hZ1; omega
  have hzL : Large k t z := by change Q k ≤ |f z|; have := neg_le_abs (f z); dsimp only [Z2] at hZ2; omega
  have hRsmall (T : List (Fin k)) (hT : ∀ i ∈ T, i ∈ S) :
      largeUsed k t T = 0 ∧ H k t T = 0 :=
    small_weights t T (fun i hi => hsmall i (hT i hi))
  have hT1 := hRsmall T1 (by intro i hi; simp [S, smallWord, hi])
  have hT2 := hRsmall T2 (by intro i hi; simp [S, smallWord, hi])
  have hE := hRsmall E (by intro i hi; simp [S, smallWord, hi])
  have hRcount : largeUsed k t R = 2 := by
    simp [R, largeUsed_append, largeUsed_cons, largeWeight, hzpL, hzL,
      hT1.1, hT2.1, hE.1]
  have hREnergy : H k t R = 3 ^ (f zpen).natAbs + 3 ^ (f z).natAbs := by
    have heq : H k t R = H k t T1 + H k t [zpen] + H k t T2 + H k t [z] + H k t E := by
      simp only [R, H, mass, List.map_append, List.sum_append, Nat.add_assoc]
    rw [heq, hT1.2, hT2.2, hE.2]
    simp [H, mass, energyWeight, hzpL, hzL, f, s]
  have hPn : ((f p).natAbs : ℤ) = P := by
    rw [Int.natCast_natAbs, abs_of_pos hP]
  have hnL : ((f n).natAbs : ℤ) = D := by simp only [Int.natCast_natAbs, D]
  have hbLn : ((f beta).natAbs : ℤ) = L := by rw [Int.natCast_natAbs, hbval, abs_of_pos hLpos]
  have hz1n : ((f zpen).natAbs : ℤ) = Z1 := by
    simpa only [Int.natCast_natAbs,
      abs_of_neg (show f zpen < 0 by dsimp only [Z1] at hZ1; omega), Z1]
  have hz2n : ((f z).natAbs : ℤ) = Z2 := by
    simpa only [Int.natCast_natAbs,
      abs_of_neg (show f z < 0 by dsimp only [Z2] at hZ2; omega), Z2]
  -- The literal first-y gate supplies this exchange regardless of parent status.
  by_cases hpreEnergy : P < max Z1 Z2 ∨ max Z1 Z2 = P ∧ D < min Z1 Z2
  · have hsI : InStrip f (C k) v [p,n] := by
      change 0 ≤ v ∧ v ≤ C k ∧ 0 ≤ v + P ∧ v + P ≤ C k ∧
        0 ≤ v + P + f n ∧ v + P + f n ≤ C k
      rw [hnval]
      omega
    obtain ⟨hv, hs, hpref, inv, hp⟩ := prefix_insert hk t F R [p,n]
      (hWshape ▸ hW) (by simp [hpn])
      (by
        intro i hi
        rw [← hWshape]
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl
        · exact hpunused
        · exact hnunused)
      (by
        intro i hi
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl
        · exact geo.pLarge
        · exact geo.nLarge) hsI
    rw [← hWshape] at inv hp
    have hi : largeUsed k t [p,n] = 2 := by
      simp [largeUsed, mass, largeWeight, geo.pLarge, show Large k t n from geo.nLarge]
    have hie : H k t [p,n] = 3 ^ (f p).natAbs + 3 ^ (f n).natAbs := by
      simp [H, mass, energyWeight, geo.pLarge, show Large k t n from geo.nLarge, f, s]
    have hg : G k t (F ++ [p,n]) = G k t W := by
      have hh := inv.largeBalance
      rw [hi, hRcount] at hh
      omega
    have hen : 3 ^ (f p).natAbs + 3 ^ (f n).natAbs <
        (3 : ℕ) ^ (f zpen).natAbs + 3 ^ (f z).natAbs := by
      apply two_energy_threshold _ _ _ _ (by omega)
      have hm1 : ((max (f zpen).natAbs (f z).natAbs : ℕ) : ℤ) = max Z1 Z2 := by
        push_cast
        simpa only [Int.natCast_natAbs] using congrArg₂ max hz1n hz2n
      have hm2 : ((min (f zpen).natAbs (f z).natAbs : ℕ) : ℤ) = min Z1 Z2 := by
        push_cast
        simpa only [Int.natCast_natAbs] using congrArg₂ min hz1n hz2n
      omega
    have hh : H k t (F ++ [p,n]) < H k t W := by
      have hb := inv.energyBalance
      rw [hREnergy, hie] at hb
      omega
    have hj : J k t (F ++ [p,n]) < J k t W :=
      Prod.Lex.toLex_lt_toLex.mpr (Or.inr ⟨hg, Prod.Lex.toLex_lt_toLex.mpr (Or.inl hh)⟩)
    exact Or.inr (Or.inl ⟨F ++ [p,n], [p,n], R,
      hv, inv.nodup, hs, hpref, hp, hj,
      Or.inl ⟨inv, Or.inl ⟨rfl,rfl,rfl,hg,hh⟩⟩⟩)
  have hpreMax : max Z1 Z2 ≤ P :=
    le_of_not_gt (fun h => hpreEnergy (Or.inl h))
  have hpreTie : max Z1 Z2 = P → min Z1 Z2 ≤ D :=
    fun hm => le_of_not_gt (fun h => hpreEnergy (Or.inr ⟨hm, h⟩))
  by_cases hbetaA : beta ∈ A
  · exact Or.inl ⟨hbetaA, hpreMax, hpreTie⟩
  have hbunused : beta ∉ W := by
    intro hi
    rcases (hsplit beta).mp hi with ha | hx | hy | hzp | hz | hs
    · exact hbetaA ha
    · have hh := congrArg f hx; omega
    · have hh := congrArg f hy; dsimp only [Y] at hY; omega
    · have hh := congrArg f hzp; dsimp only [Z1] at hZ1; omega
    · have hh := congrArg f hz; dsimp only [Z2] at hZ2; omega
    · have hh := abs_lt.mp (hsmall beta hs); omega
  have hfresh3 (i : Fin k) (hi : i ∈ [p,n,beta]) : i ∉ W := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl
    · exact hpunused
    · exact hnunused
    · exact hbunused
  have hlarge3 (i : Fin k) (hi : i ∈ [p,n,beta]) : Large k t i := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl
    · exact geo.pLarge
    · exact geo.nLarge
    · exact hbL
  by_cases hgate : 2 * (v + d) ≤ Y - 1
  · have hsI : InStrip f (C k) v [p,n,beta] := by
      change 0 ≤ v ∧ v ≤ C k ∧ 0 ≤ v + P ∧ v + P ≤ C k ∧
        0 ≤ v + P + f n ∧ v + P + f n ≤ C k ∧
        0 ≤ v + P + f n + f beta ∧ v + P + f n + f beta ≤ C k
      rw [hnval, hbval]
      dsimp only [d] at hgate
      omega
    obtain ⟨hv, hs, hpref, inv, hp⟩ := prefix_insert hk t F R [p,n,beta]
      (hWshape ▸ hW) (by simp [hpn, hpb, hnb])
      (by simpa only [← hWshape] using hfresh3) hlarge3 hsI
    rw [← hWshape] at inv hp
    have hi : largeUsed k t [p,n,beta] = 3 := by
      simp [largeUsed, mass, largeWeight, geo.pLarge, show Large k t n from geo.nLarge, hbL]
    have hg : G k t (F ++ [p,n,beta]) + 1 = G k t W := by
      have hh := inv.largeBalance
      rw [hi, hRcount] at hh
      omega
    have hj : J k t (F ++ [p,n,beta]) < J k t W :=
      Prod.Lex.toLex_lt_toLex.mpr (Or.inl (by omega))
    exact Or.inr (Or.inl ⟨F ++ [p,n,beta], [p,n,beta], R,
      hv, inv.nodup, hs, hpref, hp, hj, Or.inl ⟨inv, Or.inr (Or.inl ⟨rfl,rfl,rfl,hgate,hg⟩)⟩⟩)
  have hnarrow : 3 * delta ≤ d - 2 := by dsimp only [delta, d]; omega
  have hvlower : (Y + 1) / 2 - d ≤ v := by omega
  have hDL : D < L := by dsimp only [delta, d] at hnarrow; omega
  by_cases henergy : L < max Z1 Z2 ∨ max Z1 Z2 = L ∧ D < min Z1 Z2
  · have hsI : InStrip f (C k) v [beta,n] := by
      change 0 ≤ v ∧ v ≤ C k ∧ 0 ≤ v + f beta ∧ v + f beta ≤ C k ∧
        0 ≤ v + f beta + f n ∧ v + f beta + f n ≤ C k
      rw [hbval, hnval]
      omega
    obtain ⟨hv, hs, hpref, inv, hp⟩ := prefix_insert hk t F R [beta,n]
      (hWshape ▸ hW) (by simp [hnb.symm])
      (by
        intro i hi
        rw [← hWshape]
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl
        · exact hbunused
        · exact hnunused)
      (by
        intro i hi
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl
        · exact hbL
        · exact geo.nLarge) hsI
    rw [← hWshape] at inv hp
    have hi : largeUsed k t [beta,n] = 2 := by
      simp [largeUsed, mass, largeWeight, hbL, show Large k t n from geo.nLarge]
    have hie : H k t [beta,n] = 3 ^ (f beta).natAbs + 3 ^ (f n).natAbs := by
      simp [H, mass, energyWeight, hbL, show Large k t n from geo.nLarge, f, s]
    have hg : G k t (F ++ [beta,n]) = G k t W := by
      have hh := inv.largeBalance
      rw [hi, hRcount] at hh
      omega
    have hen : 3 ^ (f beta).natAbs + 3 ^ (f n).natAbs <
        (3 : ℕ) ^ (f zpen).natAbs + 3 ^ (f z).natAbs := by
      apply two_energy_threshold _ _ _ _ (by omega)
      have hm1 : ((max (f zpen).natAbs (f z).natAbs : ℕ) : ℤ) = max Z1 Z2 := by
        push_cast
        simpa only [Int.natCast_natAbs] using congrArg₂ max hz1n hz2n
      have hm2 : ((min (f zpen).natAbs (f z).natAbs : ℕ) : ℤ) = min Z1 Z2 := by
        push_cast
        simpa only [Int.natCast_natAbs] using congrArg₂ min hz1n hz2n
      omega
    have hh : H k t (F ++ [beta,n]) < H k t W := by
      have hb := inv.energyBalance
      rw [hREnergy, hie] at hb
      omega
    have hj : J k t (F ++ [beta,n]) < J k t W :=
      Prod.Lex.toLex_lt_toLex.mpr (Or.inr ⟨hg, Prod.Lex.toLex_lt_toLex.mpr (Or.inl hh)⟩)
    exact Or.inr (Or.inl ⟨F ++ [beta,n], [beta,n], R,
      hv, inv.nodup, hs, hpref, hp, hj,
      Or.inl ⟨inv, Or.inr (Or.inr (Or.inl ⟨rfl,rfl,rfl,hg,hh⟩))⟩⟩)
  have hZmax : max Z1 Z2 ≤ L :=
    le_of_not_gt (fun h => henergy (Or.inl h))
  have hZtie : max Z1 Z2 = L → min Z1 Z2 ≤ D :=
    fun hm => le_of_not_gt (fun h => henergy (Or.inr ⟨hm, h⟩))
  have hZ1L : Z1 ≤ L := le_trans (le_max_left _ _) hZmax
  have hZ2L : Z2 ≤ L := le_trans (le_max_right _ _) hZmax
  have hgeven (he : L % 2 = 0) : f gamma = L / 2 ∧ 0 < f gamma ∧ |f gamma| < Q k := by
    have hv : f gamma = L / 2 := by simpa only [he, ite_true] using hgformula
    have ha : 0 < L / 2 ∧ L / 2 < Q k := by omega
    exact ⟨hv, by omega, by rw [hv, abs_of_pos ha.1]; exact ha.2⟩
  have hgodd (ho : L % 2 = 1) : f gamma = -((N k - L) / 2) ∧
      D < L ∧ L < (N k - L) / 2 ∧ (N k - L) / 2 < P ∧ P < Y := by
    have hv : f gamma = (L - N k) / 2 := by
      simpa only [if_neg (show L % 2 ≠ 0 by omega)] using hgformula
    have heq : 2 * ((N k - L) / 2) = N k - L := by omega
    refine ⟨by omega, hDL, by omega, ?_, hY⟩
    dsimp only [delta, d] at hnarrow
    omega
  have hresidual (hgA : gamma ∈ A) :
      beta ∉ W ∧ gamma ∈ A ∧ f beta = L ∧
      1 ≤ delta ∧ 3 * delta ≤ d - 2 ∧ (Y + 1) / 2 - d ≤ v ∧ v ≤ C k - Y ∧
      Q k ≤ D ∧ D < L ∧ L < P ∧ 2 * d ≤ Q k - 1 ∧
      max Z1 Z2 ≤ L ∧ (max Z1 Z2 = L → min Z1 Z2 ≤ D) ∧
      (L % 2 = 0 → f gamma = L / 2 ∧ 0 < f gamma ∧ |f gamma| < Q k) ∧
      (L % 2 = 1 → f gamma = -((N k - L) / 2) ∧
        D < L ∧ L < (N k - L) / 2 ∧ (N k - L) / 2 < P ∧ P < Y) :=
    ⟨hbunused, hgA, hbval, by dsimp only [delta]; omega, hnarrow, hvlower,
      hvY, hD, hDL, hLP, h2d, hZmax, hZtie, hgeven, hgodd⟩
  by_cases hgammaA : gamma ∈ A
  · exact Or.inr (Or.inr (hresidual hgammaA))
  by_cases heven : L % 2 = 0
  · obtain ⟨hgval, hgpos, hgsmall⟩ := hgeven heven
    by_cases hgunused : gamma ∉ W
    · have hcap : mass f W + f gamma ≤ C k := by
        change mass f W < D at hblockhi
        omega
      obtain ⟨hv, hs, hpref, hu, hd, hc, hsm, hg, hh, hU, hm, hcomp, hj⟩ :=
        small_append hk t W gamma hW hgunused hgsmall hgpos hcap
      have hp : ((W ++ [gamma]) ++ []).Perm (W ++ [gamma]) := by simp
      exact Or.inr (Or.inl ⟨W ++ [gamma], [gamma], [],
        hv, hv.1, hs, hpref, hp, hj,
        Or.inr ⟨rfl,rfl,rfl,heven,hgunused,hu,hd,hc,hsm,hg,hh,hU,hm,hcomp⟩⟩)
    · have hgS : gamma ∈ S := by
        have hgW : gamma ∈ W := by simpa using hgunused
        rcases (hsplit gamma).mp hgW with ha | hx | hy | hzp | hz | hs
        · exact False.elim (hgammaA ha)
        · have hh := congrArg f hx; have hs := abs_lt.mp hgsmall; omega
        · have hh := congrArg f hy; dsimp only [Y] at hYQ; omega
        · have hh := congrArg f hzp; dsimp only [Z1] at hZ1; omega
        · have hh := congrArg f hz; dsimp only [Z2] at hZ2; omega
        · exact hs
      have haBound : f gamma ≤ C k - f beta + 1 := by rw [hbval]; omega
      have hother (i : Fin k) (hi : i ∈ S) (_hne : i ≠ gamma) (hip : 0 < f i) :
          f i ≤ f gamma + (C k - f beta) + 1 := by
        have hiS := hsmall i hi
        rw [abs_of_pos hip] at hiS
        rw [hbval]
        omega
      obtain ⟨B, K, hB, hKB, hBsmall, hfull⟩ :=
        actualSource_threeLarge_singleAnchor_exchange_full k t hk p beta y zpen z gamma
          A T0 T1 T2 E hpositive hnlarge hexpand hW hpunused hnunused hbunused
          hsmall hylarge hzpenlarge hzlarge (by change Z2 ≤ f beta; omega)
          (by change Q k ≤ f beta; omega) (by change f beta < P; omega)
          hgS hgpos haBound hother
      obtain ⟨hv, hs, hpref, inv, hg, hU, henergyEq, hh, hj, hend, helo, hehi⟩ := hfull
      let V := A ++ [p,n] ++ K ++ [z,beta]
      let Ret := [x,y,zpen] ++ B
      have hp : (V ++ Ret).Perm (W ++ [p,n,beta]) := by
        apply List.perm_iff_count.mpr
        intro i
        have hc := hKB.count_eq i
        simp only [S, smallWord, List.count_append] at hc
        simp only [V, Ret, W, oldWord, x, List.count_append, List.count_cons, List.count_nil]
        omega
      exact Or.inr (Or.inl ⟨V, [p,n,beta], Ret,
        hv, inv.nodup, hs, hpref, hp, hj, Or.inl ⟨inv,
          Or.inr (Or.inr (Or.inr (Or.inr ⟨K,B,heven,hgS,hB,hKB,hBsmall,
            rfl,rfl,rfl,hg,hU,hh⟩)))⟩⟩)
  · have hodd : L % 2 = 1 := by omega
    let M := (N k - L) / 2
    obtain ⟨hgval, _, hLM, hMP, _⟩ := hgodd hodd
    change f gamma = -M at hgval
    change L < M at hLM
    change M < P at hMP
    have hgL : Large k t gamma := by
      change Q k ≤ |f gamma|
      rw [hgval, abs_of_neg (show -M < 0 by omega)]
      omega
    have hgunused : gamma ∉ W := by
      intro hi
      rcases (hsplit gamma).mp hi with ha | hx | hy | hzp | hz | hs
      · exact hgammaA ha
      · have hh := congrArg f hx; omega
      · have hh := congrArg f hy; dsimp only [Y] at hY; omega
      · have hh := congrArg f hzp; dsimp only [Z1] at hZ1L; omega
      · have hh := congrArg f hz; dsimp only [Z2] at hZ2L; omega
      · have hh := abs_lt.mp (hsmall gamma hs); omega
    have hMpos : 0 < M := lt_trans hLpos hLM
    have hgb : gamma ≠ beta := by
      intro he
      have hh : -M = L := by simpa only [hgval, hbval] using congrArg f he
      exact (ne_of_lt (lt_trans (neg_neg_of_pos hMpos) hLpos)) hh
    have hgp : gamma ≠ p := by
      intro he
      have hh : -M = P := by simpa only [hgval, hPval] using congrArg f he
      exact (ne_of_lt (lt_trans (neg_neg_of_pos hMpos) hP)) hh
    have hgn : gamma ≠ n := by
      intro he
      have hh : -M = -D := by simpa only [hgval, hnval] using congrArg f he
      exact (ne_of_lt (neg_lt_neg (lt_trans hDL hLM))) hh
    have hI : [beta,gamma,p,n].Nodup := by
      simp [hgb.symm, hpb.symm, hnb.symm, hgp, hgn, hpn]
    have hfresh (i : Fin k) (hi : i ∈ [beta,gamma,p,n]) : i ∉ F ++ R := by
      rw [← hWshape]
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl
      · exact hbunused
      · exact hgunused
      · exact hpunused
      · exact hnunused
    have hlarge (i : Fin k) (hi : i ∈ [beta,gamma,p,n]) : Large k t i := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl
      · exact hbL
      · exact hgL
      · exact geo.pLarge
      · exact geo.nLarge
    have hMeq : 2 * M = N k - L := by dsimp only [M]; omega
    have hwpos : 0 < v + L - M := by omega
    have hwB : v + L - M < C k - P := by omega
    have hsI : InStrip f (C k) v [beta,gamma,p,n] := by
      change 0 ≤ v ∧ v ≤ C k ∧
        0 ≤ v + f beta ∧ v + f beta ≤ C k ∧
        0 ≤ v + f beta + f gamma ∧ v + f beta + f gamma ≤ C k ∧
        0 ≤ v + f beta + f gamma + P ∧ v + f beta + f gamma + P ≤ C k ∧
        0 ≤ v + f beta + f gamma + P + f n ∧
          v + f beta + f gamma + P + f n ≤ C k
      rw [hbval, hgval, hnval]
      omega
    obtain ⟨hv, hs, hpref, inv, hp⟩ := prefix_insert hk t F R [beta,gamma,p,n]
      (hWshape ▸ hW) hI hfresh hlarge hsI
    rw [← hWshape] at inv hp
    have hi : largeUsed k t [beta,gamma,p,n] = 4 := by
      simp [largeUsed, mass, largeWeight, hbL, hgL, geo.pLarge, show Large k t n from geo.nLarge]
    have hg : G k t (F ++ [beta,gamma,p,n]) + 2 = G k t W := by
      have hh := inv.largeBalance
      rw [hi, hRcount] at hh
      omega
    have hj : J k t (F ++ [beta,gamma,p,n]) < J k t W :=
      Prod.Lex.toLex_lt_toLex.mpr (Or.inl (by omega))
    exact Or.inr (Or.inl ⟨F ++ [beta,gamma,p,n], [beta,gamma,p,n], R,
      hv, inv.nodup, hs, hpref, hp, hj,
      Or.inl ⟨inv, Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl,rfl,rfl,hodd,hg⟩)))⟩⟩)

/-- Move the ENTIRE actual SMALL prefix after a positive x, choosing a new
order for that batch. The untouched old tail starts at the same height.
In particular, the old order of A is not asserted legal after x. -/
private theorem normalize_small_prefix {k : ℕ} (hk : 3 ≤ k) (t : ℕ)
    (x : Fin k) (A tail : List (Fin k))
    (hW : Legal k t (A ++ [x] ++ tail))
    (hsmallA : ∀ i ∈ A, |s k t i| < Q k) (hxpos : 0 < s k t x) :
    ∃ Aprime : List (Fin k), Aprime.Perm A ∧
      InStrip (s k t) (C k) (s k t x) Aprime ∧
      Legal k t ([x] ++ Aprime ++ tail) ∧
      ([x] ++ Aprime ++ tail).Perm (A ++ [x] ++ tail) := by
  obtain ⟨hQ, _, hC, hNpos, hNodd⟩ := source_geometry hk
  change 2 ≤ Q k at hQ
  change C k = 2 * Q k - 1 at hC
  have hxC : s k t x ≤ C k := (centered_bounds hNpos hNodd _).2
  have hsplit := strip_split A ([x] ++ tail)
    (by simpa only [List.append_assoc] using strip_of_legal hW)
  have ha0 : 0 ≤ mass (s k t) A ∧ mass (s k t) A ≤ C k := by
    simpa only [List.take_length, zero_add, mass] using
      inStrip_prefix hsplit.1 A.length
  have hxtail : InStrip (s k t) (C k) (mass (s k t) A) (x :: tail) := by
    simpa only [zero_add, List.singleton_append] using hsplit.2
  have hend : 0 ≤ mass (s k t) A + s k t x ∧
      mass (s k t) A + s k t x ≤ C k := by
    simpa only [List.take_succ_cons, List.take_zero, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, add_zero] using inStrip_prefix hxtail 1
  have hcompatible : ∀ i ∈ A, ∀ j ∈ A,
      0 < s k t i → s k t j < 0 → s k t i - s k t j ≤ C k := by
    intro i hi j hj hip hjn
    have hiSmall := hsmallA i hi
    have hjSmall := hsmallA j hj
    rw [abs_of_pos hip] at hiSmall
    rw [abs_of_neg hjn] at hjSmall
    -- The integral opposite difference is at most 2Q-2, below C=2Q-1.
    omega
  obtain ⟨Aprime, hAprime, hsAprime⟩ :=
    exists_order_between (s k t) A (C k) (s k t x)
      ⟨le_of_lt hxpos, hxC⟩ (by
        change 0 ≤ s k t x + mass (s k t) A ∧
          s k t x + mass (s k t) A ≤ C k
        exact ⟨add_nonneg (le_of_lt hxpos) ha0.1, by omega⟩) hcompatible
  have hmassA : mass (s k t) Aprime = mass (s k t) A := by
    simpa only [mass] using (hAprime.map (s k t)).sum_eq
  have hsTail : InStrip (s k t) (C k)
      (s k t x + mass (s k t) Aprime) tail := by
    have he : s k t x + mass (s k t) Aprime = mass (s k t) A + s k t x := by
      rw [hmassA]
      omega
    rw [he]
    exact hxtail.2.2
  have hsNew : InStrip (s k t) (C k) 0 ([x] ++ Aprime ++ tail) := by
    change 0 ≤ (0 : ℤ) ∧ 0 ≤ C k ∧
      InStrip (s k t) (C k) (0 + s k t x) (Aprime ++ tail)
    refine ⟨by omega, by omega, ?_⟩
    simpa only [zero_add] using inStrip_append hsAprime hsTail
  have hp : ([x] ++ Aprime ++ tail).Perm (A ++ [x] ++ tail) := by
    have hfirst := (hAprime.cons x).append_right tail
    have hfirst' : ([x] ++ Aprime ++ tail).Perm (([x] ++ A) ++ tail) := by
      simpa only [List.singleton_append] using hfirst
    have hswap :=
      (List.perm_append_comm : ([x] ++ A).Perm (A ++ [x])).append_right tail
    simpa only [List.append_assoc] using hfirst'.trans hswap
  exact ⟨Aprime, hAprime, hsAprime,
    legal_of_strip (hp.nodup_iff.mpr hW.1) hsNew, hp⟩

set_option maxHeartbeats 1600000 in
/-- Unconditional classification for the ORIGINAL arbitrary-A source word.
The physical competitor is represented relative to the original batches or
to a constructed complete SMALL-prefix normalization. All Inventory and
strict-J comparisons are nevertheless with the original W. The only other
alternative requires a LARGE occurrence in the original A, together with
the exact original parent/grandparent placement and narrow-strip bounds. -/
theorem actualSource_threeNegative_oddFirstNegative_placement
    (k t : ℕ) (hk : 3 ≤ k) (p y zpen z : Fin k)
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
    (hblocklo : C k - s k t p < mass (s k t) (oldWord p y zpen z A T0 T1 T2 E))
    (hblockhi : mass (s k t) (oldWord p y zpen z A T0 T1 T2 E) < |s k t (hit k 1 p)|)
    (hyP : s k t p < -s k t y) (hyodd : (-s k t y) % 2 = 1) :
    let f := s k t
    let n := hit k 1 p
    let x := hit k 2 p
    let W := oldWord p y zpen z A T0 T1 T2 E
    let R := T1 ++ [zpen] ++ T2 ++ [z] ++ E
    let beta := (finRotate k).symm y
    let gamma := (finRotate k).symm beta
    let P := f p
    let D := |f n|
    let Y := -f y
    let Z1 := -f zpen
    let Z2 := -f z
    let L := (N k - Y) / 2
    let d := P - D
    let delta := Y - P
    let v := mass f (A ++ [x] ++ T0 ++ [y])
    (∃ A' T0' V I Ret : List (Fin k),
      ((A' = A ∧ T0' = T0) ∨
       (A' = [] ∧ ∃ Aprime : List (Fin k), Aprime.Perm A ∧ T0' = Aprime ++ T0)) ∧
      let W' := oldWord p y zpen z A' T0' T1 T2 E
      let S' := smallWord T0' T1 T2 E
      let F' := A' ++ [x] ++ T0' ++ [y]
      W'.Perm W ∧ Legal k t W' ∧ W'.toFinset = W.toFinset ∧
      mass f W' = mass f W ∧ G k t W' = G k t W ∧
      H k t W' = H k t W ∧ U W' = U W ∧ J k t W' = J k t W ∧
      (∀ i ∈ S', |f i| < Q k) ∧
      Legal k t V ∧ V.Nodup ∧ InStrip f (C k) 0 V ∧
      (∀ j : ℕ, 0 ≤ mass f (V.take j) ∧ mass f (V.take j) ≤ C k) ∧
      (V ++ Ret).Perm (W ++ I) ∧ J k t V < J k t W ∧
      ((Inventory k t W V I Ret ∧
        ((V = F' ++ [p,n] ∧ I = [p,n] ∧ Ret = R ∧
          G k t V = G k t W ∧ H k t V < H k t W) ∨
         (V = F' ++ [p,n,beta] ∧ I = [p,n,beta] ∧ Ret = R ∧
          2 * (v + d) ≤ Y - 1 ∧ G k t V + 1 = G k t W) ∨
         (V = F' ++ [beta,n] ∧ I = [beta,n] ∧ Ret = R ∧
          G k t V = G k t W ∧ H k t V < H k t W) ∨
         (V = F' ++ [beta,gamma,p,n] ∧ I = [beta,gamma,p,n] ∧ Ret = R ∧
          L % 2 = 1 ∧ G k t V + 2 = G k t W) ∨
         (∃ K B : List (Fin k),
          L % 2 = 0 ∧ gamma ∈ S' ∧ B.Subperm (positive t S') ∧ (K ++ B).Perm S' ∧
          (∀ i ∈ B, 0 < f i ∧ |f i| < Q k) ∧
          V = A' ++ [p,n] ++ K ++ [z,beta] ∧ I = [p,n,beta] ∧
          Ret = [x,y,zpen] ++ B ∧ G k t V = G k t W ∧
          U V = U W + B.length ∧ H k t V < H k t W))) ∨
       (V = W' ++ [gamma] ∧ I = [gamma] ∧ Ret = [] ∧
        L % 2 = 0 ∧ gamma ∉ W ∧
        V.toFinset = W.toFinset ∪ {gamma} ∧ Disjoint W.toFinset {gamma} ∧
        V.toFinsetᶜ = W.toFinsetᶜ \ {gamma} ∧
        remainingSmall t V = remainingSmall t W \ {gamma} ∧
        G k t V = G k t W ∧ H k t V = H k t W ∧ U V + 1 = U W ∧
        mass f V = mass f W + f gamma ∧
        remainingMass f V = -mass f V))) ∨
    ((∃ i ∈ A, Large k t i) ∧
      ((beta ∈ A ∧ max Z1 Z2 ≤ P ∧ (max Z1 Z2 = P → min Z1 Z2 ≤ D)) ∨
       (beta ∉ W ∧ gamma ∈ A ∧ f beta = L ∧
        1 ≤ delta ∧ 3 * delta ≤ d - 2 ∧ (Y + 1) / 2 - d ≤ v ∧ v ≤ C k - Y ∧
        Q k ≤ D ∧ D < L ∧ L < P ∧ 2 * d ≤ Q k - 1 ∧
        max Z1 Z2 ≤ L ∧ (max Z1 Z2 = L → min Z1 Z2 ≤ D) ∧
        (L % 2 = 0 → f gamma = L / 2 ∧ 0 < f gamma ∧ |f gamma| < Q k) ∧
        (L % 2 = 1 → f gamma = -((N k - L) / 2) ∧
          D < L ∧ L < (N k - L) / 2 ∧ (N k - L) / 2 < P ∧ P < Y)))) := by
  classical
  dsimp only
  let f := s k t
  let n := hit k 1 p
  let x := hit k 2 p
  let W := oldWord p y zpen z A T0 T1 T2 E
  let beta := (finRotate k).symm y
  let gamma := (finRotate k).symm beta
  change Legal k t W at hW
  change p ∉ W at hpunused
  change n ∉ W at hnunused
  -- The representative is chosen before the classifier is applied. A prefix
  -- with a LARGE occurrence is kept literally; only an all-SMALL A is moved.
  have hrepresentative : ∃ A' T0' : List (Fin k),
      ((A' = A ∧ T0' = T0 ∧ ∃ i ∈ A, Large k t i) ∨
       (A' = [] ∧ ∃ Aprime : List (Fin k), Aprime.Perm A ∧ T0' = Aprime ++ T0)) ∧
      Legal k t (oldWord p y zpen z A' T0' T1 T2 E) ∧
      (oldWord p y zpen z A' T0' T1 T2 E).Perm W ∧
      (∀ i ∈ smallWord T0' T1 T2 E, |f i| < Q k) := by
    by_cases hlargeA : ∃ i ∈ A, Large k t i
    · exact ⟨A, T0, Or.inl ⟨rfl, rfl, hlargeA⟩, hW, .refl _, hsmall⟩
    · have hsmallA : ∀ i ∈ A, |f i| < Q k := by
        intro i hi
        by_contra hnot
        exact hlargeA ⟨i, hi, show Large k t i from le_of_not_gt hnot⟩
      have hxpos : 0 < f x := by
        have geo := native_geometry hk t p hnlarge hexpand
        have hxval : f x = |f x| := by
          simpa [f, x, orient, show ¬ s k t p < 0 by omega] using geo.xValue
        have hxorder : |s k t p| < |f x| := geo.strictOrder.2
        have hP := abs_nonneg (s k t p)
        omega
      let tail := T0 ++ [y] ++ T1 ++ [zpen] ++ T2 ++ [z] ++ E
      have hWtail : Legal k t (A ++ [x] ++ tail) := by
        simpa only [W, oldWord, x, tail, List.append_assoc] using hW
      obtain ⟨Aprime, hAprime, _, hWprime, hperm⟩ :=
        normalize_small_prefix hk t x A tail hWtail hsmallA hxpos
      refine ⟨[], Aprime ++ T0, Or.inr ⟨rfl, Aprime, hAprime, rfl⟩, ?_, ?_, ?_⟩
      · simpa only [oldWord, x, tail, List.nil_append, List.append_assoc] using hWprime
      · simpa only [W, oldWord, x, tail, List.nil_append, List.append_assoc] using hperm
      · intro i hi
        have hS : smallWord (Aprime ++ T0) T1 T2 E =
            Aprime ++ smallWord T0 T1 T2 E := by
          simp only [smallWord, List.append_assoc]
        rw [hS] at hi
        rcases List.mem_append.mp hi with hi | hi
        · exact hsmallA i (hAprime.mem_iff.mp hi)
        · exact hsmall i hi
  obtain ⟨A', T0', hchoice, hWprime, hperm, hsmallprime⟩ := hrepresentative
  let W' := oldWord p y zpen z A' T0' T1 T2 E
  change Legal k t W' at hWprime
  change W'.Perm W at hperm
  have hmem (i : Fin k) : i ∈ W' ↔ i ∈ W := hperm.mem_iff
  have hused : W'.toFinset = W.toFinset := by
    ext i
    simpa only [List.mem_toFinset] using hmem i
  have hmass : mass f W' = mass f W := by
    simpa only [mass] using (hperm.map f).sum_eq
  have hg : G k t W' = G k t W := by simp only [G, remainingMass, hused]
  have hh : H k t W' = H k t W := by
    simpa only [H, mass] using (hperm.map (energyWeight k t)).sum_eq
  have hu : U W' = U W := by simp only [U, remainingMass, hused]
  have hj : J k t W' = J k t W := by simp only [J, hg, hh, hu]
  have hsm : remainingSmall t W' = remainingSmall t W := by
    simp only [remainingSmall, hused]
  have hprefixMass : mass f (A' ++ [x] ++ T0' ++ [y]) =
      mass f (A ++ [x] ++ T0 ++ [y]) := by
    rcases hchoice with ⟨rfl, rfl, _⟩ | ⟨rfl, Aprime, hAprime, rfl⟩
    · rfl
    · have hm := (hAprime.map f).sum_eq
      simp only [List.nil_append, mass, List.map_append, List.sum_append] at hm ⊢
      omega
  have hpprime : p ∉ W' := fun hi => hpunused ((hmem p).mp hi)
  have hnprime : n ∉ W' := fun hi => hnunused ((hmem n).mp hi)
  have hblockloprime : C k - f p < mass f W' := by
    rw [hmass]
    exact hblocklo
  have hblockhiprime : mass f W' < |f n| := by
    rw [hmass]
    exact hblockhi
  have hclassification := two_generation_placement k t hk p y zpen z
    A' T0' T1 T2 E hpositive hnlarge hexpand hWprime hpprime hnprime hsmallprime
    hylarge hzpenlarge hzlarge hblockloprime hblockhiprime hyP hyodd
  dsimp only at hclassification
  dsimp only [W', f, x] at hmem hused hmass hg hh hu hj hsm hprefixMass
  rcases hclassification with hbetaA | hcompetitor | hresidual
  · apply Or.inr
    rcases hchoice with ⟨rfl, rfl, hlargeA⟩ | ⟨hAempty, _⟩
    · exact ⟨hlargeA, Or.inl hbetaA⟩
    · rw [hAempty] at hbetaA
      exact False.elim (by simpa only [List.not_mem_nil] using hbetaA.1)
  · obtain ⟨V, I, Ret, hV, hnod, hs, hpref, hphys, hstrict, hbranches⟩ := hcompetitor
    change (V ++ Ret).Perm (W' ++ I) at hphys
    change J k t V < J k t W' at hstrict
    have hphysOriginal : (V ++ Ret).Perm (W ++ I) :=
      hphys.trans (hperm.append_right I)
    have hstrictOriginal : J k t V < J k t W :=
      lt_of_lt_of_eq hstrict hj
    apply Or.inl
    refine ⟨A', T0', V, I, Ret, ?_, hperm, hWprime, hused,
      hmass, hg, hh, hu, hj, hsmallprime, hV, hnod, hs, hpref,
      hphysOriginal, hstrictOriginal, ?_⟩
    · rcases hchoice with ⟨ha, ht, _⟩ | hn
      · exact Or.inl ⟨ha, ht⟩
      · exact Or.inr hn
    · rcases hbranches with ⟨inv, hkind⟩ | hsmallAppend
      · have invOriginal : Inventory k t W V I Ret := by
          exact ⟨inv.nodup,
            by simpa only [hused] using inv.used,
            by simpa only [hused] using inv.usedDisjoint,
            by simpa only [hused] using inv.unused,
            by simpa only [hused] using inv.unusedDisjoint,
            by simpa only [hg] using inv.largeBalance,
            by simpa only [hh] using inv.energyBalance,
            by simpa only [hu] using inv.countBalance,
            inv.complementSum,
            by simpa only [hmass] using inv.sourceBalance,
            by simpa only [hsm] using inv.smallPartition,
            by simpa only [hsm] using inv.smallDisjoint⟩
        exact Or.inl ⟨invOriginal, by simpa only [hg, hh, hu, hprefixMass] using hkind⟩
      · -- Keep the literal W' append, but transfer its physical set, SMALL
        -- subtraction, source mass and all three objective coordinates to W.
        exact Or.inr (by
          simpa only [hmem, hused, hsm, hg, hh, hu, hmass] using hsmallAppend)
  · apply Or.inr
    rcases hchoice with ⟨rfl, rfl, hlargeA⟩ | ⟨hAempty, _⟩
    · exact ⟨hlargeA, Or.inr hresidual⟩
    · have hgammaA : gamma ∈ A' := hresidual.2.1
      rw [hAempty] at hgammaA
      exact False.elim (by simpa only [List.not_mem_nil] using hgammaA)

end D5.S3.Combinatorics.Circle.OddFirstNegativePlacement

