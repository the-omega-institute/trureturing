/- GID: D5/S3/Combinatorics/Circle/CrossingAnchorOrdering
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/CrossingAnchorOrdering
   mirror-E: none(waiver:audit-open-22063)
   anchors: [mathlib/module/Mathlib.Data.List.Perm.Subperm]
   utility: none
   digest: An actual positive anchor orders two negative LARGE steps and every SMALL occurrence. -/
module
public import D5.S3.Combinatorics.Circle.SingleAnchorLargeExchange
public import Mathlib.Data.List.Perm.Subperm

/-! Complete physical orderings with a crossing anchor and arbitrary legal endpoint. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
namespace D5.S3.Combinatorics.Circle.CrossingAnchorOrdering
open SourceWidth ExpandingSourcePath MixedSuffixEnergy SmallStepOrdering
open TwoOppositeLargeExchange ThreeLargePacketExchange SingleAnchorLargeExchange

private theorem partition {α : Type*} (X K : List α)
    (hX : X.Nodup) (hK : K.Subperm X) :
    ∃ R : List α, (K ++ R).Perm X ∧
      ∀ i ∈ R, i ∈ X ∧ i ∉ K := by
  obtain ⟨Y, hY, hKY⟩ := List.subperm_iff.mp hK
  obtain ⟨R, hR⟩ := hKY.exists_perm_append
  have hp : (K ++ R).Perm X := hR.symm.trans hY
  have hn := List.nodup_append.mp (hp.nodup_iff.mpr hX)
  refine ⟨R, hp, fun i hi => ⟨hp.mem_iff.mp (List.mem_append_right _ hi), ?_⟩⟩
  intro hiK
  exact hn.2.2 i hiK i hi rfl

private theorem small_compatible {α : Type*} (f : α → ℤ)
    (Q C : ℤ) (hC : C = 2 * Q - 1) (p n : α)
    (hp : |f p| < Q) (hn : |f n| < Q) : f p - f n ≤ C := by
  have hp' := le_abs_self (f p)
  have hn' := neg_le_abs (f n)
  omega

/-- An actual anchor supplies a positive gate packet which is executed before
one negative LARGE; the entire SMALL complement then reaches the given end. -/
private theorem one_negative {α : Type*}
    (f : α → ℤ) (X : List α) (v a : α) (Q C u e : ℤ)
    (hQ : 2 ≤ Q) (hC : C = 2 * Q - 1) (hX : X.Nodup)
    (hv : v ∈ X) (ha : a ∈ X)
    (hvQ : Q ≤ -f v) (hvC : -f v ≤ C)
    (hsmall : ∀ i ∈ X, i ≠ v → |f i| < Q)
    (ha0 : 0 < f a) (haC : f a ≤ C + f v)
    (hother : ∀ i ∈ X, i ≠ a → 0 < f i → f i ≤ f a + (C + f v))
    (hu : 0 ≤ u ∧ u ≤ C) (he : 0 ≤ e ∧ e ≤ C)
    (hmass : u + mass f X = e) :
    ∃ L : List α, L.Perm X ∧ InStrip f C u L := by
  classical
  let T := X.erase v
  have hav : a ≠ v := by intro hh; rw [hh] at ha0; omega
  have haT : a ∈ T := (List.mem_erase_of_ne hav).mpr ha
  have hp : (T ++ [v]).Perm X :=
    List.perm_append_comm.trans (List.perm_cons_erase hv).symm
  have hTsmall (i : α) (hi : i ∈ T) : |f i| < Q :=
    hsmall i (List.mem_of_mem_erase hi) (hX.mem_erase_iff.mp hi).1
  have hmassT : mass f T + f v = mass f X := by
    simpa [mass] using (hp.map f).sum_eq
  obtain ⟨R, hRT, hRpositive, hgate⟩ : ∃ R : List α,
      R.Subperm T ∧ (∀ i ∈ R, 0 < f i) ∧
      -f v ≤ u + mass f R ∧ u + mass f R ≤ C := by
    by_cases hfit : -f v ≤ u
    · exact ⟨[], List.nil_subperm, by simp,
        by simpa [mass] using hfit, by simpa [mass] using hu.2⟩
    · let Pos := T.filter (fun i => decide (0 < f i))
      have hPosT : Pos.Sublist T := List.filter_sublist
      have haPos : a ∈ Pos := by simp [Pos, haT, ha0]
      have hdom : mass f T ≤ mass f Pos := positive_mass_dominates f T
      have htotal : -f v - u ≤ mass f Pos := by omega
      obtain ⟨R, hR, hlo, hhi⟩ := single_anchor_select f Pos a (f a)
        (C + f v) (-f v - u) haPos rfl ha0 (by omega) (by omega)
        (by
          intro i hi
          have hh : i ∈ T ∧ 0 < f i := by simpa [Pos] using hi
          exact ⟨hh.2, fun hia => by
            have ho := hother i (List.mem_of_mem_erase hh.1) hia hh.2
            omega⟩) htotal
      refine ⟨R, hR.trans hPosT.subperm, ?_, by omega, by omega⟩
      intro i hi
      have him := hR.subset hi
      exact (List.mem_filter.mp him).2 |> of_decide_eq_true
  obtain ⟨S, hRS, hS⟩ := partition T R (hX.erase v) hRT
  have hmRS : mass f R + mass f S = mass f T := by
    simpa [mass] using (hRS.map f).sum_eq
  have hstart : 0 ≤ u + mass f R + f v ∧ u + mass f R + f v ≤ C := by omega
  have hend : 0 ≤ u + mass f R + f v + (S.map f).sum ∧
      u + mass f R + f v + (S.map f).sum ≤ C := by
    change 0 ≤ u + mass f R + f v + mass f S ∧
      u + mass f R + f v + mass f S ≤ C
    constructor <;> omega
  obtain ⟨L, hL, hsL⟩ := exists_order_between f S C (u + mass f R + f v)
    hstart hend (fun p hp n hn _ _ => small_compatible f Q C hC p n
      (hTsmall p (hS p hp).1) (hTsmall n (hS n hn).1))
  have hsR : InStrip f C u R := by
    apply strip_of_all_prefixes
    intro j
    have hn : 0 ≤ mass f (R.take j) := by
      apply List.sum_nonneg
      intro z hz
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hz
      exact le_of_lt (hRpositive i ((List.take_sublist j R).subset hi))
    have hl : mass f (R.take j) ≤ mass f R := by
      have hd : 0 ≤ mass f (R.drop j) := by
        apply List.sum_nonneg
        intro z hz
        obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hz
        exact le_of_lt (hRpositive i ((List.drop_sublist j R).subset hi))
      have hh : mass f (R.take j) + mass f (R.drop j) = mass f R := by
        simpa [mass] using congrArg (fun K : List α => (K.map f).sum)
          (List.take_append_drop j R)
      omega
    constructor <;> omega
  have hs : InStrip f C u (R ++ v :: L) := by
    apply inStrip_append hsR
    change InStrip f C (u + mass f R) (v :: L)
    exact ⟨by omega, hgate.2, hsL⟩
  refine ⟨R ++ v :: L, ?_, hs⟩
  apply List.perm_iff_count.mpr
  intro i
  have h1 := hRS.count_eq i
  have h2 := hp.count_eq i
  have h3 := hL.count_eq i
  simp only [List.count_append, List.count_cons, List.count_nil] at h1 h2 ⊢
  omega

set_option maxHeartbeats 1800000 in
private theorem two_negative_sorted {α : Type*}
    (f : α → ℤ) (T : List α) (v w a : α) (Q C b e : ℤ)
    (hQ : 2 ≤ Q) (hC : C = 2 * Q - 1)
    (hnd : (T ++ [v, w]).Nodup)
    (hsmall : ∀ i ∈ T, |f i| < Q)
    (hv : Q ≤ -f v ∧ -f v ≤ C) (hw : Q ≤ -f w ∧ -f w ≤ -f v)
    (ha : a ∈ T) (ha0 : 0 < f a) (haC : f a ≤ C + f v)
    (ham : -f w ≤ f a + (C + f v))
    (hb : 0 ≤ b ∧ b ≤ Q - 1) (he : 0 ≤ e ∧ e ≤ C)
    (hmass : b + mass f (T ++ [v, w]) = e) :
    ∃ L : List α, L.Perm (T ++ [v, w]) ∧ InStrip f C b L := by
  classical
  let X := T ++ [v, w]
  let c := C + f v
  change b + mass f X = e at hmass
  have hc : 0 ≤ c := by dsimp only [c]; omega
  have hbC : b ≤ C := by omega
  have hnT := (List.nodup_append.mp hnd).1
  have hvw : v ≠ w := by simpa using (List.nodup_append.mp hnd).2.1
  have hXmem (i : α) : i ∈ X ↔ i ∈ T ∨ i = v ∨ i = w := by simp [X]
  have hapos : |f a| < Q := hsmall a ha
  have hnotneg (i : α) (hi : i ∈ T) : i ≠ v ∧ i ≠ w := by
    have hs := hsmall i hi
    have hn := neg_le_abs (f i)
    constructor <;> intro h <;> subst i <;> omega
  have hav := (hnotneg a ha).1
  have haw := (hnotneg a ha).2
  have hfinishCompat (K : List α) (hK : K.Nodup) (hsub : K ⊆ X)
      (hsK : InStrip f C b K)
      (hcompat : ∀ p ∈ X, p ∉ K → ∀ n ∈ X, n ∉ K →
        0 < f p → f n < 0 → f p - f n ≤ C) :
      ∃ L : List α, L.Perm X ∧ InStrip f C b L := by
    obtain ⟨R, hpart, hR⟩ := partition X K hnd (hK.subperm hsub)
    have hsum : mass f K + mass f R = mass f X := by
      simpa [mass] using (hpart.map f).sum_eq
    have hs := inStrip_prefix hsK K.length
    simp only [List.take_length] at hs
    change 0 ≤ b + mass f K ∧ b + mass f K ≤ C at hs
    obtain ⟨L, hL, hsL⟩ := exists_order_between f R C (b + mass f K) hs
      (by change 0 ≤ b + mass f K + mass f R ∧ b + mass f K + mass f R ≤ C; constructor <;> omega)
      (fun p hp n hn => hcompat p (hR p hp).1 (hR p hp).2
        n (hR n hn).1 (hR n hn).2)
    exact ⟨K ++ L, (List.Perm.refl K |>.append hL).trans hpart,
      inStrip_append hsK hsL⟩
  have hfinishOne (K : List α) (r : α) (hK : K.Nodup) (hsub : K ⊆ X)
      (hsK : InStrip f C b K) (hr : r ∈ X) (hrK : r ∉ K)
      (haK : a ∉ K) (hrQ : Q ≤ -f r) (hrM : -f r ≤ -f v)
      (hrest : ∀ i ∈ X, i ∉ K → i ≠ r → |f i| < Q) :
      ∃ L : List α, L.Perm X ∧ InStrip f C b L := by
    obtain ⟨R, hpart, hR⟩ := partition X K hnd (hK.subperm hsub)
    have hRmem (i : α) (hi : i ∈ X) (hiK : i ∉ K) : i ∈ R := by
      have hh := hpart.mem_iff.mpr hi
      exact (List.mem_append.mp hh).resolve_left hiK
    have hsum : mass f K + mass f R = mass f X := by
      simpa [mass] using (hpart.map f).sum_eq
    have hs := inStrip_prefix hsK K.length
    simp only [List.take_length] at hs
    change 0 ≤ b + mass f K ∧ b + mass f K ≤ C at hs
    have hRsmall (i : α) (hi : i ∈ R) (hir : i ≠ r) : |f i| < Q :=
      hrest i (hR i hi).1 (hR i hi).2 hir
    obtain ⟨L, hL, hsL⟩ := one_negative f R r a Q C (b + mass f K) e hQ hC
      (List.nodup_append.mp (hpart.nodup_iff.mpr hnd)).2.1
      (hRmem r hr hrK) (hRmem a (hXmem a |>.mpr (Or.inl ha)) haK)
      hrQ (by omega) hRsmall ha0 (by omega)
      (by
        intro i hi hia hi0
        have hir : i ≠ r := by intro hh; subst i; omega
        have hh := hRsmall i hi hir
        have hl := le_abs_self (f i)
        omega) hs he (by omega)
    exact ⟨K ++ L, (List.Perm.refl K |>.append hL).trans hpart,
      inStrip_append hsK hsL⟩
  by_cases hbad : ∃ i ∈ T, c < f i
  · obtain ⟨i, hi, hib⟩ := hbad
    have his := hsmall i hi
    have hi0 : 0 < f i := by omega
    have hia : i ≠ a := by intro hh; subst i; dsimp only [c] at hib; omega
    obtain ⟨hiv, hiw⟩ := hnotneg i hi
    have hsI : InStrip f C b [i] := by
      change 0 ≤ b ∧ b ≤ C ∧ 0 ≤ b + f i ∧ b + f i ≤ C
      have hle := le_abs_self (f i)
      omega
    by_cases hsecond : ∃ j ∈ T, j ≠ i ∧ c < f j
    · obtain ⟨j, hj, hji, hjb⟩ := hsecond
      have hjs := hsmall j hj
      have hj0 : 0 < f j := by omega
      have hja : j ≠ a := by intro hh; subst j; dsimp only [c] at hjb; omega
      obtain ⟨hjv, hjw⟩ := hnotneg j hj
      by_cases hpair : b + f i + f j ≤ C
      · apply hfinishOne [i, j, w] v
        · simp [hji.symm, hiw, hjw]
        · intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl <;> simp [X, hi, hj]
        · change 0 ≤ b ∧ b ≤ C ∧ 0 ≤ b + f i ∧ b + f i ≤ C ∧
            0 ≤ b + f i + f j ∧ b + f i + f j ≤ C ∧
            0 ≤ b + f i + f j + f w ∧ b + f i + f j + f w ≤ C
          dsimp only [c] at hib hjb
          have hh := le_abs_self (f i)
          omega
        · simp [X]
        · simp [hiv.symm, hjv.symm, hvw]
        · simp [hia.symm, hja.symm, haw]
        · exact hv.1
        · omega
        · intro r hr hrK hrv
          rcases (hXmem r).mp hr with hr | rfl | rfl
          · exact hsmall r hr
          · exact False.elim (hrv rfl)
          · simp at hrK
      · by_cases hgate : -f w ≤ b + f i
        · apply hfinishOne [i, w] v
          · simp [hiw]
          · intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
            rcases hr with rfl | rfl <;> simp [X, hi]
          · change 0 ≤ b ∧ b ≤ C ∧ 0 ≤ b + f i ∧ b + f i ≤ C ∧
              0 ≤ b + f i + f w ∧ b + f i + f w ≤ C
            have hh := le_abs_self (f i); omega
          · simp [X]
          · simp [hiv.symm, hvw]
          · simp [hia.symm, haw]
          · exact hv.1
          · omega
          · intro r hr hrK hrv
            rcases (hXmem r).mp hr with hr | rfl | rfl
            · exact hsmall r hr
            · exact False.elim (hrv rfl)
            · simp at hrK
        · apply hfinishCompat [i, a, w, j, v]
          · simp [hia, hiv, hiw, hji.symm, hav, haw, hja.symm, hjw.symm, hjv, hvw.symm]
          · intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
            rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp [X, hi, ha, hj]
          · change 0 ≤ b ∧ b ≤ C ∧ 0 ≤ b + f i ∧ b + f i ≤ C ∧
              0 ≤ b + f i + f a ∧ b + f i + f a ≤ C ∧
              0 ≤ b + f i + f a + f w ∧ b + f i + f a + f w ≤ C ∧
              0 ≤ b + f i + f a + f w + f j ∧ b + f i + f a + f w + f j ≤ C ∧
              0 ≤ b + f i + f a + f w + f j + f v ∧
              b + f i + f a + f w + f j + f v ≤ C
            dsimp only [c] at hib hjb
            have hi' := le_abs_self (f i)
            have hj' := le_abs_self (f j)
            omega
          · intro p hp hpK n hn hnK _ _
            have hpT : p ∈ T := by
              rcases (hXmem p).mp hp with hp | rfl | rfl
              · exact hp
              · simp at hpK
              · simp at hpK
            have hnT : n ∈ T := by
              rcases (hXmem n).mp hn with hn | rfl | rfl
              · exact hn
              · simp at hnK
              · simp at hnK
            exact small_compatible f Q C hC p n (hsmall p hpT) (hsmall n hnT)
    · apply hfinishCompat [i]
      · simp
      · intro r hr
        simp only [List.mem_singleton] at hr
        subst r
        exact (hXmem i).mpr (Or.inl hi)
      · exact hsI
      · intro p hp hpK n hn hnK hp0 hn0
        have hpT : p ∈ T := by
          rcases (hXmem p).mp hp with hp | rfl | rfl
          · exact hp
          · omega
          · omega
        have hpbound : f p ≤ c := by
          by_contra hh
          have hpi : p ≠ i := by intro hh; subst p; simp at hpK
          exact hsecond ⟨p, hpT, hpi, by omega⟩
        rcases (hXmem n).mp hn with hn | rfl | rfl
        · exact small_compatible f Q C hC p n (hsmall p hpT) (hsmall n hn)
        · dsimp only [c] at hpbound; omega
        · dsimp only [c] at hpbound; omega
  · have hall (i : α) (hi : i ∈ T) : f i ≤ c := by
      by_contra hh; exact hbad ⟨i, hi, by omega⟩
    apply hfinishCompat [] (by simp) (by simp)
      (show InStrip f C b [] from ⟨hb.1, hbC⟩)
    intro p hp _ n hn _ hp0 hn0
    have hpT : p ∈ T := by
      rcases (hXmem p).mp hp with hp | rfl | rfl
      · exact hp
      · omega
      · omega
    have hpbound := hall p hpT
    rcases (hXmem n).mp hn with hn | rfl | rfl
    · exact small_compatible f Q C hC p n (hsmall p hpT) (hsmall n hn)
    · dsimp only [c] at hpbound; omega
    · dsimp only [c] at hpbound; omega

/-- Two distinct physical negative LARGE occurrences and every SMALL label
can be ordered using one actual crossing anchor. No bound on the number or
mass of incompatible positive labels, and no residual-width endpoint bound. -/
theorem exists_order_two_negative {α : Type*}
    (f : α → ℤ) (T : List α) (v1 v2 a : α) (Q C b e : ℤ)
    (hQ : 2 ≤ Q) (hC : C = 2 * Q - 1)
    (hnd : (T ++ [v1, v2]).Nodup)
    (hsmall : ∀ i ∈ T, |f i| < Q)
    (hv1 : Q ≤ -f v1 ∧ -f v1 ≤ C) (hv2 : Q ≤ -f v2 ∧ -f v2 ≤ C)
    (ha : a ∈ T) (ha0 : 0 < f a)
    (haC : f a ≤ C - max (-f v1) (-f v2))
    (ham : min (-f v1) (-f v2) ≤ f a + (C - max (-f v1) (-f v2)))
    (hb : 0 ≤ b ∧ b ≤ Q - 1) (he : 0 ≤ e ∧ e ≤ C)
    (hmass : b + mass f T + f v1 + f v2 = e) :
    ∃ L : List α, L.Perm (T ++ [v1, v2]) ∧ InStrip f C b L ∧
      b + mass f L = e ∧
      ∀ d : ℕ, 0 ≤ b + mass f (L.take d) ∧ b + mass f (L.take d) ≤ C := by
  have hbase : ∃ L : List α, L.Perm (T ++ [v1, v2]) ∧ InStrip f C b L := by
    classical
    by_cases hv : -f v2 ≤ -f v1
    · simp only [max_eq_left hv, min_eq_right hv] at haC ham
      apply two_negative_sorted f T v1 v2 a Q C b e hQ hC hnd hsmall hv1
        ⟨hv2.1, hv⟩ ha ha0 (by omega) (by omega) hb he
      simpa [mass, add_assoc] using hmass
    · have hv' : -f v1 ≤ -f v2 := by omega
      simp only [max_eq_right hv', min_eq_left hv'] at haC ham
      have hp : (T ++ [v2, v1]).Perm (T ++ [v1, v2]) :=
        (List.Perm.swap ..).append_left T
      obtain ⟨L, hL, hsL⟩ := two_negative_sorted f T v2 v1 a Q C b e hQ hC
        (hp.nodup_iff.mpr hnd) hsmall hv2 ⟨hv1.1, hv'⟩ ha ha0
        (by omega) (by omega) hb he (by
          simp only [mass, List.map_append, List.map_cons, List.map_nil,
            List.sum_append, List.sum_cons, List.sum_nil, add_zero]
          dsimp only [mass] at hmass
          omega)
      exact ⟨L, hL.trans hp, hsL⟩
  obtain ⟨L, hL, hsL⟩ := hbase
  refine ⟨L, hL, hsL, ?_, ?_⟩
  · have hm : mass f L = mass f T + f v1 + f v2 := by
      simpa [mass, add_assoc] using (hL.map f).sum_eq
    omega
  · intro d
    exact inStrip_prefix hsL d

#print axioms exists_order_two_negative
end D5.S3.Combinatorics.Circle.CrossingAnchorOrdering
