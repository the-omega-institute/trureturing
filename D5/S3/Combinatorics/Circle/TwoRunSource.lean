/- GID: D5/S3/Combinatorics/Circle/TwoRunSource
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/TwoRunSource
   mirror-E: none(waiver:no-escape-mirror-specified)
   anchors: [mathlib/module/Mathlib.Dynamics.PeriodicPts.Defs, mathlib/module/Mathlib.Logic.Equiv.Fin.Rotate]
   utility: none
   digest: Genuine-period ordering and disjoint physical repetition for actual two-run sources. -/
import D5.S3.Combinatorics.Circle.TwoLargeOrdering
import Mathlib.Dynamics.PeriodicPts.Defs
import Mathlib.Logic.Equiv.Fin.Rotate

/-! # Complete physical orderings for actual cyclic two-run sources -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Circle.TwoRunSource

open SourceWidth

/-- The actual centered source extended to all natural iterate indices. -/
def orbit (k t n : ℕ) : ℤ :=
  centered (modulus k) ((2 : ℤ) ^ n * (t : ℤ))

/-- The least dynamical period, including zero and nonunit source parameters. -/
noncomputable def period (k t : ℕ) : ℕ :=
  Function.minimalPeriod (doubleStep (modulus k)) (orbit k t 0)

/-- Zero source, or exactly one cyclic negative-to-positive crossing in its least period. -/
def TwoRun (k t : ℕ) : Prop :=
  orbit k t 0 = 0 ∨ (orbit k t 0 ≠ 0 ∧
    ∃! i : Fin (period k t), orbit k t i.val < 0 ∧
      0 < orbit k t (finRotate (period k t) i).val)

/-- Maximum magnitude over all physical labels, with repeated values still distinct. -/
def amplitude (k t : ℕ) : ℤ :=
  (Finset.univ.sup (fun i : Fin k => (actualSource k t i).natAbs) : ℕ)

private theorem modulus_positive_odd (k : ℕ) (hk : 0 < k) :
    0 < modulus k ∧ modulus k % 2 = 1 := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  have hp : 0 < (2 : ℤ) ^ j := pow_pos (by omega) _
  simp only [modulus, pow_succ]
  omega

private theorem orbit_step (k t : ℕ) (hk : 0 < k) (n : ℕ) :
    orbit k t (n + 1) = doubleStep (modulus k) (orbit k t n) := by
  obtain ⟨hN, hodd⟩ := modulus_positive_odd k hk
  have he : (2 : ℤ) ^ (n + 1) * (t : ℤ) = 2 * (2 ^ n * (t : ℤ)) := by
    rw [pow_succ]; ring
  change centered (modulus k) _ = _
  rw [he]
  exact centered_double hN hodd _

private theorem orbit_iterate (k t : ℕ) (hk : 0 < k) (n : ℕ) :
    (doubleStep (modulus k))^[n] (orbit k t 0) = orbit k t n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', ih, orbit_step k t hk]

private theorem actual_return (k t : ℕ) (hk : 0 < k) :
    Function.IsPeriodicPt (doubleStep (modulus k)) k (orbit k t 0) := by
  change (doubleStep (modulus k))^[k] (orbit k t 0) = orbit k t 0
  rw [orbit_iterate k t hk]
  simpa [orbit] using centered_full_period k t

private theorem period_facts (k t : ℕ) (hk : 0 < k) :
    0 < period k t ∧ period k t ≤ k ∧ period k t ∣ k := by
  have hr := actual_return k t hk
  exact ⟨hr.minimalPeriod_pos hk, hr.minimalPeriod_le hk, hr.minimalPeriod_dvd⟩

private theorem orbit_mod_period (k t : ℕ) (hk : 0 < k) (n : ℕ) :
    orbit k t (n % period k t) = orbit k t n := by
  simpa only [orbit_iterate k t hk, period] using
    (Function.iterate_mod_minimalPeriod_eq (f := doubleStep (modulus k))
      (x := orbit k t 0) (n := n))

private theorem orbit_period_return (k t : ℕ) (hk : 0 < k) :
    orbit k t (period k t) = orbit k t 0 := by
  simpa using (orbit_mod_period k t hk (period k t)).symm

private theorem orbit_bounds (k t : ℕ) (hk : 0 < k) (n : ℕ) :
    -(modulus k / 2) ≤ orbit k t n ∧ orbit k t n ≤ modulus k / 2 := by
  obtain ⟨hN, hodd⟩ := modulus_positive_odd k hk
  exact centered_bounds hN hodd _

private theorem magnitude_bound (k t : ℕ) (i : Fin k) :
    |actualSource k t i| ≤ amplitude k t := by
  have h := Finset.le_sup (s := Finset.univ)
    (f := fun i : Fin k => (actualSource k t i).natAbs) (Finset.mem_univ i)
  dsimp only [amplitude]
  rw [← Int.natCast_natAbs]
  exact_mod_cast h

private theorem amplitude_bounds (k t : ℕ) (hk : 0 < k) :
    0 ≤ amplitude k t ∧ amplitude k t ≤ ((2 : ℤ) ^ k - 2) / 2 := by
  obtain ⟨hN, hodd⟩ := modulus_positive_odd k hk
  have hn := Int.emod_add_mul_ediv (modulus k) 2
  have hhalf : modulus k / 2 = ((2 : ℤ) ^ k - 2) / 2 := by
    dsimp [modulus] at *
    omega
  refine ⟨Int.natCast_nonneg _, ?_⟩
  rw [← hhalf]
  have h : Finset.univ.sup (fun i : Fin k => (actualSource k t i).natAbs) ≤
      (modulus k / 2).toNat := by
    apply Finset.sup_le
    intro i _
    have hb := abs_le.mpr (orbit_bounds k t hk i.val)
    change |actualSource k t i| ≤ modulus k / 2 at hb
    rw [← Int.natCast_natAbs] at hb
    exact_mod_cast (hb.trans_eq (Int.toNat_of_nonneg (by omega)).symm)
  exact (Int.ofNat_le.mpr h).trans_eq (Int.toNat_of_nonneg (by omega))

private theorem period_magnitude (k t : ℕ) (hk : 0 < k) (i : Fin (period k t)) :
    |orbit k t i.val| ≤ amplitude k t := by
  exact magnitude_bound k t ⟨i.val, lt_of_lt_of_le i.isLt (period_facts k t hk).2.1⟩

private theorem orbit_nonzero (k t : ℕ) (hk : 0 < k) (h0 : orbit k t 0 ≠ 0)
    (n : ℕ) (hn : n < period k t) : orbit k t n ≠ 0 := by
  obtain ⟨hN, _⟩ := modulus_positive_odd k hk
  have hz : ∀ r, (doubleStep (modulus k))^[r] 0 = 0 := by
    intro r
    induction r with
    | zero => rfl
    | succ r ih =>
      rw [Function.iterate_succ_apply', ih]
      simp [doubleStep, not_lt.mpr hN.le]
  intro he
  apply h0
  rw [← orbit_period_return k t hk, ← orbit_iterate k t hk,
    ← Nat.sub_add_cancel (by omega : n ≤ period k t), Function.iterate_add_apply,
    orbit_iterate k t hk, he, hz]

private theorem cyclic_step (k t : ℕ) (hk : 0 < k) (i : Fin (period k t)) :
    orbit k t (finRotate (period k t) i).val =
      doubleStep (modulus k) (orbit k t i.val) := by
  have he := (period_facts k t hk).1
  let : NeZero (period k t) := ⟨ne_of_gt he⟩
  rw [finRotate_apply]
  simp only [Fin.val_add, Fin.val_one', Nat.add_mod_mod]
  rw [orbit_mod_period k t hk, orbit_step k t hk]

private theorem unique_exit {α : Type*} [Finite α]
    (σ : Equiv.Perm α) (v : α → ℤ) (hnz : ∀ i, v i ≠ 0)
    (hin : ∃! i, v i < 0 ∧ 0 < v (σ i)) :
    ∃! i, 0 < v i ∧ v (σ i) < 0 := by
  classical
  let := Fintype.ofFinite α
  let P := Finset.univ.filter (fun i => 0 < v i)
  let Q := Finset.univ.filter (fun i => 0 < v (σ i))
  have hQ : Q = P.map σ.symm.toEmbedding := by
    ext i
    simp [P, Q]
  have hcard : P.card = Q.card := by rw [hQ, Finset.card_map]
  have hmem (i) : i ∈ Q \ P ↔ v i < 0 ∧ 0 < v (σ i) := by
    simp only [P, Q, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ,
      true_and, not_lt]
    have := hnz i
    omega
  have hin' : ∃! i, i ∈ Q \ P := by simpa only [hmem] using hin
  have hcount : (P \ Q).card = 1 := by
    rw [Finset.card_sdiff_eq_card_sdiff_iff.mpr hcard]
    exact Finset.card_eq_one_iff_existsUnique.mpr hin'
  have hout := Finset.card_eq_one_iff_existsUnique.mp hcount
  convert hout using 1
  ext i
  simp only [P, Q, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and,
    not_lt]
  have := hnz (σ i)
  omega

private theorem large_crossing {N s s' A : ℤ} (hN : 0 < N) (hodd : N % 2 = 1)
    (hs : -(N / 2) ≤ s ∧ s ≤ N / 2) (hstep : s' = doubleStep N s)
    (_hA : 0 ≤ A) (hb : |s'| ≤ A) :
    (A < 2 * s → 0 < s ∧ s' < 0) ∧
      (A < -2 * s → s < 0 ∧ 0 < s') := by
  have hn := Int.emod_add_mul_ediv N 2
  have hb' := abs_le.mp hb
  dsimp only [doubleStep] at hstep
  split_ifs at hstep <;> constructor <;> intro h <;> omega

private theorem period_sum (k t : ℕ) (hk : 0 < k) :
    ((List.finRange (period k t)).map (fun i => orbit k t i.val)).sum = 0 := by
  obtain ⟨hN, hodd⟩ := modulus_positive_odd k hk
  let u : ℤ → ℤ := fun s => s + if s < 0 then modulus k else 0
  have hp := path_range (orbit k t) (period k t)
    (N := modulus k) (f := id) (u := u)
    (fun n _ => by
      dsimp [u]
      rw [orbit_step k t hk]
      exact unsigned_step hN hodd (orbit_bounds k t hk n))
    (fun n _ => orbit_step k t hk n)
  have hs := path_sum hp
  rw [orbit_period_return k t hk, sub_self] at hs
  have hl : (List.finRange (period k t)).map (fun i => orbit k t i.val) =
      (List.range (period k t)).map (orbit k t) := by
    apply List.ext_getElem <;> simp
  simpa [hl, List.map_map] using hs

private theorem period_large_unique (k t : ℕ) (hk : 0 < k)
    (h0 : orbit k t 0 ≠ 0)
    (hin : ∃! i : Fin (period k t), orbit k t i.val < 0 ∧
      0 < orbit k t (finRotate (period k t) i).val) :
    (∀ i j : Fin (period k t), amplitude k t < 2 * orbit k t i.val →
      amplitude k t < 2 * orbit k t j.val → i = j) ∧
    (∀ i j : Fin (period k t), amplitude k t < -2 * orbit k t i.val →
      amplitude k t < -2 * orbit k t j.val → i = j) := by
  have hout := unique_exit (finRotate (period k t)) (fun i => orbit k t i.val)
    (fun i => orbit_nonzero k t hk h0 i.val i.isLt) hin
  obtain ⟨hN, hodd⟩ := modulus_positive_odd k hk
  have hcross (i : Fin (period k t)) := large_crossing hN hodd
    (orbit_bounds k t hk i.val) (cyclic_step k t hk i) (amplitude_bounds k t hk).1
    (period_magnitude k t hk (finRotate (period k t) i))
  constructor
  · intro i j hi hj
    exact (hout.unique ((hcross i).1 hi) ((hcross j).1 hj))
  · intro i j hi hj
    exact (hin.unique ((hcross i).2 hi) ((hcross j).2 hj))

private theorem concatenate_zero {α β : Type*} (f : α → ℤ) (B : ℤ) (hB : 0 ≤ B)
    (blocks : List β) (words : β → List α)
    (hsum : ∀ j ∈ blocks, ((words j).map f).sum = 0)
    (hstrip : ∀ j ∈ blocks, InStrip f B 0 (words j)) :
    InStrip f B 0 (blocks.flatMap words) := by
  induction blocks with
  | nil => exact ⟨le_refl _, hB⟩
  | cons j js ih =>
    simp only [List.flatMap_cons]
    apply inStrip_append (hstrip j (by simp))
    simpa only [hsum j (by simp), add_zero] using
      ih (fun i hi => hsum i (by simp [hi])) (fun i hi => hstrip i (by simp [hi]))

/-- Every selected actual source has a complete physical-label ordering at its maximum
step magnitude, which is at most the original half-modulus capacity. -/
theorem exists_order (k : ℕ) (hk : 0 < k) (t : ℕ) (hsource : TwoRun k t) :
    ∃ word : List (Fin k), word.Perm (List.finRange k) ∧
      InStrip (actualSource k t) (amplitude k t) 0 word ∧
      0 ≤ amplitude k t ∧ amplitude k t ≤ ((2 : ℤ) ^ k - 2) / 2 := by
  classical
  have hA := amplitude_bounds k t hk
  rcases hsource with hzero | ⟨hzero, hcross⟩
  · have hz : ∀ n, orbit k t n = 0 := by
      intro n
      induction n with
      | zero => exact hzero
      | succ n ih =>
        rw [orbit_step k t hk, ih]
        have hN := (modulus_positive_odd k hk).1
        simp [doubleStep, not_lt.mpr hN.le]
    refine ⟨List.finRange k, .refl _, ?_, hA⟩
    apply inStrip_nonpos (fun i _ => le_of_eq (hz i.val)) hA.1
    have hf : actualSource k t = fun _ => 0 := funext (fun i => hz i.val)
    simp [hf]
  · obtain ⟨he, _, hedvd⟩ := period_facts k t hk
    let e := period k t
    let m := k / e
    have hme : m * e = k := Nat.div_mul_cancel hedvd
    let θ : Fin m × Fin e ≃ Fin k := finProdFinEquiv.trans (finCongr hme)
    let labels : Fin m → List (Fin k) :=
      fun j => (List.finRange e).map (fun i => θ (j, i))
    have hval (j : Fin m) (i : Fin e) : (θ (j, i)).val = i.val + e * j.val := rfl
    have hphysical (j : Fin m) (i : Fin e) :
        actualSource k t (θ (j, i)) = orbit k t i.val := by
      change orbit k t (θ (j, i)).val = _
      rw [hval, ← orbit_mod_period k t hk (i.val + e * j.val)]
      congr 1
      exact Nat.add_mul_mod_self_left _ _ _ |>.trans (Nat.mod_eq_of_lt i.isLt)
    have hsum (j : Fin m) : ((labels j).map (actualSource k t)).sum = 0 := by
      simpa only [labels, List.map_map, Function.comp_def, hphysical] using
        period_sum k t hk
    have hnd (j : Fin m) : (labels j).Nodup := by
      apply (List.nodup_finRange e).map
      intro a b hab
      exact (Prod.mk.inj (θ.injective hab)).2
    have hlarge := period_large_unique k t hk hzero hcross
    have horders (j : Fin m) : ∃ word : List (Fin k), word.Perm (labels j) ∧
        InStrip (actualSource k t) (amplitude k t) 0 word := by
      apply TwoLargeOrdering.exists_order _ _ _ (hnd j) hA.1 (hsum j)
        (fun i _ => magnitude_bound k t i)
      · intro x hx y hy hxl hyl
        obtain ⟨i, _, rfl⟩ := List.mem_map.mp hx
        obtain ⟨i', _, rfl⟩ := List.mem_map.mp hy
        rw [hphysical] at hxl hyl
        rw [hlarge.1 i i' hxl hyl]
      · intro x hx y hy hxl hyl
        obtain ⟨i, _, rfl⟩ := List.mem_map.mp hx
        obtain ⟨i', _, rfl⟩ := List.mem_map.mp hy
        rw [hphysical] at hxl hyl
        rw [hlarge.2 i i' hxl hyl]
    choose words hperm hstrip using horders
    have htotal (j : Fin m) : ((words j).map (actualSource k t)).sum = 0 :=
      ((hperm j).map _).sum_eq.trans (hsum j)
    have hflatten : (List.finRange m).flatMap labels =
        ((List.finRange m).product (List.finRange e)).map θ := by
      simp only [labels, List.product, List.map_flatMap, List.map_map, Function.comp_def]
    have hcomplete : ((List.finRange m).flatMap labels).Perm (List.finRange k) := by
      rw [hflatten]
      apply (List.perm_ext_iff_of_nodup
        (((List.nodup_finRange m).product (List.nodup_finRange e)).map θ.injective)
        (List.nodup_finRange k)).mpr
      intro x
      simp only [List.mem_finRange, iff_true]
      exact List.mem_map.mpr ⟨θ.symm x,
        List.mem_product.mpr ⟨by simp, by simp⟩, θ.apply_symm_apply x⟩
    exact ⟨(List.finRange m).flatMap words,
      (List.Perm.flatMap_left _ (fun j _ => hperm j)).trans hcomplete,
      concatenate_zero _ _ hA.1 _ words (fun j _ => htotal j) (fun j _ => hstrip j), hA⟩

#print axioms exists_order

end D5.S3.Combinatorics.Circle.TwoRunSource
