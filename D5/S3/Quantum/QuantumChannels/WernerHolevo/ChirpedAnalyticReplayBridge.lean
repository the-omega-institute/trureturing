/- GID: D5/S3/Quantum/QuantumChannels/WernerHolevo/ChirpedAnalyticReplayBridge
   generality: I
   mirror-B: D5/B/S3/Quantum/QuantumChannels/WernerHolevo/ChirpedAnalyticReplayBridge
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The analytic correlation residual and derivative matrix agree with the exact replay rows. -/

import D5.S3.Quantum.QuantumChannels.WernerHolevo.ChirpedAnalyticDrift
import D5.S3.Quantum.QuantumChannels.WernerHolevo.ChirpedFiniteBridge

open scoped BigOperators ComplexConjugate

namespace ChirpedAnalyticDrift.ReplayBridge

noncomputable section

open ChirpedFinite

variable {n m : ℕ} [NeZero n]

private def slot (m j : ℕ) : Option (Fin m) :=
  if h : j < m then some ⟨j, h⟩ else none

private def tagged (m : ℕ) (c : Chirp) : List (ℕ × Option (Fin m)) :=
  (0, none) :: (List.range c.orbits.length).flatMap
    (fun i => (c.orbits.getD i []).map (fun l => (l, slot m (c.first + i))))

private def label (m : ℕ) (c : Chirp) (l : ℕ) : Option (Fin m) :=
  ((tagged m c).find? (fun a => a.1 == l)).bind Prod.snd

/-- The left list is the replay's actual enumeration of frequency occurrences.
The right list runs once over every frequency with its assigned parameter. -/
def OrbitTable (n m : ℕ) (c : Chirp) : Prop :=
  (tagged m c).Perm ((List.range n).map fun l => (l, label m c l))

instance (n m : ℕ) (c : Chirp) : Decidable (OrbitTable n m c) :=
  inferInstanceAs (Decidable ((tagged m c).Perm ((List.range n).map fun l => (l, label m c l))))

private theorem find_tagged_of_nodup {α : Type*} {xs : List (ℕ × α)} {a : ℕ × α}
    (hn : (xs.map Prod.fst).Nodup) (ha : a ∈ xs) :
    xs.find? (fun b => b.1 == a.1) = some a := by
  induction xs with
  | nil => simp at ha
  | cons b xs ih =>
    rcases List.mem_cons.mp ha with rfl | ha
    · simp
    · obtain ⟨hb, htail⟩ := List.nodup_cons.mp hn
      have hne : b.1 ≠ a.1 := fun h => hb (h ▸ List.mem_map_of_mem ha)
      simp [List.find?_cons, hne, ih htail ha]

/-- The orbit partition determines the tagged table since each frequency occurs once. -/
theorem orbitTable_of_partition {n m : ℕ} (c : Chirp)
    (h : (0 :: c.orbits.flatten).Perm (List.range n)) : OrbitTable n m c := by
  have horbits : ((List.range c.orbits.length).map (fun i => c.orbits.getD i [])) = c.orbits := by
    apply List.ext_getElem (by simp)
    intro i _ hi
    rw [List.getElem_map, List.getElem_range, List.getD_eq_getElem c.orbits [] hi]
  have hkeys : ((tagged m c).map Prod.fst).Perm (List.range n) := by
    unfold tagged
    rw [List.map_cons, List.map_flatMap]
    simp only [List.map_map, Function.comp_def, List.map_id_fun', id_eq]
    rw [List.flatMap_def, horbits]
    exact h
  have hn := hkeys.nodup_iff.mpr List.nodup_range
  have htag : tagged m c = ((tagged m c).map Prod.fst).map (fun l => (l, label m c l)) := by
    calc
      tagged m c = (tagged m c).map id := (List.map_id _).symm
      _ = _ := by
        rw [List.map_map, List.map_inj_left]
        intro a ha
        simp [Function.comp_def, label, find_tagged_of_nodup hn ha]
  change (tagged m c).Perm _
  exact htag.symm ▸ hkeys.map (fun l => (l, label m c l))

def ValidSeed (n m : ℕ) : ChirpedFinite.Seed → Prop
  | .chirped c => c.first + c.orbits.length ≤ m ∧ OrbitTable n m c
  | .constantSpectrum k => k < m

instance (n m : ℕ) (s : ChirpedFinite.Seed) : Decidable (ValidSeed n m s) := by
  cases s <;> (unfold ValidSeed; infer_instance)

def pullback (s : ChirpedFinite.Seed) : ChirpedAnalyticDrift.Seed n (Fin m) :=
  match s with
  | .chirped c => ⟨(((n + 1) / 2 * c.phase : ℕ) : ZMod n), fun l => label m c l.val⟩
  | .constantSpectrum k => ⟨0, fun l => if l = 0 then slot m k else none⟩

def phaseAt (sign : Fin m → ℤ) (x : Fin m → ℝ) (j : ℕ) : ℂ :=
  if h : j < m then ChirpedReplay.cayley (x ⟨j, h⟩) (sign ⟨j, h⟩) else 0

def slopeAt (sign : Fin m → ℤ) (x : Fin m → ℝ) (j : ℕ) : ℂ :=
  if h : j < m then ChirpedReplay.cayleySlope (x ⟨j, h⟩) (sign ⟨j, h⟩) else 0

private def payload (sign : Fin m → ℤ) (x : Fin m → ℝ) : Option (Fin m) → ℂ
  | none => 1
  | some i => ChirpedReplay.cayley (x i) (sign i)

private def payloadD (sign : Fin m → ℤ) (x u : Fin m → ℝ) : Option (Fin m) → ℂ
  | none => 0
  | some i => u i • ChirpedReplay.cayleySlope (x i) (sign i)

private theorem payload_slot (sign : Fin m → ℤ) (x : Fin m → ℝ)
    {j : ℕ} (hj : j < m) :
    payload sign x (slot m j) = phaseAt sign x j := by
  simp [slot, hj, phaseAt, payload]

private theorem payloadD_slot (sign : Fin m → ℤ) (x : Fin m → ℝ) (i : Fin m)
    {j : ℕ} (hj : j < m) :
    payloadD sign x (Pi.single i 1) (slot m j) =
      if j = i.val then slopeAt sign x j else 0 := by
  by_cases hji : j = i.val
  · subst j
    simp [slot, i.isLt, slopeAt, payloadD]
  · have hi : (⟨j, hj⟩ : Fin m) ≠ i := fun h => hji (congrArg Fin.val h)
    simp [slot, hj, payloadD, Pi.single_eq_of_ne hi, hji]

private theorem spectrum_eq_payload (sign : Fin m → ℤ) (s : ChirpedFinite.Seed)
    (x : Fin m → ℝ) (l : ZMod n) :
    spectrum sign (pullback s) x l =
      payload sign x ((pullback s : ChirpedAnalyticDrift.Seed n (Fin m)).coord l) := by
  unfold spectrum
  cases (pullback s : ChirpedAnalyticDrift.Seed n (Fin m)).coord l <;> rfl

private theorem spectrumD_eq_payload (sign : Fin m → ℤ) (s : ChirpedFinite.Seed)
    (x u : Fin m → ℝ) (l : ZMod n) :
    spectrumD sign (pullback s) x l u =
      payloadD sign x u ((pullback s : ChirpedAnalyticDrift.Seed n (Fin m)).coord l) := by
  unfold spectrumD
  cases (pullback s : ChirpedAnalyticDrift.Seed n (Fin m)).coord l <;>
    simp [payloadD, ContinuousLinearMap.smulRight_apply]

private theorem stdAddChar_eq_exactRoot (a : ZMod n) :
    ZMod.stdAddChar a = exactRoot n a.val := by
  rw [ZMod.stdAddChar_apply, ZMod.toCircle_apply, exactRoot, ChirpedReplay.unitPhase]
  push_cast
  congr 1
  ring

private theorem sum_zmod_val (f : ℕ → ℂ) :
    (∑ j : ZMod n, f j.val) = sumRange n f := by
  let e : ZMod n ≃ Fin n :=
    { toFun := fun j => ⟨j.val, ZMod.val_lt j⟩
      invFun := fun j => (j.val : ZMod n)
      left_inv := ZMod.natCast_zmod_val
      right_inv := fun j => Fin.ext (ZMod.val_natCast_of_lt j.isLt) }
  exact (Fintype.sum_equiv e _ _ (fun _ => rfl)).trans (sumRange_fin n f)

private theorem sumRange_list (k : ℕ) (f : ℕ → ℂ) :
    ((List.range k).map f).sum = sumRange k f := by
  induction k with
  | zero => simp [sumRange]
  | succ k ih => simp only [List.sum_range_succ, ih, sumRange, Finset.sum_range_succ]

private theorem list_sum_flatMap {α : Type*} (l : List α) (f : α → List ℂ) :
    (l.flatMap f).sum = (l.map fun i => (f i).sum).sum := by
  induction l with
  | nil => rfl
  | cons i l ih => simp [List.flatMap_cons, List.sum_append, ih]

private theorem list_sum_getD (l : List ℕ) (f : ℕ → ℂ) :
    (l.map f).sum = sumRange l.length (fun i => f (l.getD i 0)) := by
  induction l with
  | nil => simp [sumRange]
  | cons a l ih =>
    rw [List.map_cons, List.sum_cons, ih]
    simp [sumRange, Finset.sum_range_succ', List.getD_cons_zero, List.getD_cons_succ, add_comm]

private theorem chirped_sum (c : Chirp) (hc : OrbitTable n m c) (d : ZMod n)
    (w : Option (Fin m) → ℂ) :
    transform (((n + 1) / 2 * c.phase : ℕ) : ZMod n) (Equiv.refl _)
      (fun l => w (label m c l.val)) d =
        (exactRoot n (chirpExponent n c d.val % n) * w none +
          sumRange c.orbits.length (fun i =>
            exactCoefficient n (chirpExponent n c d.val) d.val (c.orbits.getD i []) *
              w (slot m (c.first + i)))) / (n : ℂ) := by
  let e := chirpExponent n c d.val
  let rootAt (l : ℕ) := exactRoot n ((e + d.val * l) % n)
  have hcast (l : ZMod n) :
      (((n + 1) / 2 * c.phase : ℕ) : ZMod n) * d ^ 2 + l * d =
        ((e + d.val * l.val : ℕ) : ZMod n) := by
    simp only [e, chirpExponent, Nat.cast_add, Nat.cast_mul, Nat.cast_pow, ZMod.natCast_zmod_val]
    ring
  have he (l : ZMod n) :
      ZMod.stdAddChar ((((n + 1) / 2 * c.phase : ℕ) : ZMod n) * d ^ 2 + l * d) =
        rootAt l.val := by
    rw [hcast, stdAddChar_eq_exactRoot, ZMod.val_natCast]
  rw [transform_eq_sum]
  simp only [Equiv.refl_apply, he]
  rw [sum_zmod_val (fun l => rootAt l * w (label m c l)), ← sumRange_list,
    div_eq_mul_inv, mul_comm ((n : ℂ)⁻¹)]
  congr 1
  change (tagged m c).Perm ((List.range n).map fun l => (l, label m c l)) at hc
  have hperm := (hc.map (fun a => rootAt a.1 * w a.2)).sum_eq
  simp only [List.map_map, Function.comp_def] at hperm
  rw [← hperm]
  unfold tagged
  simp only [List.map_cons, List.sum_cons, List.map_flatMap, List.map_map, Function.comp_def,
    list_sum_flatMap]
  rw [sumRange_list]
  have hzero : rootAt 0 = exactRoot n (chirpExponent n c d.val % n) := by simp [rootAt, e]
  rw [hzero]
  congr 1
  apply sumRange_congr
  intro i _
  rw [List.sum_map_mul_right, list_sum_getD] <;> rfl

private theorem constant_sum (d : ZMod n) (q z : ℂ) :
    transform 0 (Equiv.refl _) (fun l => if l = 0 then q else z) d =
      (if d = 0 then z else 0) + (q - z) / (n : ℂ) := by
  classical
  have hterm (l : ZMod n) :
      ZMod.stdAddChar (l * d) * (if l = 0 then q else z) =
        ZMod.stdAddChar (d * l) * z + (if l = 0 then q - z else 0) := by
    by_cases hl : l = 0
    · subst l
      simp [AddChar.map_zero_eq_one]
    · simp [hl, mul_comm l d]
  simp only [transform_eq_sum, Equiv.refl_apply, zero_mul, zero_add, hterm,
    Finset.sum_add_distrib, ← Finset.sum_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true,
    phase_sum]
  have hn : (n : ℂ) ≠ 0 := NeZero.ne _
  by_cases hd : d = 0 <;> simp [hd, mul_add, ← mul_assoc, hn, div_eq_inv_mul]

theorem seedValue_eq (sign : Fin m → ℤ) (s : ChirpedFinite.Seed) (hs : ValidSeed n m s)
    (x : Fin m → ℝ) (d : ZMod n) :
    seedValue sign (pullback s) (Equiv.refl _) x d =
      exactSeedValue n (phaseAt sign x) d.val s := by
  unfold seedValue
  have hSpectrum : spectrum sign (pullback s : ChirpedAnalyticDrift.Seed n (Fin m)) x =
      fun l => payload sign x ((pullback s : ChirpedAnalyticDrift.Seed n (Fin m)).coord l) :=
    funext (spectrum_eq_payload sign s x)
  rw [hSpectrum]
  cases s with
  | chirped c =>
    rcases hs with ⟨hsize, horbits⟩
    change transform (((n + 1) / 2 * c.phase : ℕ) : ZMod n) (Equiv.refl _)
      (fun l => payload sign x (label m c l.val)) d = _
    rw [chirped_sum c horbits d (payload sign x)]
    unfold exactSeedValue
    congr 1
    have hnone : payload sign x none = 1 := rfl
    rw [hnone, mul_one]
    congr 1
    apply sumRange_congr
    intro i hi
    rw [payload_slot sign x (j := c.first + i) (by omega)]
  | constantSpectrum k =>
    change transform 0 _ (fun l => payload sign x (if l = 0 then slot m k else none)) d = _
    have h : (fun l : ZMod n => payload sign x (if l = 0 then slot m k else none)) =
        fun l => if l = 0 then phaseAt sign x k else 1 := by
      funext l
      by_cases hl : l = 0
      · simpa only [hl, ite_true] using payload_slot sign x hs
      · simp [hl, payload]
    rw [h, constant_sum]
    have hd : d.val = 0 ↔ d = 0 := by
      constructor
      · intro he
        exact (ZMod.natCast_zmod_val d).symm.trans (by simp [he])
      · rintro rfl
        simp
    simp [exactSeedValue, hd]

theorem seedD_single_eq (sign : Fin m → ℤ) (s : ChirpedFinite.Seed) (hs : ValidSeed n m s)
    (x : Fin m → ℝ) (d : ZMod n) (j : Fin m) :
    seedD sign (pullback s) (Equiv.refl _) x d (Pi.single j 1) =
      exactSeedSlope n (slopeAt sign x) d.val j.val s := by
  rw [congrFun (seedD_apply sign (pullback s) (Equiv.refl _) x (Pi.single j 1)) d]
  have hSpectrum :
      (fun l : ZMod n => spectrumD sign (pullback s) x l (Pi.single j 1)) =
        fun l => payloadD sign x (Pi.single j 1)
          ((pullback s : ChirpedAnalyticDrift.Seed n (Fin m)).coord l) :=
    funext (fun l => spectrumD_eq_payload sign s x (Pi.single j 1) l)
  rw [hSpectrum]
  cases s with
  | chirped c =>
    rcases hs with ⟨hsize, horbits⟩
    change transform (((n + 1) / 2 * c.phase : ℕ) : ZMod n) (Equiv.refl _)
      (fun l => payloadD sign x (Pi.single j 1) (label m c l.val)) d = _
    rw [chirped_sum c horbits d (payloadD sign x (Pi.single j 1))]
    simp only [payloadD, mul_zero, zero_add, exactSeedSlope]
    let term (i : ℕ) := exactCoefficient n (chirpExponent n c d.val) d.val (c.orbits.getD i [])
    have hsum :
        sumRange c.orbits.length (fun i => term i * payloadD sign x (Pi.single j 1)
          (slot m (c.first + i))) =
        sumRange c.orbits.length (fun i => term i *
          (if c.first + i = j.val then slopeAt sign x j.val else 0)) := by
      apply sumRange_congr
      intro i hi
      rw [payloadD_slot sign x j (by omega)]
      split_ifs with heq
      · rw [heq]
      · rfl
    change (sumRange c.orbits.length (fun i => term i * payloadD sign x (Pi.single j 1)
      (slot m (c.first + i)))) / (n : ℂ) = _
    rw [hsum]
    by_cases hj : c.first ≤ j.val ∧ j.val < c.first + c.orbits.length
    · rw [if_pos hj]
      have hk : j.val - c.first ∈ Finset.range c.orbits.length := Finset.mem_range.mpr (by omega)
      have he : c.first + (j.val - c.first) = j.val := by omega
      simp only [sumRange]
      rw [Finset.sum_eq_single_of_mem (j.val - c.first) hk]
      · simp [he, term]
      · intro i hi hne
        have hn : c.first + i ≠ j.val := by omega
        simp [hn]
    · rw [if_neg hj]
      have hz : sumRange c.orbits.length
          (fun i => term i * (if c.first + i = j.val then slopeAt sign x j.val else 0)) =
            sumRange c.orbits.length (fun _ => 0) := by
        apply sumRange_congr
        intro i hi
        have hn : c.first + i ≠ j.val := by omega
        simp [hn]
      rw [hz]
      simp [sumRange]
  | constantSpectrum k =>
    change transform 0 _ (fun l => payloadD sign x (Pi.single j 1)
      (if l = 0 then slot m k else none)) d = _
    have h : (fun l : ZMod n =>
        payloadD sign x (Pi.single j 1) (if l = 0 then slot m k else none)) =
          fun l => if l = 0 then (if k = j.val then slopeAt sign x k else 0) else 0 := by
      funext l
      by_cases hl : l = 0
      · simpa only [hl, if_true] using payloadD_slot sign x j hs
      · simp [hl, payloadD]
    rw [h, constant_sum]
    by_cases he : k = j.val
    · simp [exactSeedSlope, he]
    · have hjk : j.val ≠ k := Ne.symm he
      simp [exactSeedSlope, he, hjk]

theorem exactSeed_entry_bounds (sign : Fin m → ℤ) (hSign : ∀ j, sign j = 1 ∨ sign j = -1)
    (s : ChirpedFinite.Seed) (hs : ValidSeed n m s) (x : Fin m → ℝ)
    (d : Fin n) (j : Fin m) :
    ‖exactSeedValue n (phaseAt sign x) d.val s‖ ≤ 1 ∧
      ‖exactSeedSlope n (slopeAt sign x) d.val j.val s‖ ≤ 2 := by
  have hd := ZMod.val_natCast_of_lt d.isLt
  simpa only [seedValue_eq sign s hs, seedD_single_eq sign s hs, hd] using
    seed_entry_bounds sign hSign (pullback s) (Equiv.refl _) x (d.val : ZMod n) j

private theorem perm_val (u : (ZMod n)ˣ) (inverse : ℕ) (hu : (u : ZMod n) = inverse)
    (c : Constraint) (d : ZMod n) :
    (((u ^ c.power).mulLeft) d).val = leftColumn n inverse c d.val := by
  have h :
      (u ^ c.power).mulLeft d =
        ((((inverse ^ c.power % n) * d.val : ℕ)) : ZMod n) := by
    change (↑(u ^ c.power) : ZMod n) * d = _
    rw [Units.val_pow_eq_pow_val, hu, Nat.cast_mul, ZMod.natCast_mod,
      Nat.cast_pow, ZMod.natCast_zmod_val]
  rw [h, ZMod.val_natCast] <;> rfl

/-- The two finite views used by the arithmetic tables, with the left columns
read through multiplication by the indicated power of a unit. -/
def replayRows (u : (ZMod n)ˣ) (pick : Fin m → Constraint) (imag : Fin m → Bool)
    (s : ℕ → ChirpedFinite.Seed) (i : Fin m) : Row n (Fin m) where
  left := pullback (s (pick i).left)
  right := pullback (s (pick i).right)
  perm := (u ^ (pick i).power).mulLeft
  imag := imag i

theorem residual_eq (sign : Fin m → ℤ) (u : (ZMod n)ˣ)
    (inverse : ℕ) (hu : (u : ZMod n) = inverse)
    (pick : Fin m → Constraint) (imag : Fin m → Bool) (s : ℕ → ChirpedFinite.Seed)
    (hL : ∀ i, ValidSeed n m (s (pick i).left)) (hR : ∀ i, ValidSeed n m (s (pick i).right))
    (x : Fin m → ℝ) :
    residual sign (replayRows u pick imag s) x =
      (selectRows (n := n) inverse pick
        (fun k d => exactSeedValue n (phaseAt sign x) d (s k))
        (fun k d j => exactSeedSlope n (slopeAt sign x) d j (s k))).exactResidual imag := by
  funext i
  unfold residual rowValue ChirpedReplay.CorrelationRows.exactResidual
  rw [projection_apply]
  congr 1
  let f (d : ℕ) :=
    conj (exactSeedValue n (phaseAt sign x) (leftColumn n inverse (pick i) d) (s (pick i).left)) *
      exactSeedValue n (phaseAt sign x) d (s (pick i).right)
  change _ = ∑ d : Fin n, f d.val
  calc
    _ = ∑ d : ZMod n, f d.val := by
      apply Finset.sum_congr rfl
      intro d _
      change conj (seedValue sign (pullback (s (pick i).left)) (Equiv.refl _)
          x ((u ^ (pick i).power).mulLeft d)) *
        seedValue sign (pullback (s (pick i).right)) (Equiv.refl _) x d = _
      rw [seedValue_eq sign _ (hL i), seedValue_eq sign _ (hR i), perm_val u inverse hu]
    _ = _ := (sum_zmod_val f).trans (sumRange_fin n f).symm

theorem jacobian_eq (sign : Fin m → ℤ) (u : (ZMod n)ˣ)
    (inverse : ℕ) (hu : (u : ZMod n) = inverse)
    (pick : Fin m → Constraint) (imag : Fin m → Bool) (s : ℕ → ChirpedFinite.Seed)
    (hL : ∀ i, ValidSeed n m (s (pick i).left)) (hR : ∀ i, ValidSeed n m (s (pick i).right))
    (x : Fin m → ℝ) :
    LinearMap.toMatrix' (derivative sign (replayRows u pick imag s) x).toLinearMap =
      (selectRows (n := n) inverse pick
        (fun k d => exactSeedValue n (phaseAt sign x) d (s k))
        (fun k d j => exactSeedSlope n (slopeAt sign x) d j (s k))).exactJacobian imag := by
  funext i j
  rw [LinearMap.toMatrix'_apply]
  change rowD sign (replayRows u pick imag s i) x (Pi.single j 1) = _
  rw [rowD_apply, projection_apply]
  unfold ChirpedReplay.CorrelationRows.exactJacobian ChirpedReplay.correlation
  congr 1
  let lval (d : ℕ) := exactSeedValue n (phaseAt sign x) (leftColumn n inverse (pick i) d)
    (s (pick i).left)
  let rval (d : ℕ) := exactSeedValue n (phaseAt sign x) d (s (pick i).right)
  let lder (d : ℕ) := exactSeedSlope n (slopeAt sign x) (leftColumn n inverse (pick i) d) j.val
    (s (pick i).left)
  let rder (d : ℕ) := exactSeedSlope n (slopeAt sign x) d j.val (s (pick i).right)
  have hl : (∑ d : ZMod n,
      conj (seedD sign (pullback (s (pick i).left)) (Equiv.refl _) x
        ((u ^ (pick i).power).mulLeft d) (Pi.single j 1)) *
          seedValue sign (pullback (s (pick i).right)) (Equiv.refl _) x d) =
        ∑ d : Fin n, conj (lder d.val) * rval d.val := by
    let f (d : ℕ) := conj (lder d) * rval d
    trans ∑ d : ZMod n, f d.val
    · apply Finset.sum_congr rfl
      intro d _
      rw [seedD_single_eq sign _ (hL i), seedValue_eq sign _ (hR i), perm_val u inverse hu]
    · exact (sum_zmod_val f).trans (sumRange_fin n f).symm
  have hr : (∑ d : ZMod n,
      conj (seedValue sign (pullback (s (pick i).left)) (Equiv.refl _) x
        ((u ^ (pick i).power).mulLeft d)) *
          seedD sign (pullback (s (pick i).right)) (Equiv.refl _) x d (Pi.single j 1)) =
        ∑ d : Fin n, conj (lval d.val) * rder d.val := by
    let f (d : ℕ) := conj (lval d) * rder d
    trans ∑ d : ZMod n, f d.val
    · apply Finset.sum_congr rfl
      intro d _
      rw [seedValue_eq sign _ (hL i), seedD_single_eq sign _ (hR i), perm_val u inverse hu]
    · exact (sum_zmod_val f).trans (sumRange_fin n f).symm
  exact congrArg₂ (· + ·) hl hr

end

end ChirpedAnalyticDrift.ReplayBridge
