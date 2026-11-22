/- GID: D5/S3/Quantum/QuantumChannels/WernerHolevo/ChirpedActualSeedBounds
   generality: I
   mirror-B: D5/B/S3/Quantum/QuantumChannels/WernerHolevo/ChirpedActualSeedBounds
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Quantum/QuantumChannels/WernerHolevo/ChirpedBasisEndpoint.mixedUnitaryRank_seventy_three; instance=D5/S3/Quantum/QuantumChannels/WernerHolevo/Chirped73Bounds.strict_inclusion
   digest: Actual order-73 seed enclosures complete the exact root-existence proof. -/

import D5.S3.Quantum.QuantumChannels.WernerHolevo.ChirpedAnalyticOrders
import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Data.Fintype.EquivFin

/-! Signed-floor seed bounds for the two concrete chirped root certificates. -/

open scoped BigOperators

namespace ChirpedActualSeedBounds

open ChirpedFinite
open ChirpedReplay (chirpedSeed_error chirpedSlope_error unchirpedSeed unchirpedSeedExact
  unchirpedSeed_error unchirpedSlope unchirpedSlope_error)
open ChirpedReplay.IntComplex (decode)
open ChirpedAnalyticDrift.ReplayBridge (OrbitTable ValidSeed exactSeed_entry_bounds phaseAt slopeAt)

noncomputable section

private abbrev OrbitIndex (c : Chirp) :=
  Option ((i : Fin c.orbits.length) × Fin (c.orbits.getD i.val []).length)

private def frequency (c : Chirp) : OrbitIndex c → ℕ
  | none => 0
  | some ⟨i, l⟩ => (c.orbits.getD i.val []).getD l.val 0

private def parameter (c : Chirp) : OrbitIndex c → Option ℕ
  | none => none
  | some ⟨i, _⟩ => some (c.first + i.val)

/-- The fixed frequency is represented by `none`. Each other index is an
occurrence in the checked orbit table. -/
private theorem card_orbitIndex {n m : ℕ} {c : Chirp} (hc : OrbitTable n m c) :
    Fintype.card (OrbitIndex c) = n := by
  have hlen :
      ((0, (none : Option (Fin m))) :: (List.range c.orbits.length).flatMap
        (fun i => (c.orbits.getD i []).map (fun l =>
          (l, if h : c.first + i < m then some ⟨c.first + i, h⟩ else none)))).length = n :=
    (List.Perm.length_eq hc).trans ((List.length_map _).trans List.length_range)
  simp only [List.length_cons, List.length_flatMap, List.length_map] at hlen
  have hsum (k : ℕ) :
      ((List.range k).map (fun i => (c.orbits.getD i []).length)).sum =
        sumRange k (fun i => (c.orbits.getD i []).length) := by
    induction k with
    | zero => simp [sumRange]
    | succ k ih =>
      simp only [List.sum_range_succ, sumRange, Finset.sum_range_succ] at ih ⊢
      rw [ih]
  rw [hsum] at hlen
  rw [Fintype.card_option, Fintype.card_sigma]
  simp only [Fintype.card_fin]
  rw [sumRange_fin c.orbits.length (fun i => (c.orbits.getD i []).length)]
  exact hlen

/-- Group each integer or exact product by the Cayley parameter it uses. -/
private theorem orbit_sum {A B : Type*} [AddCommMonoid A] (c : Chirp)
    (r : ℕ → A) (p : Option ℕ → B) (mul : A → B → A)
    (hmul : ∀ (s : Finset ℕ) (f : ℕ → A) (b : B), mul (∑ l ∈ s, f l) b =
      ∑ l ∈ s, mul (f l) b) :
    (∑ t : OrbitIndex c, mul (r (frequency c t)) (p (parameter c t))) =
      mul (r 0) (p none) + sumRange c.orbits.length (fun i =>
        mul (sumRange (c.orbits.getD i []).length (fun l => r ((c.orbits.getD i []).getD l 0)))
          (p (some (c.first + i)))) := by
  rw [Fintype.sum_option, Fintype.sum_sigma]
  change mul (r 0) (p none) + (∑ i : Fin c.orbits.length,
    ∑ l : Fin (c.orbits.getD i.val []).length,
      mul (r ((c.orbits.getD i.val []).getD l.val 0)) (p (some (c.first + i.val)))) = _
  congr 1
  rw [← sumRange_fin c.orbits.length]
  apply Finset.sum_congr rfl
  intro i _
  rw [sumRange_fin (c.orbits.getD i.val []).length
    (fun l => mul (r ((c.orbits.getD i.val []).getD l 0)) (p (some (c.first + i.val))))]
  exact (hmul _ _ _).symm

private theorem sum_active {A : Type*} [AddCommMonoid A] (c : Chirp) (j : ℕ)
    (hj : c.first ≤ j ∧ j < c.first + c.orbits.length) (f : ℕ → A) :
    sumRange c.orbits.length (fun i => if c.first + i = j then f i else 0) = f (j - c.first) := by
  have hi : j - c.first ∈ Finset.range c.orbits.length := Finset.mem_range.mpr (by omega)
  rw [sumRange, Finset.sum_eq_single_of_mem _ hi]
  · simp [show c.first + (j - c.first) = j by omega]
  · intro i hi' hne
    have hlt := Finset.mem_range.mp hi'
    simp [show c.first + i ≠ j by omega]

private theorem slope_orbit_sum {A B : Type*} [AddCommMonoid A] [Zero B]
    (c : Chirp) (j : ℕ) (hj : c.first ≤ j ∧ j < c.first + c.orbits.length)
    (base : A) (coeff : ℕ → A) (b : B) (mul : A → B → A) (hzero : ∀ a, mul a 0 = 0) :
    mul base (if (none : Option ℕ) = some j then b else 0) +
        sumRange c.orbits.length (fun i => mul (coeff i) (if some (c.first + i) = some j then b else 0)) =
      mul (coeff (j - c.first)) b := by
  rw [if_neg (by simp : (none : Option ℕ) ≠ some j), hzero, zero_add]
  calc
    _ = sumRange c.orbits.length (fun i => if c.first + i = j then mul (coeff i) b else 0) := by
      apply sumRange_congr
      intro i _
      by_cases h : c.first + i = j <;> simp [h, hzero]
    _ = _ := sum_active c j hj _

private theorem one_decode : decode scale (scale, 0) = 1 := by
  apply Complex.ext <;> norm_num [decode, scale]

private theorem zero_decode : decode scale (0 : Gaussian) = 0 := by
  apply Complex.ext <;> simp [decode]

private theorem replay_scale : ChirpedReplay.scale = scale := rfl

private theorem replay_floor (z : Gaussian) (d : ℤ) :
    ChirpedReplay.IntComplex.floorPair z d = floorPair z d := rfl

private theorem inverse_smul_eq_div (n : ℕ) (z : ℂ) : (n : ℝ)⁻¹ • z = z / (n : ℂ) := by
  rw [Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_natCast, div_eq_inv_mul]

private theorem chirped_errors {n m : ℕ} (hn : 0 < n) (c : Chirp)
    (hc : ValidSeed n m (.chirped c)) (roots phases slopes : ℕ → Gaussian)
    (q q' : ℕ → ℂ)
    (hroot : ∀ r : Fin n, ‖decode scale (roots r.val) - exactRoot n r.val‖ ≤ 45 / (scale : ℝ))
    (hphase : ∀ k < m, ‖decode scale (phases k) - q k‖ ≤ 2 / (scale : ℝ))
    (hslope : ∀ k < m, ‖decode scale (slopes k) - q' k‖ ≤ 2 / (scale : ℝ))
    (hq : ∀ k < m, ‖q k‖ ≤ 1) (hq' : ∀ k < m, ‖q' k‖ ≤ 2)
    (d : Fin n) (j : Fin m) :
    ‖decode scale (seedValue n roots phases d.val (.chirped c)) -
        exactSeedValue n q d.val (.chirped c)‖ ≤ 52 / (scale : ℝ) ∧
    ‖decode scale (seedSlope n roots slopes d.val j.val (.chirped c)) -
        exactSeedSlope n q' d.val j.val (.chirped c)‖ ≤ 97 / (scale : ℝ) := by
  obtain ⟨hsize, htable⟩ := hc
  let e : OrbitIndex c ≃ Fin n := Fintype.equivFinOfCardEq (card_orbitIndex htable)
  let exponent := chirpExponent n c d.val
  let index (l : ℕ) : Fin n := ⟨(exponent + d.val * l) % n, Nat.mod_lt _ hn⟩
  let r (l : ℕ) := roots (index l).val
  let z (l : ℕ) := exactRoot n (index l).val
  let rFin (i : Fin n) := r (frequency c (e.symm i))
  let zFin (i : Fin n) := z (frequency c (e.symm i))
  have hzFin (i : Fin n) : ‖zFin i‖ ≤ 1 := by
    change ‖exactRoot n (index (frequency c (e.symm i))).val‖ ≤ 1
    simp only [exactRoot, ChirpedReplay.unitPhase, Complex.norm_exp_I_mul_ofReal, le_rfl]
  have hrFin (i : Fin n) : ‖decode scale (rFin i) - zFin i‖ ≤ 45 / (scale : ℝ) :=
    hroot (index (frequency c (e.symm i)))
  have int_sum (p : Option ℕ → Gaussian) :
      (∑ i, gmul (rFin i) (p (parameter c (e.symm i)))) =
        gmul (roots (exponent % n)) (p none) + sumRange c.orbits.length (fun i =>
          gmul (coefficient n roots exponent d.val (c.orbits.getD i [])) (p (some (c.first + i)))) := by
    exact (e.symm.sum_comp (fun t => gmul (r (frequency c t)) (p (parameter c t)))).trans
      (orbit_sum c r p gmul ChirpedReplay.IntComplex.mul_sum_left)
  have exact_sum (p : Option ℕ → ℂ) :
      (∑ i, zFin i * p (parameter c (e.symm i))) =
        exactRoot n (exponent % n) * p none + sumRange c.orbits.length (fun i =>
          exactCoefficient n exponent d.val (c.orbits.getD i []) * p (some (c.first + i))) := by
    exact (e.symm.sum_comp (fun t => z (frequency c t) * p (parameter c t))).trans
      (orbit_sum c z p (· * ·) Finset.sum_mul)
  constructor
  · let p : Option ℕ → Gaussian := fun k => k.elim (scale, 0) phases
    let w : Option ℕ → ℂ := fun k => k.elim 1 q
    let u := gscale scale (roots (exponent % n)) + sumRange c.orbits.length (fun i =>
      gmul (coefficient n roots exponent d.val (c.orbits.getD i [])) (phases (c.first + i)))
    have hbase (a : Gaussian) : gmul a (scale, 0) = gscale scale a := by
      apply Prod.ext <;> simp [gmul, gscale, mul_comm]
    have hu : u = ∑ i, ChirpedReplay.IntComplex.mul (rFin i) (p (parameter c (e.symm i))) := by
      change u = ∑ i, gmul (rFin i) (p (parameter c (e.symm i)))
      symm
      simpa only [p, Option.elim_none, Option.elim_some, hbase, u] using int_sum p
    have hp (t : OrbitIndex c) :
        ‖decode scale (p (parameter c t)) - w (parameter c t)‖ ≤ 2 / (scale : ℝ) := by
      cases t with
      | none =>
        change ‖decode scale (scale, 0) - 1‖ ≤ 2 / (scale : ℝ)
        rw [one_decode, sub_self, norm_zero]
        norm_num [scale]
      | some t =>
        have ht := t.1.isLt
        exact hphase (c.first + t.1.val) (by omega)
    have hw (t : OrbitIndex c) : ‖w (parameter c t)‖ ≤ 1 := by
      cases t with
      | none => simp [parameter, w]
      | some t =>
        have ht := t.1.isLt
        exact hq (c.first + t.1.val) (by omega)
    have hb := chirpedSeed_error hn u rFin (fun i => p (parameter c (e.symm i))) zFin
      (fun i => w (parameter c (e.symm i))) hzFin hrFin (fun i => hp (e.symm i)) hu
      (fun i => hw (e.symm i))
    rw [exact_sum w, inverse_smul_eq_div n] at hb
    simpa only [w, Option.elim_none, Option.elim_some, mul_one, seedValue, exactSeedValue,
      u, exponent, replay_scale, replay_floor] using hb
  · by_cases hj : c.first ≤ j.val ∧ j.val < c.first + c.orbits.length
    · let p : Option ℕ → Gaussian := fun k => if k = some j.val then slopes j.val else 0
      let w : Option ℕ → ℂ := fun k => if k = some j.val then q' j.val else 0
      let a (i : ℕ) := coefficient n roots exponent d.val (c.orbits.getD i [])
      let z' (i : ℕ) := exactCoefficient n exponent d.val (c.orbits.getD i [])
      let u := gmul (a (j.val - c.first)) (slopes j.val)
      have hmul (b : Gaussian) : gmul b 0 = 0 := by
        apply Prod.ext <;> simp [gmul]
      have hu : u = ∑ i, ChirpedReplay.IntComplex.mul (rFin i) (p (parameter c (e.symm i))) := by
        exact ((int_sum p).trans
          (slope_orbit_sum c j.val hj (roots (exponent % n)) a (slopes j.val) gmul hmul)).symm
      have he : (∑ i, zFin i * w (parameter c (e.symm i))) = z' (j.val - c.first) * q' j.val :=
        (exact_sum w).trans
          (slope_orbit_sum c j.val hj (exactRoot n (exponent % n)) z' (q' j.val) (· * ·) mul_zero)
      have hp (t : OrbitIndex c) :
          ‖decode scale (p (parameter c t)) - w (parameter c t)‖ ≤ 2 / (scale : ℝ) := by
        by_cases ht : parameter c t = some j.val
        · simpa only [p, w, if_pos ht] using hslope j.val j.isLt
        · simp only [p, w, if_neg ht, zero_decode, sub_zero, norm_zero]
          norm_num [scale]
      have hw (t : OrbitIndex c) : ‖w (parameter c t)‖ ≤ 2 := by
        by_cases ht : parameter c t = some j.val
        · simpa only [w, if_pos ht] using hq' j.val j.isLt
        · simp [w, ht]
      have hb := chirpedSlope_error hn u rFin (fun i => p (parameter c (e.symm i))) zFin
        (fun i => w (parameter c (e.symm i))) hzFin (fun i => hw (e.symm i)) hrFin
        (fun i => hp (e.symm i)) hu
      rw [he, inverse_smul_eq_div n] at hb
      simpa only [seedSlope, exactSeedSlope, if_pos hj, u, a, z', exponent,
        replay_scale, replay_floor] using hb
    · simp only [seedSlope, exactSeedSlope, if_neg hj, zero_decode, sub_zero, norm_zero]
      norm_num [scale]

private theorem constant_errors {m : ℕ} (k : Fin m) (phases slopes : ℕ → Gaussian)
    (q q' : ℕ → ℂ)
    (hphase : ‖decode scale (phases k.val) - q k.val‖ ≤ 2 / (scale : ℝ))
    (hslope : ‖decode scale (slopes k.val) - q' k.val‖ ≤ 2 / (scale : ℝ))
    (roots : ℕ → Gaussian) (d : Fin 73) (j : Fin m) :
    ‖decode scale (seedValue 73 roots phases d.val (.constantSpectrum k.val)) -
        exactSeedValue 73 q d.val (.constantSpectrum k.val)‖ ≤ 52 / (scale : ℝ) ∧
    ‖decode scale (seedSlope 73 roots slopes d.val j.val (.constantSpectrum k.val)) -
        exactSeedSlope 73 q' d.val j.val (.constantSpectrum k.val)‖ ≤ 97 / (scale : ℝ) := by
  have hd : d = 0 ↔ d.val = 0 := Fin.ext_iff
  constructor
  · have hb := unchirpedSeed_error d (phases k.val) (q k.val) hphase
    have hbase : ((if d = 0 then scale else 0), (0 : ℤ)) =
        (if d.val = 0 then ((scale, 0) : Gaussian) else 0) := by
      by_cases h : d.val = 0 <;> simp [hd, h]
    rw [unchirpedSeed, unchirpedSeedExact, replay_scale, replay_floor, hbase] at hb
    simpa only [hd, seedValue, exactSeedValue, Nat.cast_ofNat,
      show (73 : ℝ)⁻¹ • (q k.val - 1) = (q k.val - 1) / (73 : ℂ) from
        inverse_smul_eq_div 73 (q k.val - 1)] using hb
  · by_cases h : j.val = k.val
    · have hb := unchirpedSlope_error (slopes k.val) (q' k.val) hslope
      rw [unchirpedSlope, replay_scale, replay_floor] at hb
      simpa only [seedSlope, exactSeedSlope, if_pos h, h, ite_true, Nat.cast_ofNat,
        show (73 : ℝ)⁻¹ • q' k.val = q' k.val / (73 : ℂ) from
          inverse_smul_eq_div 73 (q' k.val)] using hb
    · simp only [seedSlope, exactSeedSlope, if_neg h, zero_decode, sub_zero, norm_zero]
      norm_num [scale]

private theorem seed_errors {n m : ℕ} (hn : 0 < n) (s : ChirpedFinite.Seed)
    (hs : ValidSeed n m s) (hconstant : n = 73 ∨ ∃ c, s = .chirped c)
    (roots phases slopes : ℕ → Gaussian) (sign : Fin m → ℤ) (center : Fin m → ℝ)
    (hroot : ∀ r : Fin n, ‖decode scale (roots r.val) - exactRoot n r.val‖ ≤ 45 / (scale : ℝ))
    (hphase : ∀ k : Fin m,
      ‖decode scale (phases k.val) - phaseAt sign center k.val‖ ≤ 2 / (scale : ℝ) ∧
      ‖decode scale (slopes k.val) - slopeAt sign center k.val‖ ≤ 2 / (scale : ℝ))
    (hSign : ∀ k, sign k = 1 ∨ sign k = -1)
    (d : Fin n) (j : Fin m) :
    ‖decode scale (seedValue n roots phases d.val s) -
        exactSeedValue n (phaseAt sign center) d.val s‖ ≤ 52 / (scale : ℝ) ∧
    ‖decode scale (seedSlope n roots slopes d.val j.val s) -
        exactSeedSlope n (slopeAt sign center) d.val j.val s‖ ≤ 97 / (scale : ℝ) := by
  cases s with
  | chirped c =>
    have hnrm (k : Fin m) :
        ‖phaseAt sign center k.val‖ ≤ 1 ∧ ‖slopeAt sign center k.val‖ ≤ 2 := by
      have h := ChirpedReplay.cayley_norm_bounds (center k) (sign k) (hSign k)
      simpa only [phaseAt, slopeAt, dif_pos k.isLt] using And.intro h.1.le h.2
    exact chirped_errors hn c hs roots phases slopes _ _ hroot
      (fun k hk => (hphase ⟨k, hk⟩).1) (fun k hk => (hphase ⟨k, hk⟩).2)
      (fun k hk => (hnrm ⟨k, hk⟩).1) (fun k hk => (hnrm ⟨k, hk⟩).2) d j
  | constantSpectrum k =>
    rcases hconstant with rfl | ⟨c, h⟩
    · let a : Fin m := ⟨k, hs⟩
      exact constant_errors a phases slopes _ _ (hphase a).1 (hphase a).2 roots d j
    · cases h

private theorem rows_of_seed_specs {n m count : ℕ} [NeZero n] (hn : 0 < n)
    (inverse : ℕ) (pick : Fin m → Constraint) (s : ℕ → ChirpedFinite.Seed)
    (v : ℕ → ℕ → Gaussian) (dv : ℕ → ℕ → ℕ → Gaussian)
    (roots phases slopes : ℕ → Gaussian) (sign : Fin m → ℤ) (center : Fin m → ℝ)
    (hvalid : ∀ k : Fin count, ValidSeed n m (s k.val))
    (hconstant : ∀ k : Fin count, n = 73 ∨ ∃ c, s k.val = .chirped c)
    (hselect : ∀ i, (pick i).left < count ∧ (pick i).right < count)
    (hseed : ∀ k : Fin count, ∀ d : Fin n,
      v k.val d.val = seedValue n roots phases d.val (s k.val) ∧
        ∀ j : Fin m, dv k.val d.val j.val = seedSlope n roots slopes d.val j.val (s k.val))
    (hroot : ∀ r : Fin n, ‖decode scale (roots r.val) - exactRoot n r.val‖ ≤ 45 / (scale : ℝ))
    (hphase : ∀ k : Fin m,
      ‖decode scale (phases k.val) - phaseAt sign center k.val‖ ≤ 2 / (scale : ℝ) ∧
      ‖decode scale (slopes k.val) - slopeAt sign center k.val‖ ≤ 2 / (scale : ℝ))
    (hSign : ∀ k, sign k = 1 ∨ sign k = -1) :
    ChirpedReplay.CorrelationRows.SeedBounds (selectRows (n := n) inverse pick v dv)
      (selectRows (n := n) inverse pick
        (fun k d => exactSeedValue n (phaseAt sign center) d (s k))
        (fun k d j => exactSeedSlope n (slopeAt sign center) d j (s k))) := by
  have errors (k : Fin count) (d : Fin n) (j : Fin m) :
      ‖decode scale (v k.val d.val) - exactSeedValue n (phaseAt sign center) d.val (s k.val)‖ ≤
        52 / (scale : ℝ) ∧
      ‖decode scale (dv k.val d.val j.val) -
          exactSeedSlope n (slopeAt sign center) d.val j.val (s k.val)‖ ≤ 97 / (scale : ℝ) := by
    rw [(hseed k d).1, (hseed k d).2 j]
    exact seed_errors hn (s k.val) (hvalid k) (hconstant k) roots phases slopes sign center
      hroot hphase hSign d j
  have norms (k : Fin count) (d : Fin n) (j : Fin m) :=
    exactSeed_entry_bounds sign hSign (s k.val) (hvalid k) center d j
  let leftSeed (i : Fin m) : Fin count := ⟨(pick i).left, (hselect i).1⟩
  let rightSeed (i : Fin m) : Fin count := ⟨(pick i).right, (hselect i).2⟩
  let leftCol (i : Fin m) (d : Fin n) : Fin n :=
    ⟨leftColumn n inverse (pick i) d.val, Nat.mod_lt _ hn⟩
  exact
    { leftError := fun i d => (errors (leftSeed i) (leftCol i d) i).1
      rightError := fun i d => (errors (rightSeed i) d i).1
      leftSlopeError := fun i j d => (errors (leftSeed i) (leftCol i d) j).2
      rightSlopeError := fun i j d => (errors (rightSeed i) d j).2
      leftNorm := fun i d => (norms (leftSeed i) (leftCol i d) i).1
      rightNorm := fun i d => (norms (rightSeed i) d i).1
      leftSlopeNorm := fun i j d => (norms (leftSeed i) (leftCol i d) j).2
      rightSlopeNorm := fun i j d => (norms (rightSeed i) d j).2 }

end

end ChirpedActualSeedBounds

set_option maxRecDepth 100000
set_option maxHeartbeats 12000000

namespace Chirped73

local instance : NeZero n := ⟨dimension_pos.ne'⟩

theorem seedBounds : ChirpedReplay.CorrelationRows.SeedBounds rows (exactRows center) := by
  refine ChirpedActualSeedBounds.rows_of_seed_specs (count := seeds.length)
    dimension_pos inverseMultiplier pick seed seedAt seedSlopeAt rootAt phaseAt slopeAt
    (fun i => signEntry i.val) center ?_ ?_ ?_ ?_ rootAt_error ?_ ?_
  · exact fun k => valid_seed k.val k.isLt
  · exact fun _ => Or.inl rfl
  · intro i
    exact constraints_domain ⟨(equation i.val).1, equation_domain i⟩
  · exact fun k d => seed_spec k.val k.isLt d.val d.isLt
  · intro j
    simpa only [ChirpedAnalyticDrift.ReplayBridge.phaseAt, ChirpedAnalyticDrift.ReplayBridge.slopeAt,
      dif_pos j.isLt] using phaseSlope_error j
  · exact fun i => (signs_unit i).symm

theorem existsUnique_zero_closedBall :
    ∃! x, x ∈ Metric.closedBall center ChirpedReplay.radius ∧ F x = 0 :=
  existsUnique_zero_of_seedBounds seedBounds

end Chirped73
