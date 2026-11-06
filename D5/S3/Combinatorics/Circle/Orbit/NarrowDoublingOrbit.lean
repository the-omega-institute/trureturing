/- GID: D5/S3/Combinatorics/Circle/Orbit/NarrowDoublingOrbit
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Circle/Orbit/NarrowDoublingOrbit
   mirror-E: none(waiver:no-escape-mirror-specified)
   anchors: [mathlib/module/Mathlib.Dynamics.PeriodicPts.Defs, mathlib/module/Mathlib.GroupTheory.OrderOfElement]
   utility: none
   digest: Exact unit-shift numerators classify actual anchored narrow doubling orbits. -/
import D5.S3.Combinatorics.Circle.Orbit.NarrowDoublingOrbit.Basic
import D5.S1.Words.AssociatedMersenne.CircularWords
import Mathlib.Data.Int.ModEq
import Mathlib.Data.ZMod.Basic
import Mathlib.Dynamics.PeriodicPts.Lemmas
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Data.Finset.Sort
import Mathlib.Tactic

/-! # Narrow doubling orbits at arbitrary odd modulus

For odd X >= 3 and 0 < Q < X, the actual least period r, gcd g and standard
orbit diameter W satisfy r >= 2, r = orderOf (2 : ZMod (X/g)) and, when
2*W < X, X/g = 2^r-1 and 2*W = X-g. The proof derives the sorted rotation,
its single actual temporal cycle, the adjacent-gap recurrence and gcd
cancellation. Nonunit seeds remain in scope.

The actual sorted gaps also recover every orbit point and its explicit
maximum from a unit index shift. The anchored interval holds exactly for
Q=(X/(2^r-1))*explicitNumerator r s u with 2^r-1 dividing X, r>=2,
0<s<r, coprime(s,r), and u the inverse of s modulo r. The converse derives
the actual period r and the gcd scale from the constructed orbit.

The fixed-Q height consumers use one consecutive actual-period block.
Full physical Circle J remains OPEN: no common physical permutation,
nested masks, joint-strip sufficiency or physical prescribed-Q realization
is asserted.

Attribution: elementary finite cyclic order, least-period and gcd arguments.
Caller-supplied Pro reasoning and independent ordinary checking were fallible
inputs; the successful native scoped Lean build establishes the formal proof.
No literature novelty or official acceptance is claimed.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false


namespace D5.S3.Combinatorics.Circle.NarrowDoublingOrbit

open D5.S1.Words.AssociatedMersenne.CircularWords

/-- All-odd-modulus classification, including nonunit seeds.
Its source proof uses the actual sorted gap cycle; no transitivity,
recurrence, reduced-modulus classification, or unit-seed premise is added.
No physical or official acceptance is asserted. -/
theorem narrow_classification {X Q : ℕ} (hX : 3 ≤ X) (hodd : Odd X)
    (hQ : 0 < Q) (hQX : Q < X) (hnarrow : 2 * diameter X Q < X) :
    2 ≤ period X Q ∧
    period X Q = orderOf (2 : ZMod (denominator X Q)) ∧
    denominator X Q = 2 ^ period X Q - 1 ∧
    2 * diameter X Q = X - Nat.gcd X Q := by
  have hXp : 0 < X := by omega
  have hr := period_ge_two hXp hodd hQ hQX
  have hg : 0 < Nat.gcd X Q := Nat.gcd_pos_of_pos_left Q hXp
  have hM : 0 < 2 ^ period X Q - 1 := by
    have hp : 1 < (2 : ℕ) ^ period X Q :=
      one_lt_pow' (by omega) (by omega)
    omega
  have hreturn := Function.isPeriodicPt_minimalPeriod
    (fun z : ZMod X => 2 * z) (Q : ZMod X)
  change Function.IsPeriodicPt (fun z : ZMod X => 2 * z) (period X Q)
    (Q : ZMod X) at hreturn
  have hpow := (periodic_iff_reduced hXp Q (period X Q)).mp hreturn
  have hcong : Nat.ModEq (denominator X Q) 1 (2 ^ period X Q) := by
    apply Nat.ModEq.symm
    apply (ZMod.natCast_eq_natCast_iff _ _ _).mp
    simpa only [Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one] using hpow
  have hDM : denominator X Q ∣ 2 ^ period X Q - 1 :=
    (Nat.modEq_iff_dvd' (by omega : 1 ≤ (2 : ℕ) ^ period X Q)).mp hcong
  obtain ⟨d, hdpos, hgdiv, hprod, hdiam, _⟩ :=
    narrow_gap_arithmetic hX hodd hQ hQX hnarrow
  obtain ⟨u, hu⟩ := hgdiv
  have hXD : Nat.gcd X Q * denominator X Q = X := by
    exact Nat.mul_div_cancel' (Nat.gcd_dvd_left X Q)
  have hXDZ : (Nat.gcd X Q : ℤ) * denominator X Q = (X : ℤ) := by
    exact_mod_cast hXD
  have hscale : (Nat.gcd X Q : ℤ) * denominator X Q =
      (Nat.gcd X Q : ℤ) * (((2 ^ period X Q - 1 : ℕ) : ℤ) * u) := by
    calc
      _ = (X : ℤ) := hXDZ
      _ = ((2 ^ period X Q - 1 : ℕ) : ℤ) * d := hprod
      _ = _ := by rw [hu]; ring
  have hD : (denominator X Q : ℤ) = ((2 ^ period X Q - 1 : ℕ) : ℤ) * u :=
    mul_left_cancel₀ (by exact_mod_cast hg.ne') hscale
  have hMD : 2 ^ period X Q - 1 ∣ denominator X Q :=
    Int.natCast_dvd_natCast.mp ⟨u, hD⟩
  have hDeq := Nat.dvd_antisymm hDM hMD
  have hcancel : ((2 ^ period X Q - 1 : ℕ) : ℤ) * d =
      ((2 ^ period X Q - 1 : ℕ) : ℤ) * Nat.gcd X Q := by
    rw [← hprod, ← hXDZ, hDeq]
    ring
  have hdg : d = (Nat.gcd X Q : ℤ) :=
    mul_left_cancel₀ (by exact_mod_cast hM.ne') hcancel
  rw [hdg] at hdiam
  exact ⟨hr, period_eq_order hXp Q, hDeq, by omega⟩

/-- Recover every sorted point and the explicit maximum from the original
actual narrow orbit. The period and scale are the actual period and gcd;
the shift, its coprimality and inverse are conclusions. An arbitrary seed
is not asserted to equal the maximum. -/
theorem narrow_explicit_numerator {X Q : ℕ} (hX : 3 ≤ X) (hodd : Odd X)
    (hQ : 0 < Q) (hQX : Q < X) (hnarrow : 2 * diameter X Q < X) :
    ∃ s u : ℕ, 0 < s ∧ s < period X Q ∧ Nat.Coprime s (period X Q) ∧
      u < period X Q ∧ (s : ZMod (period X Q)) * u = 1 ∧
      orbit X Q = (Finset.range (period X Q)).image
        (fun j => Nat.gcd X Q * explicitPoint (period X Q) s u j) ∧
      IsGreatest (↑(orbit X Q) : Set ℕ)
        (Nat.gcd X Q * explicitNumerator (period X Q) s u) := by
  classical
  have hXp : 0 < X := by omega
  have hc := narrow_classification hX hodd hQ hQX hnarrow
  have hr := hc.1
  let r := period X Q
  let g := Nat.gcd X Q
  letI : NeZero r := ⟨by dsimp [r]; omega⟩
  have hrp : 0 < r := by dsimp [r]; omega
  have hgX : g ≤ X := Nat.le_of_dvd hXp (Nat.gcd_dvd_left X Q)
  obtain ⟨d, _, _, hprod, hdiam, s, hs, htrans, hwalk⟩ :=
    narrow_gap_arithmetic hX hodd hQ hQX hnarrow
  obtain ⟨hspos, hcop, u, hu, hunit⟩ := transitive_shift_inverse hr s htrans
  have hdg : d = (g : ℤ) := by
    have := hc.2.2.2
    dsimp [g] at hgX ⊢
    omega
  have hgap (i : Fin r) : directedGap X Q i =
      (g : ℤ) * (2 : ℤ) ^ gapExponent r u i.val := by
    have he := hwalk (gapExponent r u i.val) (ZMod.val_lt _)
      (show period X Q - 1 < period X Q by omega)
    rw [shift_gap_location hrp s i hunit] at he
    rw [hdg] at he
    simpa only [mul_comm] using he
  let a := sortedPoint X Q
  let z : Fin r := ⟨0, hrp⟩
  let w : Fin r := ⟨r - 1, by omega⟩
  have hpre (j : ℕ) (hj : j < r) :
      (a ⟨j, hj⟩ : ℤ) = (a z : ℤ) +
        (g : ℤ) * ∑ i ∈ Finset.range j, (2 : ℤ) ^ gapExponent r u i := by
    induction j with
    | zero => simp [z]
    | succ j ih =>
      have hj' : j < r := by omega
      have he := hgap (⟨j, hj'⟩ : Fin r)
      have hn : cycAdd (⟨j, hj'⟩ : Fin r) 1 = ⟨j + 1, hj⟩ := by
        apply Fin.ext
        exact Nat.mod_eq_of_lt hj
      change (a (cycAdd ⟨j, hj'⟩ 1) : ℤ) - a ⟨j, hj'⟩ +
        (if j + 1 < r then 0 else (X : ℤ)) = _ at he
      rw [hn, ite_eq_left hj, add_zero] at he
      rw [Finset.sum_range_succ, mul_add]
      linarith [ih hj']
  have hs0 := hs z
  change a (cycAdd s 0) = (2 * a z) % X at hs0
  rw [cycAdd_zero] at hs0
  have hmin : a z ≤ a s := a.monotone (by change 0 ≤ s.val; omega)
  have hazX : a z < X := orbit_lt hXp Q _
    ((orbit X Q).orderEmbOfFin_mem (orbit_card X Q) z)
  have hnowrap : 2 * a z < X := by
    by_contra hn
    have hle : X ≤ 2 * a z := by omega
    have hlt : 2 * a z - X < X := by omega
    have hm : (2 * a z) % X = 2 * a z - X := by
      rw [Nat.mod_eq_sub_mod hle, Nat.mod_eq_of_lt hlt]
    rw [hm] at hs0
    omega
  rw [Nat.mod_eq_of_lt hnowrap] at hs0
  have hs0Z : (a s : ℤ) = 2 * (a z : ℤ) := by exact_mod_cast hs0
  have hbase : (a z : ℤ) =
      (g : ℤ) * ∑ i ∈ Finset.range s.val, (2 : ℤ) ^ gapExponent r u i := by
    have he := hpre s.val s.isLt
    linarith
  have hpoint (j : Fin r) : a j = g * explicitPoint r s.val u j.val := by
    have he := hpre j.val j.isLt
    rw [hbase, ← mul_add] at he
    have he' : (a j : ℤ) = ((g * explicitPoint r s.val u j.val : ℕ) : ℤ) := by
      simpa only [explicitPoint, Nat.cast_mul, Nat.cast_add, Nat.cast_sum,
        Nat.cast_pow, Nat.cast_ofNat] using he
    exact_mod_cast he'
  have hse : gapExponent r u (s.val - 1) = 0 := by
    have he : (((s.val - 1 : ℕ) : ZMod r) + 1) = (s.val : ZMod r) := by
      simpa only [Nat.cast_add, Nat.cast_one] using
        congrArg (fun n : ℕ => (n : ZMod r))
          (Nat.sub_add_cancel (by omega : 1 ≤ s.val))
    unfold gapExponent
    rw [he, mul_comm (u : ZMod r) (s.val : ZMod r), hunit, sub_self, ZMod.val_zero]
  have hsum : (∑ i ∈ Finset.range s.val, (2 : ℤ) ^ gapExponent r u i) =
      (∑ i ∈ Finset.range (s.val - 1), (2 : ℤ) ^ gapExponent r u i) + 1 := by
    conv_lhs => rw [← Nat.sub_add_cancel (by omega : 1 ≤ s.val)]
    rw [Finset.sum_range_succ, hse, pow_zero]
  have hne := orbit_nonempty hXp hodd Q
  have hz : a z = (orbit X Q).min' hne :=
    Finset.orderEmbOfFin_zero (orbit_card X Q) hrp
  have hw : a w = (orbit X Q).max' hne :=
    Finset.orderEmbOfFin_last (orbit_card X Q) hrp
  have hW : (diameter X Q : ℤ) = (a w : ℤ) - a z := by
    have hle : a z ≤ a w := a.monotone (by change 0 ≤ r - 1; omega)
    unfold diameter
    rw [dite_eq_left hne, ← hw, ← hz]
    omega
  have hMcast : ((2 ^ r - 1 : ℕ) : ℤ) = (2 : ℤ) ^ r - 1 := by
    have hp : 0 < (2 : ℕ) ^ r := pow_pos (by omega) r
    rw [Nat.cast_sub (by omega : 1 ≤ (2 : ℕ) ^ r)]
    push_cast
    rfl
  change (X : ℤ) = ((2 ^ r - 1 : ℕ) : ℤ) * d at hprod
  rw [hMcast, hdg] at hprod
  have hpow : (2 : ℤ) ^ r = 2 * 2 ^ (r - 1) := by
    calc
      (2 : ℤ) ^ r = 2 ^ (r - 1 + 1) := by congr 1; omega
      _ = _ := by rw [pow_succ]; ring
  have hmaxZ : (a w : ℤ) = (g : ℤ) *
      ((2 : ℤ) ^ (r - 1) +
        ∑ i ∈ Finset.range (s.val - 1), (2 : ℤ) ^ gapExponent r u i) := by
    rw [hsum] at hbase
    rw [hdg] at hdiam
    rw [hpow] at hprod
    nlinarith
  have hmax : a w = g * explicitNumerator r s.val u := by
    exact_mod_cast (show (a w : ℤ) =
      ((g * explicitNumerator r s.val u : ℕ) : ℤ) by
        simpa only [explicitNumerator, Nat.cast_mul, Nat.cast_add,
          Nat.cast_pow, Nat.cast_ofNat, Nat.cast_sum] using hmaxZ)
  refine ⟨s.val, u, hspos, s.isLt, hcop, hu, hunit, ?_, ?_⟩
  · ext b
    constructor
    · intro hb
      obtain ⟨j, hj⟩ := ((orbit X Q).orderIsoOfFin (orbit_card X Q)).surjective ⟨b, hb⟩
      have he : a j = b := congrArg Subtype.val hj
      exact Finset.mem_image.mpr ⟨j.val, Finset.mem_range.mpr j.isLt,
        (hpoint j).symm.trans he⟩
    · intro hb
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hb
      rw [← hpoint (⟨j, Finset.mem_range.mp hj⟩ : Fin r)]
      exact (orbit X Q).orderEmbOfFin_mem (orbit_card X Q) _
  · rw [← hmax, hw]
    exact ⟨(orbit X Q).max'_mem hne, fun b hb => Finset.le_max' _ b hb⟩

/-- Construction from the explicit arithmetic gaps, with no orbit assumptions. -/
private theorem explicit_point_geometry {r s u : ℕ} (hr : 2 ≤ r)
    (hs : 0 < s) (hsr : s < r) (hu : (s : ZMod r) * u = 1) :
    (∀ j < r, 0 < explicitPoint r s u j ∧ explicitPoint r s u j < 2 ^ r - 1) ∧
    StrictMono (fun j : Fin r => explicitPoint r s u j.val) ∧
    explicitPoint r s u (r - 1) = explicitNumerator r s u ∧
    (∀ i : Fin r, explicitPoint r s u (cycAdd ⟨s, hsr⟩ i.val).val =
      (2 * explicitPoint r s u i.val) % (2 ^ r - 1)) ∧
    explicitPoint r s u (r - 1) = explicitPoint r s u 0 + (2 ^ (r - 1) - 1) ∧
    explicitPoint r s u s = explicitPoint r s u (s - 1) + 1 := by
  classical
  letI : NeZero r := ⟨by omega⟩
  let M := 2 ^ r - 1
  let h := 2 ^ (r - 1)
  let delta : ℕ → ℕ := fun i => 2 ^ gapExponent r u i
  let P : ℕ → ℕ := fun n => ∑ i ∈ Finset.range n, delta i
  let a : Fin r → ℕ := fun i => P s + P i.val
  let z : Fin r := ⟨0, by omega⟩
  let w : Fin r := ⟨r - 1, by omega⟩
  let shift : Fin r → Fin r := fun i => cycAdd ⟨s, hsr⟩ i.val
  have hexp (i : ℕ) : (gapExponent r u i : ZMod r) =
      (u : ZMod r) * ((i : ZMod r) + 1) - 1 := ZMod.natCast_zmod_val _
  have hlt (i : ℕ) : gapExponent r u i < r := ZMod.val_lt _
  have hinverse (i : Fin r) :
      (s : ZMod r) * ((gapExponent r u i.val : ZMod r) + 1) - 1 = i.val := by
    rw [hexp]
    calc
      (s : ZMod r) * ((u : ZMod r) * ((i.val : ZMod r) + 1) - 1 + 1) - 1 =
          ((s : ZMod r) * u) * ((i.val : ZMod r) + 1) - 1 := by ring
      _ = (i.val : ZMod r) := by rw [hu]; ring
  let E : Fin r → Fin r := fun i => ⟨gapExponent r u i.val, hlt i.val⟩
  have hEinj : Function.Injective E := by
    intro i j he
    have hc := congrArg (fun k : Fin r =>
      (s : ZMod r) * ((k.val : ZMod r) + 1) - 1) he
    change (s : ZMod r) * ((gapExponent r u i.val : ZMod r) + 1) - 1 =
      (s : ZMod r) * ((gapExponent r u j.val : ZMod r) + 1) - 1 at hc
    rw [hinverse, hinverse] at hc
    apply Fin.ext
    exact ((ZMod.natCast_eq_natCast_iff _ _ _).mp hc).eq_of_lt_of_lt i.isLt j.isLt
  let e := Equiv.ofBijective E ⟨hEinj, Finite.surjective_of_injective hEinj⟩
  have hsum : P r = ∑ i ∈ Finset.range r, 2 ^ i := by
    have he := Equiv.sum_comp e (fun j : Fin r => (2 : ℕ) ^ j.val)
    change (∑ i : Fin r, (2 : ℕ) ^ gapExponent r u i.val) =
      (∑ i : Fin r, (2 : ℕ) ^ i.val) at he
    calc
      P r = ∑ i : Fin r, (2 : ℕ) ^ gapExponent r u i.val := Finset.sum_range _
      _ = ∑ i : Fin r, (2 : ℕ) ^ i.val := he
      _ = ∑ i ∈ Finset.range r, (2 : ℕ) ^ i := (Finset.sum_range _).symm
  have htotal : P r = M := by
    have he : (∑ i ∈ Finset.range r, (2 : ℕ) ^ i) + 1 = 2 ^ r := by
      simpa using geom_sum_mul_add (1 : ℕ) r
    dsimp [M]
    omega
  have hpow : 2 ^ r = 2 * h := by
    dsimp [h]
    calc
      (2 : ℕ) ^ r = 2 ^ (r - 1 + 1) := by congr 1; omega
      _ = _ := by rw [pow_succ]; ring
  have hhp : 0 < h := pow_pos (by omega) _
  have hMp : 0 < M := by dsimp [M]; omega
  letI : NeZero M := ⟨hMp.ne'⟩
  have hwcast : ((r - 1 : ℕ) : ZMod r) = -1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ r), ZMod.natCast_self, Nat.cast_one]
    ring
  have helast : gapExponent r u (r - 1) = r - 1 := by
    have hc : (gapExponent r u (r - 1) : ZMod r) = ((r - 1 : ℕ) : ZMod r) := by
      rw [hexp, hwcast]
      ring
    exact ((ZMod.natCast_eq_natCast_iff _ _ _).mp hc).eq_of_lt_of_lt
      (hlt _) (by omega)
  have hdeltaLast : delta (r - 1) = h := by dsimp [delta, h]; rw [helast]
  have hse : gapExponent r u (s - 1) = 0 := by
    have he : (((s - 1 : ℕ) : ZMod r) + 1) = (s : ZMod r) := by
      simpa only [Nat.cast_add, Nat.cast_one] using
        congrArg (fun n : ℕ => (n : ZMod r)) (Nat.sub_add_cancel (by omega : 1 ≤ s))
    unfold gapExponent
    rw [he, mul_comm (u : ZMod r) (s : ZMod r), hu, sub_self, ZMod.val_zero]
  have hdeltaUnit : delta (s - 1) = 1 := by simp [delta, hse]
  have hPsucc (n : ℕ) : P (n + 1) = P n + delta n := Finset.sum_range_succ _ _
  have hPstrict : StrictMono P := by
    apply strictMono_nat_of_lt_succ
    intro n
    rw [hPsucc]
    have hd : 0 < delta n := pow_pos (by omega) _
    omega
  have hPzero : P 0 = 0 := by simp [P]
  have hPpositive : 0 < P s := by have := hPstrict hs; omega
  have hlastPrefix : P (r - 1) = h - 1 := by
    have he := hPsucc (r - 1)
    rw [Nat.sub_add_cancel (by omega : 1 ≤ r), htotal, hdeltaLast] at he
    dsimp [M] at he
    omega
  have hbaseBound : P s ≤ h - 1 := by
    rw [← hlastPrefix]
    exact hPstrict.monotone (by omega)
  have hbounds (i : Fin r) : 0 < a i ∧ a i < M := by
    have hp : P i.val ≤ P (r - 1) := hPstrict.monotone (by have := i.isLt; omega)
    dsimp [a]
    rw [hlastPrefix] at hp
    dsimp [M]
    omega
  have haStrict : StrictMono a := by
    intro i j hij
    exact Nat.add_lt_add_left (hPstrict hij) _
  have hmax : a w = explicitNumerator r s u := by
    have he := hPsucc (s - 1)
    rw [Nat.sub_add_cancel (by omega : 1 ≤ s), hdeltaUnit] at he
    change P s + P (r - 1) = h + P (s - 1)
    rw [hlastPrefix]
    omega
  have h2r : (2 : ZMod M) ^ r = 1 := by
    have he : 2 ^ r = M + 1 := by dsimp [M]; omega
    have hc := congrArg (fun n : ℕ => (n : ZMod M)) he
    simpa only [Nat.cast_pow, Nat.cast_ofNat, Nat.cast_add,
      ZMod.natCast_self, Nat.cast_one, zero_add] using hc
  have hshiftExp (i : Fin r) : gapExponent r u (shift i).val =
      (gapExponent r u i.val + 1) % r := by
    have hi : ((shift i).val : ZMod r) = (s : ZMod r) + i.val := by
      change (((s + i.val) % r : ℕ) : ZMod r) = _
      rw [ZMod.natCast_mod, Nat.cast_add]
    have hc : (gapExponent r u (shift i).val : ZMod r) =
        ((gapExponent r u i.val + 1 : ℕ) : ZMod r) := by
      rw [hexp, hi, Nat.cast_add, Nat.cast_one, hexp]
      have hus : (u : ZMod r) * s = 1 := by rw [mul_comm, hu]
      calc
        (u : ZMod r) * ((s : ZMod r) + i.val + 1) - 1 =
            (u : ZMod r) * s + (u : ZMod r) * ((i.val : ZMod r) + 1) - 1 := by ring
        _ = _ := by rw [hus]; ring
    have hv := congrArg ZMod.val hc
    simpa only [ZMod.val_natCast, Nat.mod_eq_of_lt (hlt _)] using hv
  have hdeltaShift (i : Fin r) : (delta (shift i).val : ZMod M) =
      2 * (delta i.val : ZMod M) := by
    dsimp [delta]
    push_cast
    rw [hshiftExp]
    by_cases he : gapExponent r u i.val + 1 < r
    · rw [Nat.mod_eq_of_lt he, pow_succ]; ring
    · have heq : gapExponent r u i.val + 1 = r := by have := hlt i.val; omega
      rw [heq, Nat.mod_self, pow_zero]
      calc
        (1 : ZMod M) = 2 ^ r := h2r.symm
        _ = 2 ^ (gapExponent r u i.val + 1) := by rw [heq]
        _ = _ := by rw [pow_succ]; ring
  have hgap (i : Fin r) : (a (cycAdd i 1) : ZMod M) - a i = delta i.val := by
    by_cases hi : i.val + 1 < r
    · have hn : (cycAdd i 1).val = i.val + 1 := Nat.mod_eq_of_lt hi
      dsimp [a]
      rw [hn, hPsucc]
      push_cast
      ring
    · have hiw : i = w := by apply Fin.ext; dsimp [w]; have := i.isLt; omega
      subst i
      have hn : cycAdd w 1 = z := by
        apply Fin.ext
        change (r - 1 + 1) % r = 0
        rw [Nat.sub_add_cancel (by omega : 1 ≤ r), Nat.mod_self]
      rw [hn]
      have he : P (r - 1) + delta (r - 1) = M := by
        rw [← hPsucc, Nat.sub_add_cancel (by omega : 1 ≤ r), htotal]
      have hc := congrArg (fun n : ℕ => (n : ZMod M)) he
      rw [Nat.cast_add, ZMod.natCast_self] at hc
      change ((P s + P 0 : ℕ) : ZMod M) - ((P s + P (r - 1) : ℕ) : ZMod M) =
        (delta (r - 1) : ZMod M)
      rw [hPzero]
      push_cast
      linear_combination -hc
  let b : Fin r → ZMod M := fun i => 2 * (a i : ZMod M) - a (shift i)
  have hbnext (i : Fin r) : b (cycAdd i 1) = b i := by
    have hc : shift (cycAdd i 1) = cycAdd (shift i) 1 :=
      cycAdd_index_add ⟨s, hsr⟩ i 1
    have h1 := hgap i
    have h2 := hgap (shift i)
    rw [← hc] at h2
    dsimp [b]
    linear_combination 2 * h1 - h2 - hdeltaShift i
  have hbzero : b z = 0 := by
    have hp : shift z = ⟨s, hsr⟩ := cycAdd_zero _
    dsimp [b]
    rw [hp]
    change 2 * ((P s + P 0 : ℕ) : ZMod M) - ((P s + P s : ℕ) : ZMod M) = 0
    rw [hPzero]
    push_cast
    ring
  have hb (n : ℕ) (hn : n < r) : b ⟨n, hn⟩ = 0 := by
    induction n with
    | zero => exact hbzero
    | succ n ih =>
      have hn' : n < r := by omega
      have hc : cycAdd (⟨n, hn'⟩ : Fin r) 1 = ⟨n + 1, hn⟩ := by
        apply Fin.ext
        exact Nat.mod_eq_of_lt hn
      rw [← hc, hbnext]
      exact ih hn'
  have hstep (i : Fin r) : a (shift i) = (2 * a i) % M := by
    have he : (a (shift i) : ZMod M) = ((2 * a i : ℕ) : ZMod M) := by
      have hh := hb i.val i.isLt
      dsimp [b] at hh
      push_cast
      linear_combination -hh
    have hm := (ZMod.natCast_eq_natCast_iff _ _ _).mp he
    simpa only [Nat.ModEq, Nat.mod_eq_of_lt (hbounds (shift i)).2] using hm
  refine ⟨?_, haStrict, hmax, hstep, ?_, ?_⟩
  · intro j hj
    exact hbounds ⟨j, hj⟩
  · change P s + P (r - 1) = P s + P 0 + (h - 1)
    rw [hPzero, hlastPrefix, Nat.add_zero]
  · change P s + P s = P s + P (s - 1) + 1
    have he := hPsucc (s - 1)
    rw [Nat.sub_add_cancel (by omega : 1 ≤ s), hdeltaUnit] at he
    omega

/-- The actual anchored interval, stated without truncated subtraction. -/
def Anchored (X Q : ℕ) : Prop :=
  ∀ n : ℕ, residue X Q n ≤ Q ∧ Q ≤ residue X Q n + (X - 1) / 2

private theorem anchored_narrow_maximum {X Q : ℕ} (hX : 3 ≤ X) (hodd : Odd X)
    (hQX : Q < X) (ha : Anchored X Q) :
    2 * diameter X Q < X ∧ IsGreatest (↑(orbit X Q) : Set ℕ) Q := by
  classical
  have hXp : 0 < X := by omega
  have hne := orbit_nonempty hXp hodd Q
  have hbound (b : ℕ) (hb : b ∈ orbit X Q) :
      b ≤ Q ∧ Q ≤ b + (X - 1) / 2 := by
    obtain ⟨n, _, rfl⟩ := Finset.mem_image.mp hb
    exact ha n
  have hmem : Q ∈ orbit X Q := by
    simpa only [residue_zero hQX] using residue_mem_orbit hXp hodd Q 0
  have hgreat : IsGreatest (↑(orbit X Q) : Set ℕ) Q :=
    ⟨hmem, fun b hb => (hbound b hb).1⟩
  have hmax : (orbit X Q).max' hne = Q :=
    le_antisymm (hbound _ ((orbit X Q).max'_mem hne)).1
      (Finset.le_max' _ Q hmem)
  have hlo := (hbound _ ((orbit X Q).min'_mem hne)).2
  have hdiam : diameter X Q ≤ (X - 1) / 2 := by
    unfold diameter
    rw [dite_eq_left hne, hmax]
    omega
  exact ⟨by omega, hgreat⟩

private theorem explicit_scaled_construction {X Q r s u : ℕ}
    (hX : 3 ≤ X) (hodd : Odd X) (hQ : 0 < Q) (hQX : Q < X)
    (hr : 2 ≤ r) (hs : 0 < s) (hsr : s < r)
    (hu : (s : ZMod r) * u = 1) (hdiv : 2 ^ r - 1 ∣ X)
    (hQeq : Q = (X / (2 ^ r - 1)) * explicitNumerator r s u) :
    Anchored X Q ∧ period X Q = r ∧ Nat.gcd X Q = X / (2 ^ r - 1) := by
  classical
  have hXp : 0 < X := by omega
  let M := 2 ^ r - 1
  let g := X / M
  let h := 2 ^ (r - 1)
  have hMg : M * g = X := Nat.mul_div_cancel' hdiv
  have hg : 0 < g := by
    by_contra hn
    have hz : g = 0 := Nat.eq_zero_of_not_pos hn
    rw [hz, Nat.mul_zero] at hMg
    omega
  have hMp : 0 < M := by
    have hp : 1 < (2 : ℕ) ^ r := one_lt_pow' (by omega) (by omega)
    dsimp [M]
    omega
  letI : NeZero r := ⟨by omega⟩
  let a : Fin r → ℕ := fun i => explicitPoint r s u i.val
  let w : Fin r := ⟨r - 1, by omega⟩
  let z : Fin r := ⟨0, by omega⟩
  let p : Fin r → Fin r := fun i => cycAdd ⟨s, hsr⟩ i.val
  obtain ⟨habounds, hastrict, hamax, hasteps, hawidth, _⟩ :=
    explicit_point_geometry hr hs hsr hu
  have hXg : X = g * M := by rw [← hMg]; ring
  have hmax : Q = g * a w := by simpa only [a, w, g, M, hamax] using hQeq
  have hscale (i : Fin r) : (2 * (g * a i)) % X = g * a (p i) := by
    rw [hXg]
    calc
      (2 * (g * a i)) % (g * M) = (g * (2 * a i)) % (g * M) := by congr 1; ring
      _ = g * ((2 * a i) % M) := Nat.mul_mod_mul_left _ _ _
      _ = g * a (p i) := by rw [← hasteps i]
  have hres (n : ℕ) : residue X Q n = g * a (p^[n] w) := by
    induction n with
    | zero => simpa only [Function.iterate_zero_apply, residue_zero hQX] using hmax
    | succ n ih => rw [residue_succ, ih, hscale, Function.iterate_succ_apply']
  have horbit : orbit X Q = Finset.univ.image (fun i : Fin r => g * a i) := by
    ext b
    constructor
    · intro hb
      obtain ⟨n, _, rfl⟩ := Finset.mem_image.mp hb
      exact Finset.mem_image.mpr ⟨p^[n] w, Finset.mem_univ _, (hres n).symm⟩
    · intro hb
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hb
      have he := hres (gapExponent r u i.val + 1)
      rw [shift_gap_location (by omega : 0 < r) ⟨s, hsr⟩ i hu] at he
      rw [← he]
      exact residue_mem_orbit hXp hodd Q _
  have hinj : Function.Injective (fun i : Fin r => g * a i) := by
    intro i j he
    apply hastrict.injective
    exact mul_left_cancel₀ hg.ne' he
  have hperiod : period X Q = r := by
    rw [← orbit_card, horbit, Finset.card_image_of_injective _ hinj,
      Finset.card_univ, Fintype.card_fin]
  have hMstep : M + 1 = 2 * h := by
    have he : (2 : ℕ) ^ r = 2 * 2 ^ (r - 1) := by
      calc
        (2 : ℕ) ^ r = 2 ^ (r - 1 + 1) := by congr 1; omega
        _ = _ := by rw [pow_succ]; ring
    dsimp [M, h]
    omega
  have hhp : 0 < h := pow_pos (by omega) _
  have hsub : h - 1 + 1 = h := Nat.sub_add_cancel (by omega)
  have hscaled : 2 * (g * (h - 1)) + g = X := by
    nlinarith only [hMg, hMstep, hsub]
  have hhalf : g * (h - 1) ≤ (X - 1) / 2 := by omega
  have ha : Anchored X Q := by
    intro n
    let i := p^[n] w
    have hilo : a z ≤ a i := hastrict.monotone (by change 0 ≤ i.val; omega)
    have hihi : a i ≤ a w := hastrict.monotone
      (by change i.val ≤ r - 1; have := i.isLt; omega)
    have haw : a w = a z + (h - 1) := hawidth
    have hdist : a w ≤ a i + (h - 1) := by omega
    have hgd := Nat.mul_le_mul_left g hdist
    rw [Nat.mul_add] at hgd
    rw [hres, hmax]
    change g * a i ≤ g * a w ∧ g * a w ≤ g * a i + (X - 1) / 2
    exact ⟨Nat.mul_le_mul_left g hihi, by omega⟩
  have hnarrow := (anchored_narrow_maximum hX hodd hQX ha).1
  have hdenom : denominator X Q = M := by
    rw [(narrow_classification hX hodd hQ hQX hnarrow).2.2.1, hperiod]
  have hgcprod : Nat.gcd X Q * M = X := by
    rw [← hdenom]
    exact Nat.mul_div_cancel' (Nat.gcd_dvd_left X Q)
  have hgcd : Nat.gcd X Q = g := by
    apply mul_right_cancel₀ hMp.ne'
    exact hgcprod.trans hXg
  exact ⟨ha, hperiod, hgcd⟩

/-- Exact anchored arithmetic classification. The second conjunct derives
actual period and gcd scale for every arithmetic witness; these are not
replacement assumptions in the converse. -/
theorem anchored_explicit_classification {X Q : ℕ} (hX : 3 ≤ X) (hodd : Odd X)
    (hQ : 0 < Q) (hQX : Q < X) :
    (Anchored X Q ↔ ∃ r s u : ℕ, 2 ≤ r ∧ 0 < s ∧ s < r ∧ Nat.Coprime s r ∧
      u < r ∧ (s : ZMod r) * u = 1 ∧ 2 ^ r - 1 ∣ X ∧
      Q = (X / (2 ^ r - 1)) * explicitNumerator r s u) ∧
    (∀ r s u : ℕ, 2 ≤ r → 0 < s → s < r → Nat.Coprime s r → u < r →
      (s : ZMod r) * u = 1 → 2 ^ r - 1 ∣ X →
      Q = (X / (2 ^ r - 1)) * explicitNumerator r s u →
      period X Q = r ∧ Nat.gcd X Q = X / (2 ^ r - 1)) := by
  constructor
  · constructor
    · intro ha
      obtain ⟨hn, hg⟩ := anchored_narrow_maximum hX hodd hQX ha
      have hc := narrow_classification hX hodd hQ hQX hn
      obtain ⟨s, u, hs, hsr, hcop, hu, hunit, _, hgreat⟩ :=
        narrow_explicit_numerator hX hodd hQ hQX hn
      have heq : Q = Nat.gcd X Q * explicitNumerator (period X Q) s u :=
        le_antisymm (hgreat.2 hg.1) (hg.2 hgreat.1)
      have hprod : Nat.gcd X Q * (2 ^ period X Q - 1) = X := by
        rw [← hc.2.2.1]
        exact Nat.mul_div_cancel' (Nat.gcd_dvd_left X Q)
      have hdiv : 2 ^ period X Q - 1 ∣ X := by
        exact ⟨Nat.gcd X Q, hprod.symm.trans (Nat.mul_comm _ _)⟩
      have hMp : 0 < 2 ^ period X Q - 1 := by
        have hp : 1 < (2 : ℕ) ^ period X Q := one_lt_pow' (by omega) (by omega)
        omega
      have hscale : X / (2 ^ period X Q - 1) = Nat.gcd X Q := by
        calc
          X / (2 ^ period X Q - 1) =
              (Nat.gcd X Q * (2 ^ period X Q - 1)) / (2 ^ period X Q - 1) :=
            congrArg (fun n => n / (2 ^ period X Q - 1)) hprod.symm
          _ = _ := Nat.mul_div_cancel _ hMp
      refine ⟨period X Q, s, u, hc.1, hs, hsr, hcop, hu, hunit, hdiv, ?_⟩
      rw [hscale]
      exact heq
    · rintro ⟨r, s, u, hr, hs, hsr, _, _, hu, hdiv, heq⟩
      exact (explicit_scaled_construction hX hodd hQ hQX hr hs hsr hu hdiv heq).1
  · intro r s u hr hs hsr _ _ hu hdiv heq
    exact (explicit_scaled_construction hX hodd hQ hQX hr hs hsr hu hdiv heq).2

/-- Finite-horizon reduction: one consecutive block of
the actual period forces the entire fixed-Q orbit to be narrow and doubling
to be a transitive cyclic shift of its sorted points, with no early return.
The classification consumer is stated separately below. -/
theorem fixedQ_block_forces_narrow {X Q : ℕ} (hX : 3 ≤ X) (hodd : Odd X)
    (hQ : (X : ℤ) + 1 ≤ 2 * (Q : ℤ)) (hQX : Q < X)
    (k m₀ : ℕ) (H : ℕ → ℤ)
    (hblock : HeightBlock X Q k m₀ (period X Q) H) :
    2 ≤ period X Q ∧
    period X Q = orderOf (2 : ZMod (denominator X Q)) ∧
    (∀ n : ℕ, 1 ≤ residue X Q n ∧
      Q - (X - 1) / 2 ≤ residue X Q n ∧ residue X Q n ≤ Q) ∧
    (∀ z ∈ orbit X Q, z ≤ Q) ∧ Q ∈ orbit X Q ∧
    2 * diameter X Q < X ∧
    ∃ s : Fin (period X Q),
      (∀ i : Fin (period X Q),
        (orbit X Q).orderEmbOfFin (orbit_card X Q) (cycAdd s i.val) =
          (2 * (orbit X Q).orderEmbOfFin (orbit_card X Q) i) % X) ∧
      (∀ i j : Fin (period X Q), ∃ n < period X Q,
        (fun v : Fin (period X Q) => cycAdd s v.val)^[n] i = j) ∧
      (∀ i : Fin (period X Q),
        (fun v : Fin (period X Q) => cycAdd s v.val)^[period X Q] i = i) ∧
      (∀ (i : Fin (period X Q)) (n : ℕ), 0 < n → n < period X Q →
        (fun v : Fin (period X Q) => cycAdd s v.val)^[n] i ≠ i) := by
  obtain ⟨hr, hord, hall, hmax, hmem, hnarrow⟩ :=
    block_narrow_data hX hodd hQ hQX k m₀ H hblock
  have hQp : 0 < Q := by
    have : (0 : ℤ) < Q := by omega
    exact_mod_cast this
  exact ⟨hr, hord, hall, hmax, hmem, hnarrow,
    narrow_doubling_sorted_cycle hX hodd hQp hQX hnarrow⟩

/-- A nontrivial Mersenne divisor produces SOME abstract narrow orbit of
exactly the specified least period. Q is chosen here; the assertion is not
a sufficient criterion for a prescribed Q, and has no physical conclusion. -/
theorem exists_narrow_of_mersenne_dvd {X t : ℕ} (hX : 3 ≤ X) (hodd : Odd X)
    (ht : 2 ≤ t) (hdiv : 2 ^ t - 1 ∣ X) :
    ∃ Q : ℕ, 0 < Q ∧ Q < X ∧ period X Q = t ∧
      (orbit X Q).card = t ∧ 2 * diameter X Q = X - Q ∧
      2 * diameter X Q < X := by
  let M : ℕ := 2 ^ t - 1
  let g : ℕ := X / M
  have hpow : 4 ≤ 2 ^ t := by
    simpa using pow_le_pow_right' (by omega : 1 ≤ (2 : ℕ)) ht
  have hM : 3 ≤ M := by dsimp [M]; omega
  have hMg : M * g = X := Nat.mul_div_cancel' hdiv
  have hg : 0 < g := by
    apply Nat.pos_of_ne_zero
    intro hzero
    have he := hMg
    rw [hzero, mul_zero] at he
    omega
  have hgX : g < X := by
    calc
      g = 1 * g := by omega
      _ < M * g := Nat.mul_lt_mul_of_pos_right (by omega : 1 < M) hg
      _ = X := hMg
  have hpred : 2 ≤ 2 ^ (t - 1) := by
    simpa using pow_le_pow_right' (by omega : 1 ≤ (2 : ℕ))
      (show 1 ≤ t - 1 by omega)
  have hpowstep : 2 ^ t = 2 ^ (t - 1) * 2 := by
    rw [← pow_succ]
    congr 1
    omega
  have hpredM : 2 ^ (t - 1) < M := by dsimp [M]; omega
  have hshort (n : ℕ) (hn : n < t) : residue X g n = g * 2 ^ n := by
    have hp := pow_le_pow_right' (by omega : 1 ≤ (2 : ℕ))
      (show n ≤ t - 1 by omega)
    have hlt : g * 2 ^ n < X := by
      calc
        g * 2 ^ n ≤ g * 2 ^ (t - 1) := Nat.mul_le_mul_left g hp
        _ < g * M := Nat.mul_lt_mul_of_pos_left hpredM hg
        _ = X := by simpa only [Nat.mul_comm] using hMg
    unfold residue
    rw [Nat.mul_comm (2 ^ n), Nat.mod_eq_of_lt hlt]
  have hreturn : residue X g t = g := by
    have hprod : 2 ^ t * g = X + g := by
      have he : 2 ^ t = M + 1 := by dsimp [M]; omega
      calc
        2 ^ t * g = (M + 1) * g := congrArg (fun z : ℕ => z * g) he
        _ = M * g + g := by ring
        _ = X + g := by rw [hMg]
    simp only [residue, hprod, Nat.add_mod, Nat.mod_self, zero_add,
      Nat.mod_eq_of_lt hgX]
  have hrp := period_pos (by omega : 0 < X) hodd g
  have hret : Function.IsPeriodicPt (fun z : ZMod X => 2 * z) t (g : ZMod X) := by
    apply (periodic_iff_modEq X g t).mpr
    change residue X g t = g % X
    rw [hreturn, Nat.mod_eq_of_lt hgX]
  have hrle : period X g ≤ t := hret.minimalPeriod_le (by omega)
  have hr : period X g = t := by
    by_contra hne
    have hlt : period X g < t := by omega
    have he := residue_return hgX
    rw [hshort _ hlt] at he
    have hp : 1 < 2 ^ period X g :=
      one_lt_pow' (by omega : 1 < (2 : ℕ)) (Nat.ne_of_gt hrp)
    have hgt : g < g * 2 ^ period X g := by
      simpa only [mul_one] using Nat.mul_lt_mul_of_pos_left hp hg
    omega
  have hne := orbit_nonempty (by omega : 0 < X) hodd g
  have hall (z : ℕ) (hz : z ∈ orbit X g) :
      g ≤ z ∧ z ≤ g * 2 ^ (t - 1) := by
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hz
    have hnt : n < t := by simpa only [hr] using Finset.mem_range.mp hn
    rw [hshort n hnt]
    have hp : 0 < 2 ^ n := pow_pos (by omega : 0 < (2 : ℕ)) n
    have hp' := pow_le_pow_right' (by omega : 1 ≤ (2 : ℕ))
      (show n ≤ t - 1 by omega)
    constructor
    · simpa only [mul_one] using
        Nat.mul_le_mul_left g (show 1 ≤ 2 ^ n by omega)
    · exact Nat.mul_le_mul_left g hp'
  have hminmem : g ∈ orbit X g := by
    simpa only [residue_zero hgX] using
      residue_mem_orbit (by omega : 0 < X) hodd g 0
  have hmaxmem : g * 2 ^ (t - 1) ∈ orbit X g := by
    rw [← hshort (t - 1) (by omega)]
    exact residue_mem_orbit (by omega : 0 < X) hodd g (t - 1)
  have hmin : (orbit X g).min' hne = g := by
    apply le_antisymm
    · exact (orbit X g).min'_le g hminmem
    · exact (hall _ ((orbit X g).min'_mem hne)).1
  have hmax : (orbit X g).max' hne = g * 2 ^ (t - 1) := by
    apply le_antisymm
    · exact (hall _ ((orbit X g).max'_mem hne)).2
    · exact (orbit X g).le_max' _ hmaxmem
  have hdiam : 2 * diameter X g = X - g := by
    unfold diameter
    rw [dite_eq_left hne, hmax, hmin]
    have hgp : g ≤ g * 2 ^ (t - 1) := by
      simpa only [mul_one] using
        Nat.mul_le_mul_left g (show 1 ≤ 2 ^ (t - 1) by omega)
    have hsub : g * 2 ^ (t - 1) - g + g = g * 2 ^ (t - 1) :=
      Nat.sub_add_cancel hgp
    have hsubX : X - g + g = X := Nat.sub_add_cancel (by omega)
    have hMstep : M + 1 = 2 * 2 ^ (t - 1) := by dsimp [M]; omega
    have hscaled : 2 * (g * 2 ^ (t - 1)) = X + g := by
      calc
        2 * (g * 2 ^ (t - 1)) = g * (M + 1) := by rw [hMstep]; ring
        _ = M * g + g := by ring
        _ = X + g := by rw [hMg]
    omega
  exact ⟨g, hg, hgX, hr, (orbit_card X g).trans hr, hdiam, by omega⟩

/-- Exactly one consecutive block of the actual period, with one fixed
nonterminal Q and an arbitrary starting layer. Necessary arithmetic only;
there is no physical-realization or prescribed-Q sufficiency claim. -/
theorem fixedQ_block_classification {X Q : ℕ} (hX : 3 ≤ X) (hodd : Odd X)
    (hQ : (X : ℤ) + 1 ≤ 2 * (Q : ℤ)) (hQX : Q < X)
    (k m₀ : ℕ) (H : ℕ → ℤ)
    (hblock : HeightBlock X Q k m₀ (period X Q) H) :
    denominator X Q = 2 ^ period X Q - 1 ∧
      2 * diameter X Q = X - Nat.gcd X Q := by
  obtain ⟨_, _, _, _, _, hnarrow, _⟩ :=
    fixedQ_block_forces_narrow hX hodd hQ hQX k m₀ H hblock
  have hQp : 0 < Q := by
    have : (0 : ℤ) < Q := by omega
    exact_mod_cast this
  obtain ⟨_, _, hD, hdiam⟩ := narrow_classification hX hodd hQp hQX hnarrow
  exact ⟨hD, hdiam⟩

/-- Abstract existence, with Q existentially chosen. This does not assert
that a prescribed Q works, or that an abstract orbit is physically realized. -/
theorem exists_narrow_period_iff_mersenne_dvd {X t : ℕ}
    (hX : 3 ≤ X) (hodd : Odd X) (ht : 2 ≤ t) :
    (∃ Q : ℕ, 0 < Q ∧ Q < X ∧ period X Q = t ∧ 2 * diameter X Q < X) ↔
      2 ^ t - 1 ∣ X := by
  constructor
  · rintro ⟨Q, hQ, hQX, hr, hnarrow⟩
    obtain ⟨_, _, hD, _⟩ := narrow_classification hX hodd hQ hQX hnarrow
    rw [← hr, ← hD]
    exact ⟨Nat.gcd X Q, (Nat.div_mul_cancel (Nat.gcd_dvd_left X Q)).symm⟩
  · intro hdiv
    obtain ⟨Q, hQ, hQX, hr, _, _, hnarrow⟩ :=
      exists_narrow_of_mersenne_dvd hX hodd ht hdiv
    exact ⟨Q, hQ, hQX, hr, hnarrow⟩

/-- Existential version when the period is not prescribed. -/
theorem exists_narrow_iff_mersenne_dvd {X : ℕ} (hX : 3 ≤ X) (hodd : Odd X) :
    (∃ Q : ℕ, 0 < Q ∧ Q < X ∧ 2 * diameter X Q < X) ↔
      ∃ t : ℕ, 2 ≤ t ∧ 2 ^ t - 1 ∣ X := by
  constructor
  · rintro ⟨Q, hQ, hQX, hnarrow⟩
    obtain ⟨hr, _, hD, _⟩ := narrow_classification hX hodd hQ hQX hnarrow
    refine ⟨period X Q, hr, ?_⟩
    rw [← hD]
    exact ⟨Nat.gcd X Q, (Nat.div_mul_cancel (Nat.gcd_dvd_left X Q)).symm⟩
  · rintro ⟨t, ht, hdiv⟩
    obtain ⟨Q, hQ, hQX, _, _, _, hnarrow⟩ :=
      exists_narrow_of_mersenne_dvd hX hodd ht hdiv
    exact ⟨Q, hQ, hQX, hnarrow⟩

end D5.S3.Combinatorics.Circle.NarrowDoublingOrbit
