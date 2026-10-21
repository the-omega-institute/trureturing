/- GID: D5/S1/Dynamics/PeriodicOrbits/OrbitCounting
   generality: G
   mirror-B: D5/B/S1/Dynamics/PeriodicOrbits/OrbitCounting
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual orbit phases yield the fixed-point divisor formula. -/

import D5.S1.Descent.FiniteSelfMapConjugacy
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Data.Fintype.Sigma

/-! # Actual periodic orbits and their phase counts. -/

set_option autoImplicit false

namespace D5.S1.Dynamics.PeriodicOrbits.OrbitCounting

open Function
open D5.S1.Descent.FiniteSelfMapConjugacy (cycleLengthMultiplicity)

variable {X : Type*}

/-- Points of least positive period `n`; period zero is excluded by the theorems. -/
def Stratum (f : X → X) (n : ℕ) := {x : X // minimalPeriod f x = n}

/-- Genuine forward cycles, identified under cyclic change of starting point. -/
def Orbits (f : X → X) (n : ℕ) :=
  Set.range (fun x : Stratum f n => periodicOrbit f x.val)

noncomputable instance [Fintype X] (f : X → X) (n : ℕ) : Fintype (Stratum f n) :=
  by classical exact inferInstanceAs (Fintype {x : X // minimalPeriod f x = n})

instance [Finite X] (f : X → X) (n : ℕ) : Finite (Orbits f n) := by
  unfold Orbits Stratum
  infer_instance

noncomputable instance [Finite X] (f : X → X) (n : ℕ) : Fintype (Orbits f n) :=
  Fintype.ofFinite _

/-- A representative is chosen from the actual range of the periodic-orbit map. -/
noncomputable def representative (f : X → X) (n : ℕ) (o : Orbits f n) : Stratum f n :=
  Classical.choose o.property

/-- Every stratum is the product of its actual cycles and their phases. The equivalence
is required to be given by iteration of a representative, rather than by cardinality alone. -/
theorem orbit_phase_decomposition (f : X → X) {n : ℕ} (hn : 0 < n) :
    ∃ e : (Orbits f n × Fin n) ≃ Stratum f n,
      ∀ o i, (e (o, i)).val = f^[i.val] (representative f n o).val := by
  classical
  have rep (o : Orbits f n) : periodicOrbit f (representative f n o).val = o.val :=
    Classical.choose_spec o.property
  have pos (x : Stratum f n) : x.val ∈ periodicPts f :=
    minimalPeriod_pos_iff_mem_periodicPts.mp (by rw [x.property]; exact hn)
  let phase : Orbits f n × Fin n → Stratum f n := fun p =>
    ⟨f^[p.2.val] (representative f n p.1).val,
      (minimalPeriod_apply_iterate (pos _) _).trans (representative f n p.1).property⟩
  have orbit_phase (p : Orbits f n × Fin n) : periodicOrbit f (phase p).val = p.1.val :=
    (periodicOrbit_apply_iterate_eq (pos _) _).trans (rep _)
  have inj : Injective phase := by
    rintro ⟨o, i⟩ ⟨p, j⟩ he
    have hop : o = p := Subtype.ext ((orbit_phase (o, i)).symm.trans
      ((congrArg (fun x : Stratum f n => periodicOrbit f x.val) he).trans
        (orbit_phase (p, j))))
    subst p
    have hi : i.val < minimalPeriod f (representative f n o).val := by
      rw [(representative f n o).property]; exact i.isLt
    have hj : j.val < minimalPeriod f (representative f n o).val := by
      rw [(representative f n o).property]; exact j.isLt
    have hij := iterate_injOn_Iio_minimalPeriod hi hj (congrArg Subtype.val he)
    exact Prod.ext rfl (Fin.ext hij)
  have surj : Surjective phase := by
    intro x
    let o : Orbits f n := ⟨periodicOrbit f x.val, ⟨x, rfl⟩⟩
    have hx : x.val ∈ periodicOrbit f (representative f n o).val := by
      rw [rep o]; exact self_mem_periodicOrbit (pos x)
    obtain ⟨k, hk⟩ := (mem_periodicOrbit_iff (pos _)).mp hx
    refine ⟨(o, ⟨k % n, Nat.mod_lt _ hn⟩), Subtype.ext ?_⟩
    change f^[k % n] (representative f n o).val = x.val
    have hm := iterate_mod_minimalPeriod_eq (f := f)
      (x := (representative f n o).val) (n := k)
    rw [(representative f n o).property] at hm
    exact hm.trans hk
  exact ⟨Equiv.ofBijective phase ⟨inj, surj⟩, fun _ _ => rfl⟩

/-- The phase decomposition gives an exact multiple, even for a noninjective update. -/
theorem stratum_card (f : X → X) [Fintype X] {n : ℕ} (hn : 0 < n) :
    Fintype.card (Stratum f n) = n * Fintype.card (Orbits f n) := by
  obtain ⟨e, _⟩ := orbit_phase_decomposition f hn
  simpa [Fintype.card_prod, Nat.mul_comm] using (Fintype.card_congr e).symm

/-- The pre-existing division-defined multiplicity counts the actual forward cycles. -/
theorem multiplicity_eq_orbit_card (f : X → X) [Fintype X] {n : ℕ} (hn : 0 < n) :
    cycleLengthMultiplicity f n = Fintype.card (Orbits f n) := by
  classical
  have hc : (Finset.univ.filter fun x => minimalPeriod f x = n).card =
      Fintype.card (Stratum f n) := (Fintype.card_subtype _).symm
  rw [cycleLengthMultiplicity, hc, stratum_card f hn, Nat.mul_div_cancel_left _ hn]

/-- Number of points fixed by the actual `n`th iterate. -/
noncomputable def fixedCount [Fintype X] (f : X → X) (n : ℕ) : ℕ := by
  classical exact (Finset.univ.filter fun x => f^[n] x = x).card

/-- The integer Möbius transform, with no condition on the value at zero. -/
def delta (a : ℕ → ℕ) (n : ℕ) : ℤ :=
  ∑ p ∈ n.divisorsAntidiagonal, (ArithmeticFunction.moebius p.1 : ℤ) * (a p.2 : ℤ)

/-- A fixed point at positive time has one and only one least-period divisor. -/
theorem fixed_count_divisor_sum (f : X → X) [Fintype X] {n : ℕ} (hn : 0 < n) :
    fixedCount f n = ∑ d ∈ n.divisors, d * cycleLengthMultiplicity f d := by
  classical
  let s := Finset.univ.filter fun x : X => f^[n] x = x
  have hpartition : s.card = ∑ d ∈ n.divisors,
      (s.filter fun x => minimalPeriod f x = d).card :=
    Finset.card_eq_sum_card_fiberwise (f := minimalPeriod f) (t := n.divisors) (by
      intro x hx
      exact Nat.mem_divisors.mpr ⟨isPeriodicPt_iff_minimalPeriod_dvd.mp
        (Finset.mem_filter.mp hx).2, hn.ne'⟩)
  change s.card = _
  rw [hpartition]
  apply Finset.sum_congr rfl
  intro d hd
  have hdn := (Nat.mem_divisors.mp hd).1
  have hdpos := Nat.pos_of_mem_divisors hd
  have hfilter : (s.filter fun x => minimalPeriod f x = d) =
      Finset.univ.filter (fun x => minimalPeriod f x = d) := by
    ext x
    simp only [s, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · exact And.right
    · intro hx
      exact ⟨isPeriodicPt_iff_minimalPeriod_dvd.mpr (hx ▸ hdn), hx⟩
  rw [hfilter]
  calc
    _ = Fintype.card (Stratum f d) := (Fintype.card_subtype _).symm
    _ = d * Fintype.card (Orbits f d) := stratum_card f hdpos
    _ = d * cycleLengthMultiplicity f d := by rw [multiplicity_eq_orbit_card f hdpos]

/-- Möbius inversion of actual fixed counts recovers points in genuine cycles. -/
theorem delta_fixed_count (f : X → X) [Fintype X] {n : ℕ} (hn : 0 < n) :
    delta (fixedCount f) n = (n : ℤ) * (cycleLengthMultiplicity f n : ℤ) := by
  apply ((ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq
    (f := fun d => (d : ℤ) * (cycleLengthMultiplicity f d : ℤ))
    (g := fun k => (fixedCount f k : ℤ))).mp ?_) n hn
  intro k hk
  exact_mod_cast (fixed_count_divisor_sum f hk).symm

#print axioms orbit_phase_decomposition
#print axioms stratum_card
#print axioms multiplicity_eq_orbit_card
#print axioms fixed_count_divisor_sum
#print axioms delta_fixed_count

end D5.S1.Dynamics.PeriodicOrbits.OrbitCounting
