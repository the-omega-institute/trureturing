/- GID: D5/S1/Deficit/Beatty/GoldenObserverRoute
   generality: I
   mirror-B: D5/B/S1/Deficit/Beatty/GoldenObserverRoute
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The frozen golden exponent has sqrt-five drift and two golden step sizes. -/

import Mathlib

/- Library-search audit trail (2026-08-30):
   * Searches in `D5` for the copied `beatty`/`beta` definitions together with
     `sqrt 5`, `Int.fract`, Beatty increments, or the corrected two-distance set
     found no declaration of the W-C1 package.
   * Searches in pinned Mathlib found the generic floor and fractional-part laws
     and the exact golden-ratio identities, but no declaration for this observer
     exponent or its two step sizes.
   * The proof below uses `Int.floor_add_fract`, `Int.fract_nonneg`,
     `Int.fract_lt_one`, the floor order interface, and
     `Real.goldenRatio_sq`; the W-C1 conjunction is new assembly over them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Deficit.Beatty.GoldenObserverRoute

/- The next four definitions are transcribed from `D5/X_Frontier/Hearts.lean`.
   This module deliberately does not import that frozen frontier module. -/

/-- The expanding golden eigenvalue. -/
noncomputable def phi : ℝ := (1 + Real.sqrt 5) / 2

/-- The contracting conjugate used by the Beatty/Witt exponent. -/
noncomputable def psi : ℝ := 1 - phi

/-- The canonical Beatty shift `S(v)`. -/
noncomputable def beatty (v : ℕ) : ℤ := ⌊((v : ℝ) + 1) * phi⌋ - 1

/-- The concrete expanding exponent `beta(v) = S(v) - v * psi`. -/
noncomputable def beta (v : ℕ) : ℝ := (beatty v : ℝ) - (v : ℝ) * psi

/-- The bounded fractional remainder in the sqrt-five drift formula. -/
noncomputable def remainder (v : ℕ) : ℝ :=
  (phi - 1) - Int.fract (((v : ℝ) + 1) * phi)

private theorem phi_sq : phi ^ 2 = phi + 1 := by
  change Real.goldenRatio ^ 2 = Real.goldenRatio + 1
  exact Real.goldenRatio_sq

private theorem one_lt_phi : (1 : ℝ) < phi := by
  change (1 : ℝ) < Real.goldenRatio
  exact Real.one_lt_goldenRatio

private theorem phi_lt_two : phi < (2 : ℝ) := by
  change Real.goldenRatio < (2 : ℝ)
  exact Real.goldenRatio_lt_two

private theorem two_mul_phi_sub_one : 2 * phi - 1 = Real.sqrt 5 := by
  rw [phi]
  ring

private theorem beatty_increment (v : ℕ) :
    beatty (v + 1) - beatty v = 1 ∨
      beatty (v + 1) - beatty v = 2 := by
  let x : ℝ := ((v : ℝ) + 1) * phi
  have hxFloor : ((⌊x⌋ : ℤ) : ℝ) ≤ x := Int.floor_le x
  have hxNext : x < ((⌊x⌋ : ℤ) : ℝ) + 1 := Int.lt_floor_add_one x
  have hlowerReal : (((⌊x⌋ + 1 : ℤ) : ℤ) : ℝ) ≤ x + phi := by
    push_cast
    linarith [one_lt_phi]
  have hlower : ⌊x⌋ + 1 ≤ ⌊x + phi⌋ := Int.le_floor.mpr hlowerReal
  have hupperReal : x + phi < (((⌊x⌋ + 3 : ℤ) : ℤ) : ℝ) := by
    push_cast
    linarith [phi_lt_two]
  have hupper : ⌊x + phi⌋ < ⌊x⌋ + 3 := Int.floor_lt.mpr hupperReal
  have hfloor : ⌊x + phi⌋ - ⌊x⌋ = 1 ∨ ⌊x + phi⌋ - ⌊x⌋ = 2 := by
    omega
  have harg : (((v + 1 : ℕ) : ℝ) + 1) * phi = x + phi := by
    simp only [Nat.cast_add, Nat.cast_one]
    dsimp [x]
    ring
  rcases hfloor with hfloor | hfloor
  · left
    rw [beatty, beatty, harg]
    change (⌊x + phi⌋ - 1) - (⌊x⌋ - 1) = 1
    omega
  · right
    rw [beatty, beatty, harg]
    change (⌊x + phi⌋ - 1) - (⌊x⌋ - 1) = 2
    omega

private theorem beta_drift (v : ℕ) :
    beta v = Real.sqrt 5 * (v : ℝ) + remainder v := by
  let x : ℝ := ((v : ℝ) + 1) * phi
  have hfloorFract := Int.floor_add_fract x
  rw [beta, beatty, psi, remainder]
  push_cast
  change ((⌊x⌋ : ℤ) : ℝ) - 1 - (v : ℝ) * (1 - phi) =
    Real.sqrt 5 * (v : ℝ) + (phi - 1 - Int.fract x)
  linear_combination hfloorFract + (v : ℝ) * two_mul_phi_sub_one

private theorem remainder_mem (v : ℕ) :
    remainder v ∈ Set.Ioc (phi - 2) (phi - 1) := by
  rw [Set.mem_Ioc, remainder]
  constructor
  · linarith [Int.fract_lt_one (((v : ℝ) + 1) * phi)]
  · linarith [Int.fract_nonneg (((v : ℝ) + 1) * phi)]

private theorem beta_step (v : ℕ) :
    beta (v + 1) - beta v =
      ((beatty (v + 1) - beatty v : ℤ) : ℝ) - psi := by
  rw [beta, beta]
  push_cast
  ring

private theorem beta_step_mem (v : ℕ) :
    beta (v + 1) - beta v ∈ ({phi, phi ^ 2} : Set ℝ) := by
  rw [Set.mem_insert_iff, Set.mem_singleton_iff]
  rcases beatty_increment v with hincrement | hincrement
  · left
    rw [beta_step, hincrement]
    norm_num [psi]
  · right
    rw [beta_step, hincrement]
    calc
      (2 : ℝ) - (1 - phi) = phi + 1 := by ring
      _ = phi ^ 2 := phi_sq.symm

private theorem beta_step_eq_phi_iff (v : ℕ) :
    beta (v + 1) - beta v = phi ↔
      beatty (v + 1) - beatty v = 1 := by
  rw [beta_step]
  constructor
  · intro h
    have hcast : ((beatty (v + 1) - beatty v : ℤ) : ℝ) = 1 := by
      rw [psi] at h
      linarith
    exact_mod_cast hcast
  · intro h
    rw [h]
    norm_num [psi]

private theorem beta_two_sub_beta_one : beta 2 - beta 1 = phi := by
  have hsqrtSq : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hsqrtNonneg : 0 ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
  have hsqrtLower : (2 : ℝ) < Real.sqrt 5 := by
    nlinarith
  have hsqrtUpper : Real.sqrt 5 < (7 / 3 : ℝ) := by
    nlinarith
  have hfloorTwo : ⌊(2 : ℝ) * phi⌋ = (3 : ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor
    · change (3 : ℝ) ≤ 2 * phi
      rw [phi]
      linarith
    · norm_num
      rw [phi]
      linarith
  have hfloorThree : ⌊(3 : ℝ) * phi⌋ = (4 : ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor
    · change (4 : ℝ) ≤ 3 * phi
      rw [phi]
      linarith
    · norm_num
      rw [phi]
      linarith
  calc
    beta 2 - beta 1 = beta (1 + 1) - beta 1 := by norm_num
    _ = ((beatty (1 + 1) - beatty 1 : ℤ) : ℝ) - psi := beta_step 1
    _ = phi := by norm_num [beatty, hfloorTwo, hfloorThree, psi]

/-- W-C1': the frozen golden observer exponent has exact sqrt-five drift with
an Ioc-bounded fractional remainder, successive gaps `phi` or `phi^2`, and a
gap is `phi` exactly when the Beatty increment is one.  The final conjunct is
the requested numeric anchor at indices one and two. -/
theorem golden_observer_route_w_c1 :
    (∀ v : ℕ,
      beta v = Real.sqrt 5 * (v : ℝ) + remainder v ∧
      remainder v =
        (phi - 1) - Int.fract (((v : ℝ) + 1) * phi) ∧
      remainder v ∈ Set.Ioc (phi - 2) (phi - 1) ∧
      beta (v + 1) - beta v ∈ ({phi, phi ^ 2} : Set ℝ) ∧
      (beta (v + 1) - beta v = phi ↔
        beatty (v + 1) - beatty v = 1)) ∧
      beta 2 - beta 1 = phi := by
  constructor
  · intro v
    exact ⟨beta_drift v, rfl, remainder_mem v, beta_step_mem v,
      beta_step_eq_phi_iff v⟩
  · exact beta_two_sub_beta_one

#print axioms golden_observer_route_w_c1

end D5.S1.Deficit.Beatty.GoldenObserverRoute
