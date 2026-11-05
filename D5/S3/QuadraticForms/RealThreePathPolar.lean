/- GID: D5/S3/QuadraticForms/RealThreePathPolar
   generality: G
   mirror-B: D5/B/S3/QuadraticForms/RealThreePathPolar
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: An arbitrary-marker three-path relation derives a positive real bilinear polar on the original vector space. -/

module

public import D5.S3.QuadraticForms.ThreeWayPositiveKernel
import all D5.S3.QuadraticForms.ParallelogramConstruction
import all Mathlib.Data.Real.Basic
public import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.Tactic

/-! The scalar parameter and a lower bound recover the real polar without regularity assumptions. -/

public section

noncomputable section

namespace D5.S3.QuadraticForms.RealThreePathPolar

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- The three-path identity reads the same function at every real scalar recipe. -/
def Balance (U : V → V) (q : V → ℝ) : Prop :=
  let Q := fun x => q x - q 0
  ∀ (x y : V) (t : ℝ),
    Q (x + t • y) + Q (x + t • U y) + Q (t • U x + y) =
      2 * Q x + Q y + Q (t • x) + 2 * Q (t • y)

private def evenPart (Q : V → ℝ) (x : V) := (Q x + Q (-x)) / 2
private def oddPart (Q : V → ℝ) (x : V) := (Q x - Q (-x)) / 2

private theorem swap (U : V → V) (q : V → ℝ) (h : Balance U q) :
    let Q := fun x => q x - q 0
    ∀ (x y : V) (t : ℝ), Q (x + t • y) - Q (t • x + y) =
      Q x - Q y - Q (t • x) + Q (t • y) := by
  intro Q x y t
  have h₁ := h x y t
  have h₂ := h y x t
  rw [add_comm y (t • x), add_comm y (t • U x), add_comm (t • U y) x] at h₂
  change Q (x + t • y) + Q (x + t • U y) + Q (t • U x + y) = _ at h₁
  change Q (t • x + y) + Q (t • U x + y) + Q (x + t • U y) = _ at h₂
  linarith

private theorem even_swap (Q : V → ℝ)
    (hs : ∀ (x y : V) (t : ℝ), Q (x + t • y) - Q (t • x + y) =
      Q x - Q y - Q (t • x) + Q (t • y)) :
    ∀ (x y : V) (t : ℝ),
      evenPart Q (x + t • y) - evenPart Q (t • x + y) =
      evenPart Q x - evenPart Q y - evenPart Q (t • x) + evenPart Q (t • y) := by
  intro x y t
  have h₁ := hs x y t
  have h₂ := hs (-x) (-y) t
  simp only [smul_neg, ← neg_add] at h₂
  dsimp [evenPart]
  linarith

private theorem odd_add (Q : V → ℝ)
    (hs : ∀ (x y : V) (t : ℝ), Q (x + t • y) - Q (t • x + y) =
      Q x - Q y - Q (t • x) + Q (t • y)) :
    ∀ x y, oddPart Q (x + y) = oddPart Q x + oddPart Q y := by
  intro x y
  have h := hs x (-y) (-1)
  simp only [neg_one_smul, neg_neg, ← neg_add] at h
  dsimp [oddPart]
  linarith

private theorem even_doubling (E : V → ℝ) (hzero : E 0 = 0)
    (he : ∀ x, E (-x) = E x)
    (hs : ∀ (x y : V) (t : ℝ), E (x + t • y) - E (t • x + y) =
      E x - E y - E (t • x) + E (t • y)) :
    ∀ x, E ((2 : ℝ) • x) = 4 * E x := by
  have hr : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  have hr2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  let r : ℝ := 1 / Real.sqrt 2
  have rr : r * r = 1 / 2 := by dsimp [r]; field_simp; nlinarith [hr2]
  have hh (x : V) : E (r • x) = E x / 2 := by
    have h := hs x (-(r • x)) r
    have hz : r • x + -(r • x) = 0 := add_neg_cancel _
    have hz' : x + r • -(r • x) = (1 / 2 : ℝ) • x := by
      rw [smul_neg, smul_smul, rr]
      module
    rw [hz, hz', he, smul_neg, smul_smul, rr, he, hzero] at h
    linarith
  have hh' (x : V) : E ((1 / 2 : ℝ) • x) = E x / 4 := by
    have h := hh (r • x)
    rw [smul_smul, rr, hh] at h
    linarith
  intro x
  have h := hh' ((2 : ℝ) • x)
  rw [smul_smul] at h
  norm_num at h
  linarith

private theorem even_parallelogram (E : V → ℝ)
    (hd : ∀ x, E ((2 : ℝ) • x) = 4 * E x)
    (hs : ∀ (x y : V) (t : ℝ), E (x + t • y) - E (t • x + y) =
      E x - E y - E (t • x) + E (t • y)) :
    ∀ a b, E (a + b) + E (a - b) = 2 * E a + 2 * E b := by
  have hrec (x h : V) : E (x + (4 : ℝ) • h) - 4 * E (x + h) + 3 * E x = 12 * E h := by
    have p := hs x ((2 : ℝ) • h) 2
    have h4 : E ((4 : ℝ) • h) = 16 * E h := by
      rw [show (4 : ℝ) • h = (2 : ℝ) • ((2 : ℝ) • h) by module, hd, hd]
      ring
    rw [hd h, smul_smul, show (2 : ℝ) * 2 = 4 by norm_num,
      ← smul_add, hd (x + h), hd x, h4] at p
    linarith
  have hsecond (x h : V) : E (x + (2 : ℝ) • h) - 2 * E (x + h) + E x = 2 * E h := by
    have p₀ := hrec x h
    have p₁ := hrec (x + h) h
    have p₄ := hrec (x + (4 : ℝ) • h) h
    have p₂ := hrec x ((2 : ℝ) • h)
    rw [hd h] at p₂
    have e₁ : x + h + (4 : ℝ) • h = x + (5 : ℝ) • h := by module
    have e₂ : x + h + h = x + (2 : ℝ) • h := by module
    have e₄ : x + (4 : ℝ) • h + (4 : ℝ) • h = x + (8 : ℝ) • h := by module
    have e₅ : x + (4 : ℝ) • h + h = x + (5 : ℝ) • h := by module
    rw [e₁, e₂] at p₁
    rw [e₄, e₅] at p₄
    rw [smul_smul, show (4 : ℝ) * 2 = 8 by norm_num] at p₂
    linarith
  intro a b
  have h := hsecond (a - b) b
  rw [show a - b + (2 : ℝ) • b = a + b by module,
    sub_add_cancel] at h
  linarith


private theorem even_quadratic (Q : V → ℝ) (hz : Q 0 = 0)
    (hs : ∀ (x y : V) (t : ℝ), Q (x + t • y) - Q (t • x + y) =
      Q x - Q y - Q (t • x) + Q (t • y)) :
    ∃ E : QuadraticMap ℤ V ℝ, ∀ x, E x = evenPart Q x := by
  have he (x : V) : evenPart Q (-x) = evenPart Q x := by simp [evenPart]; ring
  have hez : evenPart Q 0 = 0 := by simp [evenPart, hz]
  have hd := even_doubling (evenPart Q) hez he (even_swap Q hs)
  have hp := even_parallelogram (evenPart Q) hd (even_swap Q hs)
  let E : QuadraticMap ℤ V ℝ := TauCeti.QuadraticMap.ofParallelogram (f := evenPart Q)
    (smul_right_injective ℝ (by norm_num : (2 : ℕ) ≠ 0))
    (by intro x y; simpa only [two_nsmul, two_mul] using hp x y)
  exact ⟨E, fun _ => rfl⟩

omit [Module ℝ V] in
private theorem quadratic_nonneg (E : QuadraticMap ℤ V ℝ) (c : ℝ)
    (hb : ∀ x, -c ≤ E x) : ∀ x, 0 ≤ E x := by
  intro x
  by_contra hn
  have he : E x < 0 := lt_of_not_ge hn
  obtain ⟨n, hn⟩ := exists_nat_gt (max 1 (c / (-E x)))
  have hn1 : (1 : ℝ) < n := (le_max_left _ _).trans_lt hn
  have hnc : c < (n : ℝ) * (-E x) :=
    (div_lt_iff₀ (neg_pos.mpr he)).mp ((le_max_right _ _).trans_lt hn)
  have hsq : (n : ℝ) ≤ (n : ℝ)^2 := by nlinarith
  have hm := mul_le_mul_of_nonneg_right hsq (neg_nonneg.mpr he.le)
  have h := hb ((n : ℤ) • x)
  rw [E.map_smul] at h
  simp only [zsmul_eq_mul, Int.cast_mul, Int.cast_natCast] at h
  nlinarith

private theorem bounded_integer_linear_zero (a c : ℝ)
    (h : ∀ n : ℤ, -c ≤ (n : ℝ) * a) : a = 0 := by
  by_contra ha
  rcases lt_or_gt_of_ne ha with hn | hp
  · obtain ⟨n, hn'⟩ := exists_int_gt (-c / a)
    have hm := mul_lt_mul_of_neg_right hn' hn
    rw [div_mul_cancel₀ _ ha] at hm
    linarith [h n]
  · obtain ⟨n, hn'⟩ := exists_int_lt (-c / a)
    have hm := mul_lt_mul_of_pos_right hn' hp
    rw [div_mul_cancel₀ _ ha] at hm
    linarith [h n]

private theorem positive_additive_scalar (f : ℝ →+ ℝ)
    (hp : ∀ t, 0 ≤ t → 0 ≤ f t) : ∀ t, f t = t * f 1 := by
  have hm : Monotone f := (monotone_iff_map_nonneg f).mpr hp
  have hc : 0 ≤ f 1 := hp 1 (by norm_num)
  have hr (r : ℚ) : f (r : ℝ) = (r : ℝ) * f 1 := by
    simpa using map_ratCast_smul f ℝ ℝ r (1 : ℝ)
  intro t
  apply le_antisymm
  · apply le_of_forall_pos_le_add
    intro ε hε
    have hd : 0 < f 1 + 1 := by linarith
    obtain ⟨r, htr, hrt⟩ := exists_rat_btwn
      (lt_add_of_pos_right t (div_pos hε hd))
    have h := hm htr.le
    rw [hr] at h
    have he := (lt_div_iff₀ hd).mp
      (show (r : ℝ) - t < ε / (f 1 + 1) by linarith)
    nlinarith
  · apply le_of_forall_pos_le_add
    intro ε hε
    have hd : 0 < f 1 + 1 := by linarith
    obtain ⟨r, htr, hrt⟩ := exists_rat_btwn (sub_lt_self t (div_pos hε hd))
    have h := hm hrt.le
    rw [hr] at h
    have he := (lt_div_iff₀ hd).mp
      (show t - (r : ℝ) < ε / (f 1 + 1) by linarith)
    nlinarith

private theorem real_polar (E : QuadraticMap ℤ V ℝ)
    (hp : ∀ x, 0 ≤ E x)
    (hs : ∀ (x y : V) (t : ℝ), E (x + t • y) - E (t • x + y) =
      E x - E y - E (t • x) + E (t • y)) :
    ∃ B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ,
      (∀ x y, B x y = (E (x + y) - E x - E y) / 2) ∧
      (∀ x y, B x y = B y x) ∧ (∀ x, B x x = E x) := by
  let b : V →ₗ[ℤ] V →ₗ[ℤ] ℝ := (1 / 2 : ℝ) • E.polarBilin
  have hb (x y : V) : b x y = (E (x + y) - E x - E y) / 2 := by
    change (1 / 2 : ℝ) * (E (x + y) - E x - E y) = _
    ring
  have hsym (x y : V) : b x y = b y x := by rw [hb, hb, add_comm x y]; ring
  have hdiag (x : V) : b x x = E x := by
    change (1 / 2 : ℝ) * E.polarBilin x x = _
    rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_self]
    simp
  have hbal (x y : V) (t : ℝ) : b x (t • y) = b (t • x) y := by
    rw [hb, hb]
    linarith [hs x y t]
  have hscalar_diag (x : V) (t : ℝ) : b (t • x) x = t * b x x := by
    let a : ℝ →+ ℝ := AddMonoidHom.mk' (fun t => b (t • x) x) (by
      intro s t; simp [add_smul, map_add])
    have ha (t : ℝ) (ht : 0 ≤ t) : 0 ≤ a t := by
      have he : b (t • x) x = b ((Real.sqrt t) • x) ((Real.sqrt t) • x) := by
        rw [hbal, smul_smul, ← pow_two, Real.sq_sqrt ht]
      change 0 ≤ b (t • x) x
      rw [he, hdiag]
      exact hp _
    simpa [a] using positive_additive_scalar a ha t
  have hscalar (t : ℝ) (x y : V) : b (t • x) y = t * b x y := by
    have h := hscalar_diag (x + y) t
    simp only [smul_add, map_add, LinearMap.add_apply] at h
    rw [hscalar_diag x t, hscalar_diag y t] at h
    have he : b (t • y) x = b (t • x) y := by rw [hsym, hbal]
    rw [he, hsym y x] at h
    linarith
  let B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ :=
    { toFun := fun x =>
        { toFun := b x
          map_add' := (b x).map_add
          map_smul' := fun t y => by
            change b x (t • y) = t * b x y
            rw [hbal, hscalar] }
      map_add' := fun x y => by ext z; exact congrArg (fun f => f z) (b.map_add x y)
      map_smul' := fun t x => by ext y; exact hscalar t x y }
  exact ⟨B, hb, hsym, hdiag⟩


private theorem polar_null (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (hs : ∀ x y, B x y = B y x) (hp : ∀ x, 0 ≤ B x x)
    (x : V) (hx : B x x = 0) : ∀ y, B x y = 0 := by
  intro y
  by_contra hxy
  let t := -(B y y + 1) / (2 * B x y)
  have ht : 2 * t * B x y = -(B y y + 1) := by
    dsimp [t]
    field_simp
  have h := hp (y + t • x)
  simp only [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply,
    smul_eq_mul, hx, hs y x] at h
  nlinarith

private theorem raw_even_data (U : V → V) (q : V → ℝ)
    (hq : ∀ x, 0 ≤ q x) (h : Balance U q) :
    ∃ (E : QuadraticMap ℤ V ℝ) (A : V →+ ℝ) (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ),
      (∀ x, q x = q 0 + E x + A x) ∧
      (∀ x y, B x y = (E (x + y) - E x - E y) / 2) ∧
      (∀ x y, B x y = B y x) ∧ (∀ x, B x x = E x) ∧
      (∀ x, 0 ≤ E x) ∧ (∀ x, E x = 0 → A x = 0) := by
  let Q := fun x => q x - q 0
  have hz : Q 0 = 0 := sub_self _
  have hs := swap U q h
  change ∀ (x y : V) (t : ℝ), Q (x + t • y) - Q (t • x + y) =
    Q x - Q y - Q (t • x) + Q (t • y) at hs
  obtain ⟨E, hE⟩ := even_quadratic Q hz hs
  let A : V →+ ℝ := AddMonoidHom.mk' (oddPart Q) (odd_add Q hs)
  have hdec (x : V) : q x = q 0 + E x + A x := by
    rw [hE]; change q x = q 0 + evenPart Q x + oddPart Q x
    dsimp [evenPart, oddPart, Q]
    ring
  have hp : ∀ x, 0 ≤ E x := quadratic_nonneg E (q 0) (by
    intro x; rw [hE]; dsimp [evenPart, Q]; linarith [hq x, hq (-x)])
  obtain ⟨B, hb, hsym, hd⟩ := real_polar E hp (by
    intro x y t
    simp only [hE]
    exact even_swap Q hs x y t)
  refine ⟨E, A, B, hdec, hb, hsym, hd, hp, ?_⟩
  intro x hx
  apply bounded_integer_linear_zero (A x) (q 0)
  intro n
  have hh := hq (n • x)
  rw [hdec, E.map_smul, hx, smul_zero, add_zero, map_zsmul] at hh
  simp only [zsmul_eq_mul] at hh
  linarith

/-- The original finite nonnegative readout has a positive real bilinear polar;
the arbitrary marker preserves its diagonal and satisfies the three-direction relation. -/
theorem raw_real_polar (U : V → V) (q : V → ℝ)
    (hq : ∀ x, 0 ≤ q x) (h : Balance U q) :
    ∃ B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ,
      (∀ x y, B x y = (q (x + y) - q (x - y)) / 4) ∧
      (∀ x y, B x y = B y x) ∧
      (∀ x, q x = q 0 + B x x) ∧ (∀ x, 0 ≤ B x x) ∧
      (∀ x, B (U x) (U x) = B x x) ∧
      (∀ x y, B x y + B x (U y) + B (U x) y = 0) := by
  obtain ⟨E, A, B, hdec, hb, hsym, hd, hp, hnull⟩ := raw_even_data U q hq h
  let Q := fun x => q x - q 0
  have hz : Q 0 = 0 := sub_self _
  have hQ (x : V) : Q x = B x x + A x := by dsimp [Q]; rw [hdec, hd]; ring
  have hn (x : V) (hx : B x x = 0) : ∀ y, B x y = 0 :=
    polar_null B hsym (fun z => by rw [hd]; exact hp z) x hx
  have hzero (t : ℝ) : Q (t • U 0) = 0 := by
    have hh := h 0 0 t
    change Q (0 + t • 0) + Q (0 + t • U 0) + Q (t • U 0 + 0) = _ at hh
    simp only [smul_zero, add_zero, zero_add, hz] at hh
    linarith
  have hpzero : B (U 0) (U 0) = 0 := by
    have h₁ := hzero 1
    have h₂ := hzero (-1)
    simp only [one_smul, neg_one_smul, hQ, map_neg, LinearMap.neg_apply] at h₁ h₂
    linarith
  have htrans (x : V) (t : ℝ) : Q (x + t • U 0) = Q x := by
    have hb0 := hn (U 0) hpzero x
    have hb0' : B x (U 0) = 0 := by rw [hsym]; exact hb0
    have hEt : E (t • U 0) = 0 := by
      rw [← hd]; simp [map_smul, LinearMap.smul_apply, hpzero]
    rw [hQ, hQ, map_add, map_add]
    simp only [LinearMap.add_apply, map_add, map_smul, LinearMap.smul_apply,
      smul_eq_mul, hb0, hb0', hpzero, hnull _ hEt]
    ring
  have hinv (x : V) (t : ℝ) : Q (t • U x) = Q (t • x) := by
    have hh := h x 0 t
    change Q (x + t • 0) + Q (x + t • U 0) + Q (t • U x + 0) = _ at hh
    simp only [smul_zero, add_zero, hz, htrans] at hh
    linarith
  have hEU (x : V) : B (U x) (U x) = B x x := by
    have h₁ := hinv x 1
    have h₂ := hinv x (-1)
    simp only [one_smul, neg_one_smul, hQ, map_neg, LinearMap.neg_apply] at h₁ h₂
    linarith
  have hAU (x : V) : A (U x) = A x := by
    have h₁ := hinv x 1
    simp only [one_smul, hQ, hEU] at h₁
    linarith
  have horient (x y : V) : B x y + B x (U y) + B (U x) y = 0 := by
    have hh := h x y 1
    change Q (x + 1 • y) + Q (x + 1 • U y) + Q (1 • U x + y) =
      2 * Q x + Q y + Q (1 • x) + 2 * Q (1 • y) at hh
    simp only [one_smul, hQ, map_add, LinearMap.add_apply, hEU, hAU] at hh
    rw [hsym y x, hsym (U y) x, hsym y (U x)] at hh
    linarith
  have hBU (x y : V) : B (U x) (U y) = B x y := by
    have hdef (z : V) : ∀ y,
        B (U (x + y) - U x - U y) z = 0 := by
      intro y
      simp only [map_sub, LinearMap.sub_apply]
      have h₁ := horient (x + y) z
      simp only [map_add, LinearMap.add_apply] at h₁
      linarith [horient x z, horient y z]
    have he (y z : V) : B (U (x + y)) z = B (U x) z + B (U y) z := by
      have hh := hdef z y
      simp only [map_sub, LinearMap.sub_apply] at hh
      linarith
    have hdiagU := hEU (x + y)
    rw [he y (U (x + y)), hsym (U x) (U (x + y)),
      hsym (U y) (U (x + y)), he y (U x), he y (U y)] at hdiagU
    simp only [map_add, LinearMap.add_apply, hEU] at hdiagU
    rw [hsym (U y) (U x), hsym y x] at hdiagU
    linarith
  have hcycle (x : V) : B (x + U x + U (U x)) (x + U x + U (U x)) = 0 := by
    have hz (y : V) : B (x + U x + U (U x)) y = 0 := by
      have h₁ := horient x y
      have h₂ := horient (U x) y
      rw [hBU] at h₂
      simp only [map_add, LinearMap.add_apply]
      linarith
    exact hz _
  have hA (x : V) : A x = 0 := by
    have hh := hnull (x + U x + U (U x)) (by rw [← hd]; exact hcycle x)
    simp only [map_add, hAU] at hh
    linarith
  refine ⟨B, ?_, hsym, ?_, (fun x => by rw [hd]; exact hp x), hEU, horient⟩
  · intro x y
    rw [hdec (x + y), hdec (x - y), hA, hA, ← hd, ← hd]
    simp only [map_add, map_sub, LinearMap.add_apply, LinearMap.sub_apply]
    rw [hsym y x]
    ring
  · intro x
    rw [hdec, hA, ← hd]
    ring

end D5.S3.QuadraticForms.RealThreePathPolar
