/- GID: D5/S1/Dynamics/Symbolic/KhetanLatticeGeometry
   generality: G
   mirror-B: none(waiver:no mirrored proof)
   mirror-E: none(waiver:no external mirror)
   anchors: []
   utility: none
   digest: Actual lattice-fiber cancellation forces an affine product and transports its given exact cover. -/

import Mathlib
import D5.S1.Dynamics.Symbolic.KhetanProductPeriodicity
import D5.S1.Dynamics.Symbolic.KhetanSectionCancellation

/-! Geometry of the two-direction branch of the six-cell problem.

All points, differences and exponents in this module are integral. In particular,
the incidence keys do not assert that an arbitrary pair of lines meets in the
lattice. Completeness of the occupied incidence relation is a conclusion of the
counting argument, and its witnesses are members of the original tile.

The cancellation input is an explicit sum on each actual occupied fiber. The
supplier from a Laurent line factor to this input is a separate obligation.
Neither unit modulus nor a root-of-unity assumption occurs here.

The incidence proof is double counting on arbitrary finite sets and arbitrary
key types. It does not enumerate finite incidence matrices. The number six is
used in the inequalities for the cardinalities of the occupied key sets.
Consequently no declaration is a certified finite instance, bounded exhaustive
enumeration, checker, or numerical reduction; the utility classification is
`none`.
-/

set_option autoImplicit false

namespace D5.S1.Dynamics.Symbolic.KhetanLatticeGeometry

open scoped BigOperators

open KhetanSectionCancellation

abbrev Lattice := ℤ × ℤ

def det (a b : Lattice) : ℤ := a.1 * b.2 - a.2 * b.1

def Primitive (u : Lattice) : Prop := Int.gcd u.1 u.2 = 1

/-- The Bézout coordinate agrees with the integer parameter on a primitive line. -/
def fiberCoordinate (u z : Lattice) : ℤ :=
  Int.gcdA u.1 u.2 * z.1 + Int.gcdB u.1 u.2 * z.2

def fiber (F : Finset Lattice) (u p : Lattice) : Finset Lattice :=
  F.filter fun q => det u q = det u p

/-- The exponent is relative to an actual occupied base point, with positive
geometric shifts. Reversing the Laurent-mask convention replaces the root by
its inverse and does not change the geometric theorem. -/
def FiberCancellation (F : Finset Lattice) (u : Lattice) (root : ℂ) : Prop :=
  root ≠ 0 ∧ ∀ p ∈ F,
    (fiber F u p).sum (fun q => root ^ fiberCoordinate u (q - p)) = 0

def FullDifferenceSpan (F : Finset Lattice) : Prop :=
  Submodule.span ℤ {z : Lattice | ∃ p ∈ F, ∃ q ∈ F, z = p - q} = ⊤

def frame (a u : Lattice) : Lattice →ₗ[ℤ] Lattice where
  toFun z := z.1 • a + z.2 • u
  map_add' x y := by simp [add_smul]; abel
  map_smul' k z := by ext <;> simp [smul_add] <;> ring

def AffineGrid (F : Finset Lattice) (p a u : Lattice) (b c : ℤ) : Prop :=
  F = (({0, 1} : Finset ℤ).product ({0, b, c} : Finset ℤ)).image
    (fun z => p + frame a u z)

noncomputable def exactCoverCount (F : Finset Lattice) (T : Lattice → Prop)
    (x : Lattice) : ℕ := by
  classical
  exact F.sum fun f => if T (x - f) then 1 else 0

def ExactCover (F : Finset Lattice) (T : Lattice → Prop) : Prop :=
  ∀ x, exactCoverCount F T x = 1

def Period (T : Lattice → Prop) (v : Lattice) : Prop :=
  ∀ x, T (x + v) ↔ T x

noncomputable def indicator (T : Lattice → Prop) (x : Lattice) : ℕ := by
  classical
  exact if T x then 1 else 0

private lemma primitive_parallel (u z : Lattice) (hu : Primitive u)
    (hz : det u z = 0) : z = fiberCoordinate u z • u := by
  have hgcd : Int.gcd u.1 u.2 = 1 := hu
  have hb : u.1 * Int.gcdA u.1 u.2 + u.2 * Int.gcdB u.1 u.2 = 1 := by
    simpa [hgcd] using (Int.gcd_eq_gcd_ab u.1 u.2).symm
  apply Prod.ext
  · change z.1 = (Int.gcdA u.1 u.2 * z.1 + Int.gcdB u.1 u.2 * z.2) * u.1
    calc
      z.1 = (u.1 * Int.gcdA u.1 u.2 + u.2 * Int.gcdB u.1 u.2) * z.1 := by rw [hb]; ring
      _ = _ := by dsimp [det] at hz; linear_combination -(Int.gcdB u.1 u.2) * hz
  · change z.2 = (Int.gcdA u.1 u.2 * z.1 + Int.gcdB u.1 u.2 * z.2) * u.2
    calc
      z.2 = (u.1 * Int.gcdA u.1 u.2 + u.2 * Int.gcdB u.1 u.2) * z.2 := by rw [hb]; ring
      _ = _ := by dsimp [det] at hz; linear_combination (Int.gcdA u.1 u.2) * hz

private lemma det_keys_injective (u v : Lattice) (h : det u v ≠ 0) :
    Function.Injective (fun p : Lattice => (det u p, det p v)) := by
  intro p q hpq
  have hr := congrArg Prod.fst hpq
  have hc := congrArg Prod.snd hpq
  have hx : (p.1 - q.1) * det u v = 0 := by
    dsimp [det] at hr hc ⊢
    linear_combination v.1 * hr + u.1 * hc
  have hy : (p.2 - q.2) * det u v = 0 := by
    dsimp [det] at hr hc ⊢
    linear_combination v.2 * hr + u.2 * hc
  apply Prod.ext
  · exact sub_eq_zero.mp ((mul_eq_zero.mp hx).resolve_right h)
  · exact sub_eq_zero.mp ((mul_eq_zero.mp hy).resolve_right h)

private lemma frame_injective (a u : Lattice) (h : det a u ≠ 0) :
    Function.Injective (frame a u) := by
  intro x y hxy
  have h1 : (x.1 - y.1) * det a u = 0 := by
    calc
      _ = det (frame a u x) u - det (frame a u y) u := by
        simp [frame, det]; ring
      _ = 0 := by rw [hxy]; ring
  have h2 : (x.2 - y.2) * det a u = 0 := by
    calc
      _ = det a (frame a u x) - det a (frame a u y) := by
        simp [frame, det]; ring
      _ = 0 := by rw [hxy]; ring
  exact Prod.ext (sub_eq_zero.mp ((mul_eq_zero.mp h1).resolve_right h))
    (sub_eq_zero.mp ((mul_eq_zero.mp h2).resolve_right h))

private lemma cancellation_min_degree (F : Finset Lattice) (u : Lattice)
    (root : ℂ) (hc : FiberCancellation F u root) :
    ∀ r ∈ F.image (det u), 2 ≤ (F.filter fun q => det u q = r).card := by
  classical
  intro r hr
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hr
  have hpF : p ∈ fiber F u p := by simp [fiber, hp]
  by_contra hsmall
  have hle : (fiber F u p).card ≤ 1 := by dsimp [fiber]; omega
  have hsingleton : fiber F u p = {p} := by
    apply Finset.eq_singleton_iff_unique_mem.mpr
    exact ⟨hpF, fun q hq => Finset.card_le_one.mp hle q hq p hpF⟩
  have hz := hc.2 p hp
  rw [hsingleton] at hz
  norm_num [fiberCoordinate] at hz

/-! A complex character on actual lattice points. The logarithm is used only
to choose a root of a nonzero complex number. Its exponent is the integer
determinant of the actual point with the transverse direction. -/

private lemma actual_fiber_character (F : Finset Lattice) (u v : Lattice)
    (hu : Primitive u) (huv : det u v ≠ 0) (root : ℂ)
    (hc : FiberCancellation F u root) :
    ∃ w : ℤ → ℂ, (∀ j, w j ≠ 0) ∧
      ∀ i ∈ F.image (det u),
        (F.filter fun q => det u q = i).sum (fun q => w (det q v)) = 0 := by
  let μ : ℂ := Complex.exp (Complex.log root / (det u v : ℂ))
  have hμ : μ ≠ 0 := Complex.exp_ne_zero _
  have hD : (det u v : ℂ) ≠ 0 := by exact_mod_cast huv
  have hroot : μ ^ det u v = root := by
    change Complex.exp (Complex.log root / (det u v : ℂ)) ^ det u v = root
    rw [← Complex.exp_int_mul]
    have hmul : (det u v : ℂ) * (Complex.log root / (det u v : ℂ)) =
        Complex.log root := by field_simp [hD]
    rw [hmul, Complex.exp_log hc.1]
  refine ⟨fun j => μ ^ j, fun j => zpow_ne_zero j hμ, ?_⟩
  intro i hi
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hi
  have hterm : ∀ q ∈ fiber F u p,
      μ ^ det q v = μ ^ det p v * root ^ fiberCoordinate u (q - p) := by
    intro q hq
    have hparallel : det u (q - p) = 0 := by
      have := (Finset.mem_filter.mp hq).2
      dsimp [det] at this ⊢
      linear_combination this
    have hz := primitive_parallel u (q - p) hu hparallel
    have hd : det q v = det p v + det u v * fiberCoordinate u (q - p) := by
      calc
        det q v = det p v + det (q - p) v := by simp [det]; ring
        _ = _ := by
          conv_lhs => rw [hz]
          simp [det]
          ring
    rw [hd, zpow_add₀ hμ, zpow_mul, hroot]
  change (fiber F u p).sum (fun q => μ ^ det q v) = 0
  calc
    _ = (fiber F u p).sum
        (fun q => μ ^ det p v * root ^ fiberCoordinate u (q - p)) :=
      Finset.sum_congr rfl hterm
    _ = μ ^ det p v * (fiber F u p).sum
        (fun q => root ^ fiberCoordinate u (q - p)) := (Finset.mul_sum _ _ _).symm
    _ = 0 := by rw [hc.2 p hp, mul_zero]

private lemma actual_incidence_two (F : Finset Lattice) (u v : Lattice)
    (hF : F.card = 6) (hu : Primitive u) (hv : Primitive v)
    (huv : det u v ≠ 0) (rootU rootV : ℂ)
    (hU : FiberCancellation F u rootU) (hV : FiberCancellation F v rootV) :
    (F.image (det u)).card = 2 ∨ (F.image (fun p => det p v)).card = 2 := by
  classical
  have hrow := cancellation_min_degree F u rootU hU
  have hcol : ∀ j ∈ F.image (fun p => det p v),
      2 ≤ (F.filter fun p => det p v = j).card := by
    intro j hj
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hj
    have hvmin := cancellation_min_degree F v rootV hV
    have heq : (F.filter fun q => det q v = det p v) = fiber F v p := by
      ext q
      simp only [fiber, Finset.mem_filter]
      dsimp [det]
      constructor <;> rintro ⟨hq, he⟩ <;> refine ⟨hq, ?_⟩ <;> linear_combination -he
    rw [heq]
    exact hvmin (det v p) (Finset.mem_image_of_mem _ hp)
  obtain ⟨w, hw, hsum⟩ := actual_fiber_character F u v hu huv rootU hU
  exact nonzero_weight_incidence F (det u) (fun p => det p v)
    (det_keys_injective u v huv) hF hrow hcol w (fun j _ => hw j) hsum

private lemma rectangular_grid (F : Finset Lattice) (u v : Lattice)
    (hF : F.card = 6) (hu : Primitive u) (huv : det u v ≠ 0)
    (hR : (F.image (det u)).card = 2)
    (hC : (F.image (fun p => det p v)).card = 3)
    (hcomplete : ∀ i ∈ F.image (det u), ∀ j ∈ F.image (fun p => det p v),
      ∃ p ∈ F, det u p = i ∧ det p v = j) :
    ∃ p a : Lattice, ∃ b c : ℤ,
      b ≠ 0 ∧ c ≠ 0 ∧ b ≠ c ∧ det a u ≠ 0 ∧ AffineGrid F p a u b c := by
  classical
  obtain ⟨r₀, r₁, hr01, hrows⟩ := Finset.card_eq_two.mp hR
  obtain ⟨c₀, c₁, c₂, hc01, hc02, hc12, hcols⟩ := Finset.card_eq_three.mp hC
  have hr0 : r₀ ∈ F.image (det u) := by rw [hrows]; simp
  have hr1 : r₁ ∈ F.image (det u) := by rw [hrows]; simp
  have hc0 : c₀ ∈ F.image (fun p => det p v) := by rw [hcols]; simp
  have hc1 : c₁ ∈ F.image (fun p => det p v) := by rw [hcols]; simp
  have hc2 : c₂ ∈ F.image (fun p => det p v) := by rw [hcols]; simp
  obtain ⟨p₀, hp0, hp0r, hp0c⟩ := hcomplete r₀ hr0 c₀ hc0
  obtain ⟨p₁, hp1, hp1r, hp1c⟩ := hcomplete r₀ hr0 c₁ hc1
  obtain ⟨p₂, hp2, hp2r, hp2c⟩ := hcomplete r₀ hr0 c₂ hc2
  obtain ⟨q₀, hq0, hq0r, hq0c⟩ := hcomplete r₁ hr1 c₀ hc0
  obtain ⟨q₁, hq1, hq1r, hq1c⟩ := hcomplete r₁ hr1 c₁ hc1
  obtain ⟨q₂, hq2, hq2r, hq2c⟩ := hcomplete r₁ hr1 c₂ hc2
  let a := q₀ - p₀
  let b := fiberCoordinate u (p₁ - p₀)
  let c := fiberCoordinate u (p₂ - p₀)
  have hb : p₁ - p₀ = b • u := by
    apply primitive_parallel u _ hu
    dsimp [det] at hp0r hp1r ⊢
    linear_combination hp1r - hp0r
  have hc : p₂ - p₀ = c • u := by
    apply primitive_parallel u _ hu
    dsimp [det] at hp0r hp2r ⊢
    linear_combination hp2r - hp0r
  have hp1eq : p₁ = p₀ + b • u := by rw [← hb]; abel
  have hp2eq : p₂ = p₀ + c • u := by rw [← hc]; abel
  have hq0eq : q₀ = p₀ + a := by dsimp [a]; abel
  have hq1eq : q₁ = p₀ + a + b • u := by
    apply det_keys_injective u v huv
    apply Prod.ext
    · change det u q₁ = det u (p₀ + a + b • u)
      rw [hq1r]
      rw [← hq0eq]
      dsimp [det] at hq0r ⊢
      linear_combination -hq0r
    · change det q₁ v = det (p₀ + a + b • u) v
      rw [hq1c]
      have : det q₀ v = det p₀ v := hq0c.trans hp0c.symm
      have : det (p₀ + a + b • u) v = det p₁ v := by
        rw [hp1eq, ← hq0eq]
        dsimp [det] at this ⊢
        linear_combination this
      exact hp1c.symm.trans this.symm
  have hq2eq : q₂ = p₀ + a + c • u := by
    apply det_keys_injective u v huv
    apply Prod.ext
    · change det u q₂ = det u (p₀ + a + c • u)
      rw [hq2r]
      rw [← hq0eq]
      dsimp [det] at hq0r ⊢
      linear_combination -hq0r
    · change det q₂ v = det (p₀ + a + c • u) v
      rw [hq2c]
      have : det q₀ v = det p₀ v := hq0c.trans hp0c.symm
      have : det (p₀ + a + c • u) v = det p₂ v := by
        rw [hp2eq, ← hq0eq]
        dsimp [det] at this ⊢
        linear_combination this
      exact hp2c.symm.trans this.symm
  have hb0 : b ≠ 0 := by
    intro hz
    have heq : p₁ = p₀ := by simpa [hz] using hp1eq
    exact hc01 (by rw [← hp0c, ← hp1c, heq])
  have hc0' : c ≠ 0 := by
    intro hz
    have heq : p₂ = p₀ := by simpa [hz] using hp2eq
    exact hc02 (by rw [← hp0c, ← hp2c, heq])
  have hbc : b ≠ c := by
    intro hz
    have heq : p₁ = p₂ := by rw [hp1eq, hp2eq, hz]
    exact hc12 (by rw [← hp1c, ← hp2c, heq])
  have hau : det a u ≠ 0 := by
    intro hz
    apply hr01
    dsimp [a, det] at hz
    dsimp [det] at hp0r hq0r
    linear_combination -hp0r + hq0r + hz
  refine ⟨p₀, a, b, c, hb0, hc0', hbc, hau, ?_⟩
  let S := (({0, 1} : Finset ℤ).product ({0, b, c} : Finset ℤ)).image
    (fun z => p₀ + frame a u z)
  have hsub : S ⊆ F := by
    intro z hz
    obtain ⟨⟨i, j⟩, hij, rfl⟩ := Finset.mem_image.mp hz
    rcases Finset.mem_product.mp hij with ⟨hi, hj⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj
    rcases hi with rfl | rfl <;> rcases hj with rfl | rfl | rfl
    · simpa [frame] using hp0
    · simpa [frame, hp1eq] using hp1
    · simpa [frame, hp2eq] using hp2
    · simpa [frame, hq0eq] using hq0
    · simpa [frame, hq1eq, add_assoc] using hq1
    · simpa [frame, hq2eq, add_assoc] using hq2
  have hSinj : Function.Injective (fun z => p₀ + frame a u z) := by
    intro x y he
    exact frame_injective a u hau (add_left_cancel he)
  have hScard : S.card = 6 := by
    dsimp only [S]
    rw [Finset.card_image_of_injective _ hSinj, Finset.product_eq_sprod,
      Finset.card_product]
    simp [hb0, hc0', hbc, Ne.symm hb0, Ne.symm hc0']
  exact (Finset.eq_of_subset_of_card_le hsub (by omega)).symm

/-- Two actual cancellation directions give an actual affine Minkowski grid.
The proof uses arbitrary lattice points, a nonzero complex root, and counting
of occupied fibers; no grid-realization premise is assumed. -/
theorem two_direction_cancellation_grid
    (F : Finset Lattice) (u v : Lattice) (rootU rootV : ℂ)
    (hF : F.card = 6) (hu : Primitive u) (hv : Primitive v)
    (huv : det u v ≠ 0)
    (hU : FiberCancellation F u rootU) (hV : FiberCancellation F v rootV) :
    ∃ p a w : Lattice, ∃ b c : ℤ,
      (w = u ∨ w = v) ∧ b ≠ 0 ∧ c ≠ 0 ∧ b ≠ c ∧
        det a w ≠ 0 ∧ AffineGrid F p a w b c := by
  classical
  have hrow := cancellation_min_degree F u rootU hU
  have hcol : ∀ j ∈ F.image (fun p => det p v),
      2 ≤ (F.filter fun p => det p v = j).card := by
    intro j hj
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hj
    have heq : (F.filter fun q => det q v = det p v) = fiber F v p := by
      ext q
      simp only [fiber, Finset.mem_filter]
      dsimp [det]
      constructor <;> rintro ⟨hq, he⟩ <;> refine ⟨hq, ?_⟩ <;> linear_combination -he
    rw [heq]
    exact cancellation_min_degree F v rootV hV _ (Finset.mem_image_of_mem _ hp)
  have hinj := det_keys_injective u v huv
  have hswap : Function.Injective fun p : Lattice => (det p v, det u p) := by
    intro x y hxy
    exact hinj (Prod.ext (congrArg Prod.snd hxy) (congrArg Prod.fst hxy))
  rcases actual_incidence_two F u v hF hu hv huv rootU rootV hU hV with hR | hC
  · have hbound := occupied_key_bounds F (fun p => det p v) (det u) hswap hF hcol hrow
    obtain ⟨hc3, hall⟩ := complete_incidence_of_two F (det u) (fun p => det p v)
      hinj hF hR hbound.2
    obtain ⟨p, a, b, c, hb, hc, hbc, hau, hg⟩ :=
      rectangular_grid F u v hF hu huv hR hc3 hall
    exact ⟨p, a, u, b, c, Or.inl rfl, hb, hc, hbc, hau, hg⟩
  · have hvu : det v u ≠ 0 := by dsimp [det] at huv ⊢; intro h; apply huv; linear_combination -h
    have hR' : (F.image (det v)).card = 2 := by
      have heq : F.image (det v) = (F.image (fun p => det p v)).image Neg.neg := by
        ext j
        simp only [Finset.mem_image]
        constructor
        · rintro ⟨p, hp, rfl⟩
          exact ⟨det p v, ⟨p, hp, rfl⟩, by dsimp [det]; ring⟩
        · rintro ⟨j, ⟨p, hp, rfl⟩, rfl⟩
          exact ⟨p, hp, by dsimp [det]; ring⟩
      rw [heq, Finset.card_image_of_injective _ neg_injective, hC]
    have hr' := cancellation_min_degree F v rootV hV
    have hc' : ∀ j ∈ F.image (fun p => det p u),
        2 ≤ (F.filter fun p => det p u = j).card := by
      intro j hj
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hj
      have heq : (F.filter fun q => det q u = det p u) = fiber F u p := by
        ext q
        simp only [fiber, Finset.mem_filter]
        dsimp [det]
        constructor <;> rintro ⟨hq, he⟩ <;> refine ⟨hq, ?_⟩ <;> linear_combination -he
      rw [heq]
      exact hrow _ (Finset.mem_image_of_mem _ hp)
    have hi' := det_keys_injective v u hvu
    have his' : Function.Injective fun p : Lattice => (det p u, det v p) := by
      intro x y hxy
      exact hi' (Prod.ext (congrArg Prod.snd hxy) (congrArg Prod.fst hxy))
    have hbound := occupied_key_bounds F (fun p => det p u) (det v) his' hF hc' hr'
    obtain ⟨hc3, hall⟩ := complete_incidence_of_two F (det v) (fun p => det p u)
      hi' hF hR' hbound.2
    obtain ⟨p, a, b, c, hb, hc, hbc, hau, hg⟩ :=
      rectangular_grid F v u hF hv hvu hR' hc3 hall
    exact ⟨p, a, v, b, c, Or.inr rfl, hb, hc, hbc, hau, hg⟩

private lemma grid_frame_surjective (F : Finset Lattice) (p a u : Lattice)
    (b c : ℤ) (hg : AffineGrid F p a u b c) (hspan : FullDifferenceSpan F) :
    Function.Surjective (frame a u) := by
  have hle : Submodule.span ℤ {z : Lattice | ∃ x ∈ F, ∃ y ∈ F, z = x - y} ≤
      LinearMap.range (frame a u) := by
    apply Submodule.span_le.mpr
    rintro z ⟨x, hx, y, hy, rfl⟩
    rw [hg] at hx hy
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hy
    refine ⟨i - j, ?_⟩
    rw [map_sub]
    abel
  rw [hspan] at hle
  exact LinearMap.range_eq_top.mp (le_antisymm le_top hle)

private lemma grid_gcd_one (F : Finset Lattice) (p a u : Lattice) (b c : ℤ)
    (e : Lattice ≃ₗ[ℤ] Lattice)
    (he : ∀ z, e z = frame a u z)
    (hg : AffineGrid F p a u b c) (hspan : FullDifferenceSpan F) :
    Int.gcd b c = 1 := by
  let d : ℤ := Int.gcd b c
  let N : Submodule ℤ Lattice :=
    { carrier := {z | d ∣ (e.symm z).2}
      zero_mem' := by simp
      add_mem' := by
        intro x y hx hy
        change d ∣ (e.symm (x + y)).2
        simpa using dvd_add hx hy
      smul_mem' := by
        intro k x hx
        change d ∣ (e.symm (k • x)).2
        rw [map_smul]
        simpa only [Prod.smul_snd, smul_eq_mul] using dvd_mul_of_dvd_right hx k }
  have hdiv : ∀ z ∈ ({0, b, c} : Finset ℤ), d ∣ z := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with hz | hz | hz
    · rw [hz]; exact dvd_zero _
    · rw [hz]; exact Int.gcd_dvd_left b c
    · rw [hz]; exact Int.gcd_dvd_right b c
  have hle : Submodule.span ℤ {z : Lattice | ∃ x ∈ F, ∃ y ∈ F, z = x - y} ≤ N := by
    apply Submodule.span_le.mpr
    rintro z ⟨x, hx, y, hy, rfl⟩
    rw [hg] at hx hy
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hy
    change d ∣ (e.symm ((p + frame a u i) - (p + frame a u j))).2
    rw [← he i, ← he j]
    have hdiff : (p + e i) - (p + e j) = e (i - j) := by rw [map_sub]; abel
    rw [hdiff, e.symm_apply_apply]
    exact dvd_sub (hdiv i.2 (Finset.mem_product.mp hi).2)
      (hdiv j.2 (Finset.mem_product.mp hj).2)
  rw [hspan] at hle
  have hone : d ∣ (1 : ℤ) := by
    have hm : e (0, 1) ∈ N := hle (Submodule.mem_top)
    change d ∣ (e.symm (e (0, 1))).2 at hm
    simpa using hm
  change (Int.gcd b c : ℤ) ∣ (1 : ℤ) at hone
  have hn : Int.gcd b c ∣ (1 : ℕ) := by exact_mod_cast hone
  exact Nat.dvd_one.mp hn

private lemma frame_det_unit (a u : Lattice) (hs : Function.Surjective (frame a u)) :
    det a u = 1 ∨ det a u = -1 := by
  obtain ⟨x, hx⟩ := hs (1, 0)
  obtain ⟨y, hy⟩ := hs (0, 1)
  have hmul : det a u * det x y = 1 := by
    calc
      _ = det (frame a u x) (frame a u y) := by simp [frame, det]; ring
      _ = 1 := by rw [hx, hy]; norm_num [det]
  exact Int.eq_one_or_neg_one_of_mul_eq_one hmul

/-- Full integer-difference span supplies both the lattice automorphism and
the coprimality of the two longitudinal offsets. Neither is a premise. -/
theorem full_span_grid_normalization
    (F : Finset Lattice) (p a u : Lattice) (b c : ℤ)
    (hg : AffineGrid F p a u b c) (hau : det a u ≠ 0)
    (hspan : FullDifferenceSpan F) :
    ∃ e : Lattice ≃ₗ[ℤ] Lattice,
      (∀ z, e z = z.1 • a + z.2 • u) ∧ Int.gcd b c = 1 ∧
        (det a u = 1 ∨ det a u = -1) := by
  have hsurj := grid_frame_surjective F p a u b c hg hspan
  let e : Lattice ≃ₗ[ℤ] Lattice :=
    LinearEquiv.ofBijective (frame a u) ⟨frame_injective a u hau, hsurj⟩
  have he : ∀ z, e z = frame a u z := fun _ => rfl
  exact ⟨e, he, grid_gcd_one F p a u b c e he hg hspan, frame_det_unit a u hsurj⟩

private lemma affine_exact_cover_transport
    (F : Finset Lattice) (T : Lattice → Prop) (p a u : Lattice) (b c : ℤ)
    (e : Lattice ≃ₗ[ℤ] Lattice) (he : ∀ z, e z = frame a u z)
    (hg : AffineGrid F p a u b c) :
    ∀ x y, KhetanProductPeriodicity.productWindowCount
      (fun i j => T (e (i, j) - p)) b c x y = exactCoverCount F T (e (x, y)) := by
  classical
  intro x y
  let n := exactCoverCount F T (e (x, y))
  have h : exactCoverCount F T (e (x, y)) = n := rfl
  have hinj : Function.Injective (fun z : Lattice => p + frame a u z) := by
    intro i j hij
    apply e.injective
    rw [he i, he j]
    exact add_left_cancel hij
  conv_lhs at h =>
    unfold exactCoverCount
    rw [hg, Finset.sum_image (fun i _ j _ hij => hinj hij),
      Finset.product_eq_sprod, Finset.sum_product]
  have hpoint (i j : ℤ) :
      e (x, y) - (p + frame a u (i, j)) = e (x - i, y - j) - p := by
    rw [← he (i, j)]
    have hp : (x - i, y - j) = (x, y) - (i, j) := rfl
    rw [hp, map_sub]
    abel
  simp_rw [hpoint] at h
  simp only [Finset.sum_insert (by norm_num : (0 : ℤ) ∉ ({1} : Finset ℤ)),
    Finset.sum_singleton, sub_zero] at h
  change KhetanProductPeriodicity.productWindowCount
    (fun i j => T (e (i, j) - p)) b c x y = n
  unfold KhetanProductPeriodicity.productWindowCount KhetanProductPeriodicity.anchorBit
  rw [Finset.sum_add_distrib]
  simpa [add_comm] using h

private lemma affine_period_iff
    (T : Lattice → Prop) (p : Lattice) (e : Lattice ≃ₗ[ℤ] Lattice) (v : Lattice) :
    Period (fun z => T (e z - p)) v ↔ Period T (e v) := by
  constructor
  · intro hp t
    let z := e.symm (t + p)
    have hz : e z - p = t := by simp [z]
    have hv : e (z + v) - p = t + e v := by rw [map_add, ← hz]; abel
    simpa only [hv, hz] using hp z
  · intro hp z
    have hv : e (z + v) - p = (e z - p) + e v := by rw [map_add]; abel
    simpa only [hv] using hp (e z - p)

private lemma affine_period_transport
    (T : Lattice → Prop) (p a u : Lattice) (e : Lattice ≃ₗ[ℤ] Lattice)
    (he : ∀ z, e z = frame a u z)
    (hp : (∀ x y, T (e (x + 2, y) - p) ↔ T (e (x, y) - p)) ∨
      (∀ x y, T (e (x, y + 3) - p) ↔ T (e (x, y) - p))) :
    Period T ((2 : ℤ) • a) ∨ Period T ((3 : ℤ) • u) := by
  rcases hp with hp | hp
  · left
    have hp0 : Period (fun z => T (e z - p)) (2, 0) := by
      rintro ⟨x, y⟩
      change T (e (x + 2, y + 0) - p) ↔ T (e (x, y) - p)
      simpa only [add_zero] using hp x y
    have ht := (affine_period_iff T p e (2, 0)).mp hp0
    simpa [he, frame] using ht
  · right
    have hp0 : Period (fun z => T (e z - p)) (0, 3) := by
      rintro ⟨x, y⟩
      change T (e (x + 0, y + 3) - p) ↔ T (e (x, y) - p)
      simpa only [add_zero] using hp x y
    have ht := (affine_period_iff T p e (0, 3)).mp hp0
    simpa [he, frame] using ht

/-- The complete geometric branch follows the given exact-cover complement.
Its coordinate predicate is precisely `T₀(i,j) = T(e(i,j)-p)`, so the result
is a period of the original `T`, rather than a replacement tiling. -/
theorem two_direction_exact_cover_periodic
    (F : Finset Lattice) (T : Lattice → Prop) (u v : Lattice) (rootU rootV : ℂ)
    (hF : F.card = 6) (hu : Primitive u) (hv : Primitive v)
    (huv : det u v ≠ 0)
    (hU : FiberCancellation F u rootU) (hV : FiberCancellation F v rootV)
    (hspan : FullDifferenceSpan F) (hcover : ExactCover F T) :
    ∃ p a w : Lattice, ∃ b c : ℤ, ∃ e : Lattice ≃ₗ[ℤ] Lattice,
      (w = u ∨ w = v) ∧ b ≠ 0 ∧ c ≠ 0 ∧ b ≠ c ∧
      AffineGrid F p a w b c ∧ Int.gcd b c = 1 ∧
      (det a w = 1 ∨ det a w = -1) ∧
      (∀ z, e z = z.1 • a + z.2 • w) ∧
      (Period T ((2 : ℤ) • a) ∨ Period T ((3 : ℤ) • w)) ∧
      (2 : ℤ) • a ≠ 0 ∧ (3 : ℤ) • w ≠ 0 := by
  obtain ⟨p, a, w, b, c, hw, hb0, hc0, hbc, hau, hg⟩ :=
    two_direction_cancellation_grid F u v rootU rootV hF hu hv huv hU hV
  obtain ⟨e, he, hgcd, hdet⟩ := full_span_grid_normalization F p a w b c hg hau hspan
  have hef : ∀ z, e z = frame a w z := he
  have hcover0 : ∀ x y, KhetanProductPeriodicity.productWindowCount
      (fun i j => T (e (i, j) - p)) b c x y = 1 := by
    intro x y
    rw [affine_exact_cover_transport F T p a w b c e hef hg]
    exact hcover (e (x, y))
  have hperiod := KhetanProductPeriodicity.product_three_exact_cover_periodic
    (fun i j => T (e (i, j) - p)) b c hb0 hc0 hbc hgcd hcover0
  have hp := affine_period_transport T p a w e hef hperiod
  have h2 : (2 : ℤ) • a ≠ 0 := by
    intro hz
    have : e (2, 0) = e 0 := by simpa [he] using hz
    have := e.injective this
    have := congrArg Prod.fst this
    norm_num at this
  have h3 : (3 : ℤ) • w ≠ 0 := by
    intro hz
    have : e (0, 3) = e 0 := by simpa [he] using hz
    have := e.injective this
    have := congrArg Prod.snd this
    norm_num at this
  exact ⟨p, a, w, b, c, e, hw, hb0, hc0, hbc, hg, hgcd, hdet, he, hp, h2, h3⟩

private lemma period_on_orbit_closure
    (T : Lattice → Prop) (v : Lattice) (hp : Period T v) :
    ∀ c ∈ closure (Set.range (fun s : Lattice => fun x => indicator T (x + s))),
      ∀ x, c (x + v) = c x := by
  classical
  let shiftV : (Lattice → ℕ) → (Lattice → ℕ) := fun c x => c (x + v)
  have hclosed : IsClosed (Function.fixedPoints shiftV) :=
    isClosed_fixedPoints (continuous_pi fun x => continuous_apply (x + v))
  have hsub : Set.range (fun s : Lattice => fun x => indicator T (x + s)) ⊆
      Function.fixedPoints shiftV := by
    rintro c ⟨s, rfl⟩
    change (fun x => indicator T (x + v + s)) = (fun x => indicator T (x + s))
    funext x
    rw [show x + v + s = (x + s) + v by abel]
    unfold indicator
    rw [propext (hp (x + s))]
  intro c hc x
  have hf : shiftV c = c := closure_minimal hsub hclosed hc
  exact congrFun hf x

/-- In the two-direction branch, every configuration in the orbit closure of
the given tiling has one and the same nonzero period. -/
theorem two_direction_orbit_closure_periodic
    (F : Finset Lattice) (T : Lattice → Prop) (u v : Lattice) (rootU rootV : ℂ)
    (hF : F.card = 6) (hu : Primitive u) (hv : Primitive v)
    (huv : det u v ≠ 0)
    (hU : FiberCancellation F u rootU) (hV : FiberCancellation F v rootV)
    (hspan : FullDifferenceSpan F) (hcover : ExactCover F T) :
    ∃ t : Lattice, t ≠ 0 ∧
      ∀ c ∈ closure (Set.range (fun s : Lattice => fun x => indicator T (x + s))),
        ∀ x, c (x + t) = c x := by
  obtain ⟨p, a, w, b, c, e, hw, hb0, hc0, hbc, hg, hgcd, hdet, he, hp, h2, h3⟩ :=
    two_direction_exact_cover_periodic F T u v rootU rootV hF hu hv huv hU hV
      hspan hcover
  rcases hp with hp | hp
  · exact ⟨(2 : ℤ) • a, h2, period_on_orbit_closure T _ hp⟩
  · exact ⟨(3 : ℤ) • w, h3, period_on_orbit_closure T _ hp⟩

end D5.S1.Dynamics.Symbolic.KhetanLatticeGeometry
