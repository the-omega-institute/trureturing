/- GID: D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdTwistedChargeAction
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/Orbifold/ThirdTwistedChargeAction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Descent to the integral moving lattice and multiplication of actual order-three momentum charge operators. -/

import D5.S3.VertexAlgebra.Lattice.Orbifold.ThirdTwistedChargeCocycle
import Mathlib.Tactic.Abel

/-!
The charge-operator construction uses Bojko Bakalov and Victor G. Kac,
*Twisted Modules over Lattice Vertex Algebras*, arXiv:math/0402315v3,
(4.27) and §4.3, (4.42)–(4.46), together with the normalized phase convention
of (4.18)–(4.19). Write `d = 1 - g` and `N = 1 + g + g²`.
The momentum index `p` in `range N` represents the fixed projection `p / 3`.

The descent assumes an even integral lattice, `g³ = 1`, preservation of its
pairing, a normalized bimultiplicative unit multiplier with the specified
moving commutator, and a compatible lift phase trivial on fixed charges.
Cubicity of the multiplier's root is sufficient. `MovingExact` is the additional
integral hypothesis `ker N = range d`; in the P48q application this is supplied
by the Nebe row-lattice moving certificate. The existing ThirdTwistedChargeCocycle
module supplies the concrete BK multiplier and its moving commutator.

The descended scalar `chi` is independent of the representative along `d` and
satisfies the twisted multiplication law on the moving subgroup. Choosing a
section of `N` produces the momentum translation and its coefficient. The
cocycle identity and the multiplication of `chi` give `U_comp` on the entire
finite-support complex module. `U_difference_single` proves the moving-charge
scalar relation at every momentum. The native standard phase is constructed
separately using the sign of the native lift on the orbit norm and the stated
rescaling compatibility with the multiplier.

These statements concern the charge part of the order-three construction.
The P48q specialization, oscillator fields and full twisted-module identities
require subsequent results.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.Lattice.Orbifold.ThirdTwistedChargeAction

open LatticeGeneratingFieldLocality
open LatticeActualGeneratorLocality (bilinear_add_right)
open LatticeFiniteNegativeGeneration (bilinear_symmetric)
open CyclicIsometryLift (orbitNorm)
open ThirdTwistedChargeCocycle (pairing_shift_one pairing_shift_two)

noncomputable section

variable (D : LatticeData) (g : Charge D ≃+ Charge D)

def d : Charge D →+ Charge D :=
  AddMonoidHom.id (Charge D) - g.toAddMonoidHom

@[simp] theorem d_apply (a : Charge D) : d D g a = a - g a := rfl

abbrev N : Charge D →+ Charge D := orbitNorm D g 3

theorem N_apply (a : Charge D) : N D g a = a + g a + g (g a) :=
  ThirdTwistedChargeCocycle.orbitNorm_three D g a

variable (h3 : ∀ a, g (g (g a)) = a)
variable (hg : ∀ a b, bilinear D (g a) (g b) = bilinear D a b)

include h3 in
theorem norm_fixed (a : Charge D) : g (N D g a) = N D g a := by
  simp only [N_apply, map_add, h3]
  abel

include h3 in
@[simp] theorem norm_difference (a : Charge D) : N D g (d D g a) = 0 := by
  simp only [d_apply, map_sub, N_apply, h3]
  abel

def q (a : Charge D) : ℤ := bilinear D a (g a) - bilinear D a a

/-- Equation (4.27), with the squared norm of the fixed projection written using
the integral numerator of that projection. -/
def bShift (a : Charge D) : ℚ :=
  ((bilinear D (N D g a) (N D g a) : ℚ) / 9 - (bilinear D a a : ℚ)) / 2

include h3 hg in
theorem norm_pairing (a b : Charge D) :
    bilinear D (N D g a) b = bilinear D a (N D g b) :=
  ThirdTwistedChargeCocycle.orbitNorm_pairing D g hg h3 a b

include h3 hg in
private theorem norm_pairing_g (a b : Charge D) :
    bilinear D (N D g a) (g b) = bilinear D (N D g a) b := by
  simpa only [norm_fixed D g h3 a] using hg (N D g a) b

include h3 hg in
theorem three_mul_bShift (a : Charge D) :
    3 * bShift D g a = (q D g a : ℚ) := by
  have hPair : bilinear D a (N D g a) = bilinear D a a + 2 * bilinear D a (g a) := by
    rw [N_apply, bilinear_add_right, bilinear_add_right, pairing_shift_two D g hg h3,
      bilinear_symmetric D (g a) a]
    ring
  have hNorm : bilinear D (N D g a) (N D g a) =
      3 * (bilinear D a a + 2 * bilinear D a (g a)) := by
    calc
      bilinear D (N D g a) (N D g a) =
          bilinear D (N D g a) (a + g a + g (g a)) :=
        congrArg (bilinear D (N D g a)) (N_apply D g a)
      _ = 3 * bilinear D (N D g a) a := by
        rw [bilinear_add_right, bilinear_add_right,
          norm_pairing_g D g h3 hg a (g a), norm_pairing_g D g h3 hg a a]
        ring
      _ = _ := by rw [norm_pairing D g h3 hg a a, hPair]
  unfold bShift q
  rw [hNorm]
  push_cast
  ring

include h3 hg in
theorem q_polarization (a b : Charge D) :
    q D g (a + b) - q D g a - q D g b =
      bilinear D (N D g a) b - 3 * bilinear D a b := by
  rw [bilinear_symmetric D (N D g a) b]
  simp only [q, map_add, N_apply, bilinear_add_right]
  simp only [bilinear_symmetric D (a + b), bilinear_add_right,
    bilinear_symmetric D (g a) a, bilinear_symmetric D (g b) b,
    bilinear_symmetric D (g a) b, bilinear_symmetric D (g b) a,
    pairing_shift_one D g hg h3 a b, bilinear_symmetric D (g (g a)) b,
    bilinear_symmetric D b a]
  ring

/-- Input supplied by the order-three multiplier of (4.42) and its moving
commutator. Cubicity is the only property of the primitive root used here. -/
structure Multiplier where
  c : Charge D → Charge D → ℂˣ
  zeta : ℂˣ
  cube : zeta ^ (3 : ℤ) = 1
  zero_mul : ∀ a, c 0 a = 1
  mul_zero : ∀ a, c a 0 = 1
  add_left : ∀ a b t, c (a + b) t = c a t * c b t
  add_right : ∀ a b t, c a (b + t) = c a b * c a t
  commutator : ∀ a b, c (d D g a) b / c b (d D g a) = zeta ^ (-bilinear D (N D g a) b)

theorem Multiplier.cocycle {D : LatticeData} {g : Charge D ≃+ Charge D}
    (C : Multiplier D g) (a b t : Charge D) :
    C.c a b * C.c (a + b) t = C.c b t * C.c a (b + t) := by
  rw [C.add_left a b t, C.add_right a b t]
  ac_rfl

/-- The lift phase in the twisted multiplier convention, normalized on fixed charges. -/
structure LiftPhase (C : Multiplier D g) where
  eta : Charge D → ℂˣ
  mul : ∀ a b, eta a * eta b * C.c a b = eta (a + b) * C.c (g a) (g b)
  fixed : ∀ a, g a = a → eta a = 1

private theorem epsilon_ne_zero (a b : Charge D) : epsilon D a b ≠ 0 := by
  intro h
  have hs : epsilon D a b * epsilon D a b = 1 :=
    LatticeActualGeneratorLocality.paritySign_square (lowerCocycleExponent D a b)
  rw [h, zero_mul] at hs
  exact zero_ne_one hs

include hg in
private theorem phase_add_fixed (a b : Charge D) (ha : g a = a) (hb : g b = b) :
    IsometryLift.phase D g (a + b) = IsometryLift.phase D g a * IsometryLift.phase D g b := by
  apply Units.ext
  apply mul_right_cancel₀ (epsilon_ne_zero D a b)
  simpa only [Units.val_mul, ha, hb] using IsometryLift.phase_law D g hg a b

/-- Correct the native phase by the inverse of its fixed-charge character pulled
back along the orbit norm. -/
def nativeStandardEta (a : Charge D) : ℂˣ :=
  IsometryLift.phase D g a * (IsometryLift.phase D g (N D g a))⁻¹

include hg in
theorem nativeStandardEta_fixed (a : Charge D) (ha : g a = a) :
    nativeStandardEta D g a = 1 := by
  have haa : g (a + a) = a + a := by rw [map_add, ha]
  unfold nativeStandardEta
  simp only [N_apply, ha]
  rw [phase_add_fixed D g hg (a + a) a haa ha,
    phase_add_fixed D g hg a a ha ha, CyclicIsometryLift.phase_square D g hg a, one_mul]
  exact mul_inv_cancel _

include h3 hg in
/-- The concrete multiplier supplies this compatibility because its factor
multiplying epsilon is invariant under simultaneous application of the isometry. -/
def nativeLiftPhase (C : Multiplier D g)
    (hRescale : ∀ a b, (C.c a b : ℂ) * epsilon D a b =
      (C.c (g a) (g b) : ℂ) * epsilon D (g a) (g b)) :
    LiftPhase D g C where
  eta := nativeStandardEta D g
  fixed := nativeStandardEta_fixed D g hg
  mul a b := by
    have hPhase : IsometryLift.phase D g a * IsometryLift.phase D g b * C.c a b =
        IsometryLift.phase D g (a + b) * C.c (g a) (g b) := by
      apply Units.ext
      simp only [Units.val_mul]
      apply mul_right_cancel₀ (epsilon_ne_zero D (g a) (g b))
      calc
        _ = ((IsometryLift.phase D g a : ℂ) * (IsometryLift.phase D g b : ℂ) *
            epsilon D (g a) (g b)) * (C.c a b : ℂ) := by ac_rfl
        _ = (IsometryLift.phase D g (a + b) : ℂ) * ((C.c a b : ℂ) * epsilon D a b) := by
          rw [← IsometryLift.phase_law D g hg a b]
          ac_rfl
        _ = _ := by
          rw [hRescale a b]
          ac_rfl
    unfold nativeStandardEta
    rw [map_add (N D g), phase_add_fixed D g hg (N D g a) (N D g b)
      (norm_fixed D g h3 a) (norm_fixed D g h3 b)]
    calc
      _ = (IsometryLift.phase D g a * IsometryLift.phase D g b * C.c a b) *
          (IsometryLift.phase D g (N D g a) * IsometryLift.phase D g (N D g b))⁻¹ := by
        apply Additive.ofMul.injective
        simp only [ofMul_mul, ofMul_inv]
        abel
      _ = _ := by
        rw [hPhase]
        ac_rfl

variable (C : Multiplier D g) (E : LiftPhase D g C)

/-- The scalar of a difference charge at zero momentum, from (4.46). -/
def f (a : Charge D) : ℂˣ :=
  (E.eta a)⁻¹ * C.c (g a) (d D g a) * C.zeta ^ (-q D g a)

theorem f_ratio (a b : Charge D) :
    f D g C E a * f D g C E b / (C.c (d D g a) (d D g b) * f D g C E (a + b)) =
      (C.c (d D g a) (g b) / C.c (g b) (d D g a)) *
        C.zeta ^ (q D g (a + b) - q D g a - q D g b) := by
  have hEta : (E.eta a)⁻¹ * (E.eta b)⁻¹ * E.eta (a + b) =
      C.c a b * (C.c (g a) (g b))⁻¹ := by
    apply mul_right_cancel (b := C.c (g a) (g b))
    calc
      _ = (E.eta a)⁻¹ * (E.eta b)⁻¹ * (E.eta (a + b) * C.c (g a) (g b)) := by
        ac_rfl
      _ = _ := by
        rw [← E.mul a b]
        apply Additive.ofMul.injective
        simp only [ofMul_mul, ofMul_inv]
        abel
  have hGa : g a + d D g a = a := by rw [d_apply]; abel
  have hGb : g b + d D g b = b := by rw [d_apply]; abel
  have hC : C.c a b =
      (C.c (g a) (g b) * C.c (g a) (d D g b)) *
        (C.c (d D g a) (g b) * C.c (d D g a) (d D g b)) := by
    calc
      C.c a b = C.c (g a + d D g a) (g b + d D g b) := by rw [hGa, hGb]
      _ = _ := by rw [C.add_left, C.add_right, C.add_right]
  calc
    _ = ((E.eta a)⁻¹ * (E.eta b)⁻¹ * E.eta (a + b)) *
        ((C.c (g a) (d D g a) * C.c (g b) (d D g b)) /
          (C.c (d D g a) (d D g b) * C.c (g (a + b)) (d D g (a + b)))) *
        C.zeta ^ (q D g (a + b) - q D g a - q D g b) := by
      apply Additive.ofMul.injective
      simp only [f, zpow_sub, zpow_neg, ofMul_mul, ofMul_div, ofMul_inv]
      abel
    _ = _ := by
      rw [hEta, hC, map_add g, map_add (d D g),
        C.add_left (g a) (g b) (d D g a + d D g b),
        C.add_right (g a) (d D g a) (d D g b),
        C.add_right (g b) (d D g a) (d D g b)]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_div, ofMul_inv]
      abel

include h3 hg in
theorem f_mul (a b : Charge D) :
    f D g C E a * f D g C E b = C.c (d D g a) (d D g b) * f D g C E (a + b) := by
  apply div_eq_one.mp
  rw [f_ratio, C.commutator, norm_pairing_g D g h3 hg, q_polarization D g h3 hg, ← zpow_add]
  rw [show -bilinear D (N D g a) b + (bilinear D (N D g a) b - 3 * bilinear D a b) =
      3 * (-bilinear D a b) by ring, zpow_mul, C.cube, one_zpow]

theorem f_fixed (a : Charge D) (ha : g a = a) : f D g C E a = 1 := by
  simp only [f, E.fixed a ha, d_apply, q, ha, sub_self, C.mul_zero, inv_one,
    neg_zero, zpow_zero, mul_one]

include h3 hg in
theorem f_congr {a b : Charge D} (hab : d D g a = d D g b) :
    f D g C E a = f D g C E b := by
  have hd : d D g (a - b) = 0 := by rw [map_sub, hab, sub_self]
  have hf : g (a - b) = a - b := (sub_eq_zero.mp (by simpa only [d_apply] using hd)).symm
  have h := f_mul D g h3 hg C E b (a - b)
  rw [hd, C.mul_zero, f_fixed D g C E (a - b) hf, mul_one, one_mul,
    show b + (a - b) = a by abel] at h
  exact h.symm

/-- The nonzero-momentum scalar of (4.46), evaluated at the fixed projection
of a lattice charge. The exponent depends integrally on the orbit norm. -/
def fAt (a b : Charge D) : ℂˣ :=
  f D g C E a * C.zeta ^ (-bilinear D (N D g a) b)

include h3 hg in
theorem fAt_congr {a a' b b' : Charge D}
    (ha : d D g a = d D g a') (hb : N D g b = N D g b') :
    fAt D g C E a b = fAt D g C E a' b' := by
  unfold fAt
  rw [f_congr D g h3 hg C E ha, ← C.commutator a b, ha,
    C.commutator a' b, norm_pairing D g h3 hg a' b, hb,
    ← norm_pairing D g h3 hg a' b']

abbrev Moving := (N D g).ker
abbrev Momentum := (N D g).range

include h3 in
def differenceCharge (a : Charge D) : Moving D g :=
  ⟨d D g a, norm_difference D g h3 a⟩

/-- Every integral charge in the norm kernel is a difference charge. When
`g³ = 1`, `norm_difference` gives the reverse inclusion, so this is exactness
of the integral moving lattice, `ker N = range d`. -/
def MovingExact : Prop :=
  ∀ m : Charge D, N D g m = 0 → ∃ a, d D g a = m

variable (hExact : MovingExact D g)

/-- The scalar on the actual moving lattice, namely the integral norm kernel. -/
def chi (m : Moving D g) : ℂˣ :=
  f D g C E (Classical.choose (hExact m.1 m.2))

include h3 hg in
theorem chi_difference (a : Charge D) :
    chi D g C E hExact (differenceCharge D g h3 a) = f D g C E a := by
  unfold chi
  apply f_congr D g h3 hg C E
  exact Classical.choose_spec (hExact (d D g a) (norm_difference D g h3 a))

include h3 hg in
theorem chi_zero : chi D g C E hExact 0 = 1 := by
  have h : differenceCharge D g h3 0 = (0 : Moving D g) :=
    Subtype.ext (map_zero (d D g))
  rw [← h, chi_difference D g h3 hg, f_fixed D g C E 0 (map_zero g)]

include h3 hg in
theorem chi_mul (m n : Moving D g) :
    chi D g C E hExact m * chi D g C E hExact n =
      C.c m.1 n.1 * chi D g C E hExact (m + n) := by
  obtain ⟨a, ha⟩ := hExact m.1 m.2
  obtain ⟨b, hb⟩ := hExact n.1 n.2
  have hm : differenceCharge D g h3 a = m := Subtype.ext ha
  have hn : differenceCharge D g h3 b = n := Subtype.ext hb
  have hmn : differenceCharge D g h3 (a + b) = m + n := by
    apply Subtype.ext
    change d D g (a + b) = m.1 + n.1
    rw [map_add, ha, hb]
  rw [← hmn, ← hm, ← hn, chi_difference D g h3 hg, chi_difference D g h3 hg,
    chi_difference D g h3 hg]
  exact f_mul D g h3 hg C E a b

/-- A set section on the integral momentum index. -/
structure MomentumSection where
  lift : Momentum D g → Charge D
  right_inv : ∀ p, N D g (lift p) = p.1

def chooseSection : MomentumSection D g where
  lift p := Classical.choose (show ∃ a, N D g a = p.1 from p.2)
  right_inv p := Classical.choose_spec (show ∃ a, N D g a = p.1 from p.2)

def shift (a : Charge D) (p : Momentum D g) : Momentum D g :=
  p + (N D g).rangeRestrict a

theorem shift_add (a b : Charge D) (p : Momentum D g) :
    shift D g a (shift D g b p) = shift D g (a + b) p := by
  simp only [shift, map_add]
  abel

theorem shift_moving (m : Moving D g) (p : Momentum D g) : shift D g m.1 p = p := by
  apply Subtype.ext
  change p.1 + N D g m.1 = p.1
  rw [show N D g m.1 = 0 from m.2, add_zero]

variable (s : MomentumSection D g)

def sectionDifference (a : Charge D) (p : Momentum D g) : Moving D g :=
  ⟨a + s.lift p - s.lift (shift D g a p), by
    change N D g (a + s.lift p - s.lift (shift D g a p)) = 0
    rw [map_sub, map_add, s.right_inv, s.right_inv]
    change N D g a + p.1 - (p.1 + N D g a) = 0
    abel⟩

private theorem section_decompose (a : Charge D) (p : Momentum D g) :
    a + s.lift p = s.lift (shift D g a p) + (sectionDifference D g s a p).1 := by
  change _ = s.lift (shift D g a p) + (a + s.lift p - s.lift (shift D g a p))
  abel

private theorem sectionDifference_add (a b : Charge D) (p : Momentum D g) :
    sectionDifference D g s (a + b) p =
      sectionDifference D g s a (shift D g b p) + sectionDifference D g s b p := by
  apply Subtype.ext
  change a + b + s.lift p - s.lift (shift D g (a + b) p) =
    (a + s.lift (shift D g b p) - s.lift (shift D g a (shift D g b p))) +
      (b + s.lift p - s.lift (shift D g b p))
  rw [shift_add D g a b p]
  abel

def coefficient (a : Charge D) (p : Momentum D g) : ℂˣ :=
  C.c a (s.lift p) * (C.c (s.lift (shift D g a p)) (sectionDifference D g s a p).1)⁻¹ *
    chi D g C E hExact (sectionDifference D g s a p)

include h3 hg in
theorem coefficient_mul (a b : Charge D) (p : Momentum D g) :
    coefficient D g C E hExact s b p * coefficient D g C E hExact s a (shift D g b p) =
      C.c a b * coefficient D g C E hExact s (a + b) p := by
  let r := shift D g b p
  let t := shift D g a r
  let u := s.lift p
  let v := s.lift r
  let w := s.lift t
  let e := sectionDifference D g s b p
  let m := sectionDifference D g s a r
  have hFirst : C.c a (b + u) = C.c a v * C.c (a + v) e.1 / C.c v e.1 := by
    rw [show b + u = v + e.1 from section_decompose D g s b p, eq_div_iff_mul_eq']
    exact (mul_comm _ _).trans (C.cocycle a v e.1).symm
  have hSecond : C.c (a + v) e.1 = C.c m.1 e.1 * C.c w (m.1 + e.1) / C.c w m.1 := by
    rw [show a + v = w + m.1 from section_decompose D g s a r, eq_div_iff_mul_eq']
    exact (mul_comm _ _).trans (C.cocycle w m.1 e.1)
  calc
    _ = (C.c b u * (C.c v e.1)⁻¹ * chi D g C E hExact e) *
        (C.c a v * (C.c w m.1)⁻¹ * chi D g C E hExact m) := rfl
    _ = C.c b u * C.c a (b + u) * (C.c w (m.1 + e.1))⁻¹ * chi D g C E hExact (m + e) := by
      calc
        _ = C.c b u * (C.c a v / (C.c v e.1 * C.c w m.1)) *
            (chi D g C E hExact m * chi D g C E hExact e) := by
          apply Additive.ofMul.injective
          simp only [ofMul_mul, ofMul_div, ofMul_inv]
          abel
        _ = _ := by
          rw [hFirst, hSecond, chi_mul D g h3 hg]
          apply Additive.ofMul.injective
          simp only [ofMul_mul, ofMul_div, ofMul_inv]
          abel
    _ = _ := by
      rw [← C.cocycle a b u]
      simp only [coefficient, sectionDifference_add, ← shift_add D g a b p, mul_assoc]
      rfl

/-- The twisted ground space over the rescaled lattice of fixed momenta. -/
abbrev Ground := Momentum D g →₀ ℂ

def U (a : Charge D) : Module.End ℂ (Ground D g) :=
  Finsupp.lsum ℂ fun p =>
    (coefficient D g C E hExact s a p : ℂ) • Finsupp.lsingle (shift D g a p)

theorem U_single (a : Charge D) (p : Momentum D g) (z : ℂ) :
    U D g C E hExact s a (Finsupp.single p z) =
      (coefficient D g C E hExact s a p : ℂ) • Finsupp.single (shift D g a p) z := by
  simp only [U, Finsupp.lsum_single, LinearMap.smul_apply, Finsupp.lsingle_apply]

include h3 hg in
theorem U_zero : U D g C E hExact s 0 = LinearMap.id := by
  apply Finsupp.lhom_ext
  intro p z
  have hShift : shift D g 0 p = p := by simp [shift]
  have hDiff : sectionDifference D g s 0 p = 0 := by
    apply Subtype.ext
    change 0 + s.lift p - s.lift (shift D g 0 p) = 0
    rw [hShift, zero_add, sub_self]
  simp only [U_single, LinearMap.id_apply, coefficient, hDiff, hShift,
    AddSubgroup.coe_zero, C.zero_mul, C.mul_zero, chi_zero D g h3 hg, inv_one, mul_one,
    Units.val_one, one_smul]

include h3 hg in
/-- The twisted group algebra relation (4.42) on the whole finite-support carrier. -/
theorem U_comp (a b : Charge D) :
    (U D g C E hExact s a).comp (U D g C E hExact s b) =
      (C.c a b : ℂ) • U D g C E hExact s (a + b) := by
  apply Finsupp.lhom_ext
  intro p z
  simp only [LinearMap.comp_apply, LinearMap.smul_apply, U_single, map_smul, smul_smul,
    ← Units.val_mul, shift_add, coefficient_mul D g h3 hg]

include h3 hg in
/-- On the momentum of p, the difference charge acts by the scalar of (4.46).
The integer representative of that momentum is the orbit norm of the section. -/
theorem U_difference_single (a : Charge D) (p : Momentum D g) (z : ℂ) :
    U D g C E hExact s (d D g a) (Finsupp.single p z) =
      (fAt D g C E a (s.lift p) : ℂ) • Finsupp.single p z := by
  have hShift : shift D g (d D g a) p = p :=
    shift_moving D g (differenceCharge D g h3 a) p
  have hDiff : sectionDifference D g s (d D g a) p = differenceCharge D g h3 a := by
    apply Subtype.ext
    change d D g a + s.lift p - s.lift (shift D g (d D g a) p) = d D g a
    rw [hShift, add_sub_cancel_right]
  have hCoeff : coefficient D g C E hExact s (d D g a) p = fAt D g C E a (s.lift p) := by
    unfold coefficient fAt
    rw [hDiff, hShift, chi_difference D g h3 hg]
    calc
      _ = (C.c (d D g a) (s.lift p) / C.c (s.lift p) (d D g a)) * f D g C E a := by
        rw [div_eq_mul_inv]
        rfl
      _ = _ := by
        rw [C.commutator]
        exact mul_comm _ _
  rw [U_single, hCoeff, hShift]

end

end D5.S3.VertexAlgebra.Lattice.Orbifold.ThirdTwistedChargeAction
