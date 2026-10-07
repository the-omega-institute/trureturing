/- GID: D5/S3/ArithUnits/Gardam
   generality: G
   mirror-B: D5/B/S3/ArithUnits/Gardam
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Algebra.Field.ZMod, mathlib/module/Mathlib.Algebra.MonoidAlgebra.MapDomain, mathlib/module/Mathlib.GroupTheory.PresentedGroup]
   utility: none
   digest: Gardam's explicit nontrivial unit in the exact Promislow group ring over ZMod 2, with torsion-free presentation and faithful four-coset transport. -/

/-
proof_shape: content
escape_witness: the public suppliers `presented_torsion_free`, `official_isUnit`,
  and `official_not_basis` depend on the explicit four-coset group construction,
  the faithful normalEquiv, the two-sided inverse certificate, and the 21-element
  support computation.  These are live proof paths, not wrappers around a pinned
  theorem.
admission_basis: escape-witness
source: accepted public source commit 92adfe225bb26dfed06f5ba77d9abbb7f680733f
literature: Giles Gardam, A counterexample to the unit conjecture for group rings,
  Annals of Mathematics 194 (3) (2021), arXiv:2102.11818v2,
  DOI 10.4007/annals.2021.194.3.9
-/

import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.MonoidAlgebra.Defs
import Mathlib.GroupTheory.PresentedGroup
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.MonoidAlgebra.MapDomain
import Mathlib.Tactic.Group
import Mathlib.Algebra.Group.Commute.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Abel

/-!
# Gardam's counterexample to the unit conjecture for group rings

This module is a native Lean 4.33 transplantation of the accepted public
proof source from trureturning-lean-eval commit
`92adfe225bb26dfed06f5ba77d9abbb7f680733f` (Apache-2.0).  The mathematical
source is Giles Gardam, *A counterexample to the unit conjecture for group
rings*, Annals of Mathematics 194 (3) (2021), arXiv:2102.11818v2,
DOI 10.4007/annals.2021.194.3.9.  This repository implementation claims no
new counterexample.

The definitions below reproduce the official PresentedGroup and its
\(\mathbb F_2\)-group-ring element exactly.  The proof supplies a faithful
four-coset normal form, torsion freeness, Gardam's explicit two-sided inverse,
non-basis support, and transport back to the presented group.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.ArithUnits.Gardam

namespace UnitConjecture

/-- The two generators of the group `P` defined in Theorem A of the paper. -/
inductive generators where
  | a
  | b

/-- The first generator of the group `P` defined in Theorem A of the paper. -/
def a : FreeGroup generators := .of generators.a

/-- The second generator of the group `P` defined in Theorem A of the paper. -/
def b : FreeGroup generators := .of generators.b

/-- The relations defining the group `P` defined in Theorem A of the paper. -/
def relations : Set (FreeGroup generators) :=
  {b⁻¹ * a ^ 2 * b * a ^ 2, a⁻¹ * b ^ 2 * a * b ^ 2}

/-- The group `P` defined in Theorem A of the paper. -/
def P := PresentedGroup relations
deriving Coe (FreeGroup generators), Group

/-- The element `x` defined in Theorem A of the paper. -/
def x : P := a ^ 2

/-- The element `y` defined in Theorem A of the paper. -/
def y : P := b ^ 2

/-- The element `z` defined in Theorem A of the paper. -/
def z : P := (a * b) ^ 2

/-- The group ring `𝔽₂[P]` defined in Theorem A of the paper. -/
abbrev R := MonoidAlgebra (ZMod 2) P

instance : Coe P R where
  coe := MonoidAlgebra.of (ZMod 2) P

/-- The element `p` defined in Theorem A of the paper. -/
def p : R := (1 + x) * (1 + y) * (1 + z⁻¹)

/-- The element `q` defined in Theorem A of the paper. -/
def q : R := x⁻¹ * y⁻¹ + x + y⁻¹ * z + z

/-- The element `r` defined in Theorem A of the paper. -/
def r : R := 1 + x + y⁻¹ * z + x * y * z

/-- The element `s` defined in Theorem A of the paper. -/
def s : R := 1 + (x + x⁻¹ + y + y⁻¹) * z⁻¹

/-- The nontrivial unit defined in Theorem A of the paper. -/
def u : R := p + q * a + r * b + s * (a * b)

end UnitConjecture


/-!
Explicit four-coset model for the Promislow presentation.
The action and factor set are those of Gardam, arXiv:2102.11818v2, §3.1.
This submission dependency makes no claim of new mathematical content.
-/

namespace Promislow

inductive Coset where
  | one | a | b | ab
  deriving DecidableEq, Repr

open Coset

def addQ : Coset → Coset → Coset
  | one, r => r
  | a, one => a | a, a => one | a, b => ab | a, ab => b
  | b, one => b | b, a => ab | b, b => one | b, ab => a
  | ab, one => ab | ab, a => b | ab, b => a | ab, ab => one

structure Vec where
  x : ℤ
  y : ℤ
  z : ℤ
  deriving DecidableEq, Repr

@[ext] theorem Vec.ext (v w : Vec) (hx : v.x = w.x) (hy : v.y = w.y)
    (hz : v.z = w.z) : v = w := by
  cases v; cases w; cases hx; cases hy; cases hz; rfl

def zeroV : Vec := ⟨0, 0, 0⟩
def addV (v w : Vec) : Vec := ⟨v.x + w.x, v.y + w.y, v.z + w.z⟩
def negV (v : Vec) : Vec := ⟨-v.x, -v.y, -v.z⟩
def rho : Coset → Vec → Vec
  | one, v => v
  | a, v => ⟨v.x, -v.y, -v.z⟩
  | b, v => ⟨-v.x, v.y, -v.z⟩
  | ab, v => ⟨-v.x, -v.y, v.z⟩

def factor : Coset → Coset → Vec
  | one, _ => zeroV
  | _, one => zeroV
  | a, a => ⟨1, 0, 0⟩
  | a, b => zeroV
  | a, ab => ⟨1, 0, 0⟩
  | b, a => ⟨-1, 1, -1⟩
  | b, b => ⟨0, 1, 0⟩
  | b, ab => ⟨-1, 0, -1⟩
  | ab, a => ⟨0, -1, 1⟩
  | ab, b => ⟨0, -1, 0⟩
  | ab, ab => ⟨0, 0, 1⟩

theorem rho_add (q : Coset) (v w : Vec) :
    rho q (addV v w) = addV (rho q v) (rho q w) := by
  cases q <;> apply Vec.ext <;> simp [rho, addV] <;> omega

theorem rho_comp (q r : Coset) (v : Vec) :
    rho (addQ q r) v = rho q (rho r v) := by
  cases q <;> cases r <;> apply Vec.ext <;> simp [rho, addQ]

theorem factor_cocycle (q r s : Coset) :
    addV (factor q r) (factor (addQ q r) s) =
      addV (rho q (factor r s)) (factor q (addQ r s)) := by
  cases q <;> cases r <;> cases s <;> decide

structure E where
  v : Vec
  q : Coset
  deriving DecidableEq, Repr

@[ext] theorem E.ext (g h : E) (hv : g.v = h.v) (hq : g.q = h.q) : g = h := by
  cases g; cases h; cases hv; cases hq; rfl

def mulE (g h : E) : E :=
  ⟨addV (addV g.v (rho g.q h.v)) (factor g.q h.q), addQ g.q h.q⟩
def oneE : E := ⟨zeroV, one⟩
def invE (g : E) : E := ⟨negV (rho g.q (addV g.v (factor g.q g.q))), g.q⟩

instance : Group E where
  mul := mulE
  one := oneE
  inv := invE
  mul_assoc g h k := by
    change mulE (mulE g h) k = mulE g (mulE h k)
    rcases g with ⟨v, q⟩; rcases h with ⟨w, r⟩; rcases k with ⟨t, s⟩
    cases q <;> cases r <;> cases s <;> apply E.ext
    all_goals first
      | rfl
      | apply Vec.ext <;> (try simp only [mulE, addV, rho, factor, zeroV, addQ]) <;> omega
  one_mul g := by
    change mulE oneE g = g
    rcases g with ⟨v, q⟩; cases q <;> apply E.ext
    all_goals first | rfl | apply Vec.ext <;> simp [mulE, oneE, addV, rho, factor, zeroV, addQ]
  mul_one g := by
    change mulE g oneE = g
    rcases g with ⟨v, q⟩; cases q <;> apply E.ext
    all_goals first | rfl | apply Vec.ext <;> simp [mulE, oneE, addV, rho, factor, zeroV, addQ]
  inv_mul_cancel g := by
    change mulE (invE g) g = oneE
    rcases g with ⟨v, q⟩; cases q <;> apply E.ext
    all_goals first
      | rfl
      | apply Vec.ext <;> simp [mulE, invE, oneE, addV, negV, rho, factor, zeroV, addQ]

@[simp] theorem mul_def (g h : E) : g * h = mulE g h := rfl
@[simp] theorem one_def : (1 : E) = oneE := rfl
@[simp] theorem inv_def (g : E) : g⁻¹ = invE g := rfl

def ea : E := ⟨zeroV, a⟩
def eb : E := ⟨zeroV, b⟩

theorem relation_a : eb⁻¹ * ea ^ 2 * eb * ea ^ 2 = 1 := by
  decide

theorem relation_b : ea⁻¹ * eb ^ 2 * ea * eb ^ 2 = 1 := by
  decide

def generatorImage : UnitConjecture.generators → E
  | .a => ea
  | .b => eb

theorem relations_satisfied (w : FreeGroup UnitConjecture.generators)
    (hw : w ∈ UnitConjecture.relations) : FreeGroup.lift generatorImage w = 1 := by
  simp only [UnitConjecture.relations, Set.mem_insert_iff, Set.mem_singleton_iff] at hw
  rcases hw with rfl | rfl
  · simpa [map_mul, map_inv, map_pow, UnitConjecture.a, UnitConjecture.b,
      generatorImage] using relation_a
  · simpa [map_mul, map_inv, map_pow, UnitConjecture.a, UnitConjecture.b,
      generatorImage] using relation_b

/-- This homomorphism satisfies the presentation; injectivity is a separate obligation. -/
def encode : UnitConjecture.P →* E := PresentedGroup.toGroup relations_satisfied

def scaleV (n : ℕ) (v : Vec) : Vec := ⟨n * v.x, n * v.y, n * v.z⟩

theorem translation_pow (v : Vec) (n : ℕ) :
    (⟨v, one⟩ : E) ^ n = ⟨scaleV n v, one⟩ := by
  induction n with
  | zero =>
    apply E.ext
    · apply Vec.ext <;> simp [scaleV, oneE, zeroV]
    · rfl
  | succ n ih =>
    rw [pow_succ, ih]
    apply E.ext
    · apply Vec.ext <;>
        simp [mul_def, mulE, scaleV, addV, factor, rho, zeroV, Nat.cast_add, add_mul]
    · rfl

theorem translation_torsion (v : Vec) (n : ℕ) (hn : n ≠ 0)
    (h : (⟨v, one⟩ : E) ^ n = 1) : v = zeroV := by
  rw [translation_pow] at h
  have hv := congrArg E.v h
  have hnz : (n : ℤ) ≠ 0 := by simpa using hn
  apply Vec.ext
  · have hx := congrArg Vec.x hv
    exact (mul_eq_zero.mp hx).resolve_left hnz
  · have hy := congrArg Vec.y hv
    exact (mul_eq_zero.mp hy).resolve_left hnz
  · have hz := congrArg Vec.z hv
    exact (mul_eq_zero.mp hz).resolve_left hnz

theorem square_coset (g : E) : (g ^ 2).q = one := by
  rcases g with ⟨v, q⟩
  cases q <;> rfl

theorem square_eq_one (g : E) (h : g ^ 2 = 1) : g = 1 := by
  rcases g with ⟨v, q⟩
  cases q
  · have hv := congrArg E.v h
    apply E.ext
    · apply Vec.ext
      · have hx := congrArg Vec.x hv
        simp [pow_two, mul_def, one_def, mulE, oneE, addV, rho, factor, zeroV] at hx ⊢
        omega
      · have hy := congrArg Vec.y hv
        simp [pow_two, mul_def, one_def, mulE, oneE, addV, rho, factor, zeroV] at hy ⊢
        omega
      · have hz := congrArg Vec.z hv
        simp [pow_two, mul_def, one_def, mulE, oneE, addV, rho, factor, zeroV] at hz ⊢
        omega
    · rfl
  · have hx := congrArg (fun g : E => g.v.x) h
    simp [pow_two, mul_def, one_def, mulE, oneE, addV, rho, factor, zeroV] at hx
    omega
  · have hy := congrArg (fun g : E => g.v.y) h
    simp [pow_two, mul_def, one_def, mulE, oneE, addV, rho, factor, zeroV] at hy
    omega
  · have hz := congrArg (fun g : E => g.v.z) h
    simp [pow_two, mul_def, one_def, mulE, oneE, addV, rho, factor, zeroV] at hz
    omega

theorem torsion_free (g : E) (n : ℕ) (hn : n ≠ 0) (h : g ^ n = 1) : g = 1 := by
  have hs : (g ^ 2) ^ n = 1 := by
    rw [← pow_mul, Nat.mul_comm 2 n, pow_mul, h, one_pow]
  have hc := square_coset g
  have he : g ^ 2 = ⟨(g ^ 2).v, one⟩ := E.ext _ _ rfl hc
  rw [he] at hs
  have hv := translation_torsion _ n hn hs
  apply square_eq_one g
  rw [he, hv]
  rfl

def scaleZ (i : ℤ) (v : Vec) : Vec := ⟨i * v.x, i * v.y, i * v.z⟩

theorem translation_zpow (v : Vec) (i : ℤ) :
    (⟨v, one⟩ : E) ^ i = ⟨scaleZ i v, one⟩ := by
  cases i with
  | ofNat n => simpa [scaleV, scaleZ] using translation_pow v n
  | negSucc n =>
    rw [zpow_negSucc, translation_pow]
    apply E.ext
    · apply Vec.ext <;>
        simp [inv_def, invE, negV, rho, addV, factor, zeroV, scaleV, scaleZ,
          Int.negSucc_eq, add_mul]
    · rfl

end Promislow


/-! Presentation calculations for Gardam's §3.1 normal form. -/

namespace Promislow

noncomputable section

abbrev pa : UnitConjecture.P := PresentedGroup.of UnitConjecture.generators.a
abbrev pb : UnitConjecture.P := PresentedGroup.of UnitConjecture.generators.b
abbrev px : UnitConjecture.P := pa ^ 2
abbrev py : UnitConjecture.P := pb ^ 2
abbrev pz : UnitConjecture.P := (pa * pb) ^ 2

theorem presentation_x : pb⁻¹ * px * pb = px⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  change PresentedGroup.mk UnitConjecture.relations
    (UnitConjecture.b⁻¹ * UnitConjecture.a ^ 2 * UnitConjecture.b * UnitConjecture.a ^ 2) = 1
  exact PresentedGroup.one_of_mem (by simp [UnitConjecture.relations])

theorem presentation_y : pa⁻¹ * py * pa = py⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  change PresentedGroup.mk UnitConjecture.relations
    (UnitConjecture.a⁻¹ * UnitConjecture.b ^ 2 * UnitConjecture.a * UnitConjecture.b ^ 2) = 1
  exact PresentedGroup.one_of_mem (by simp [UnitConjecture.relations])

theorem inverse_conjugation {G : Type*} [Group G] (g t : G)
    (h : t⁻¹ * g * t = g⁻¹) : t * g * t⁻¹ = g⁻¹ := by
  have hi := congrArg Inv.inv h
  simp only [mul_inv_rev, inv_inv, ← mul_assoc] at hi
  calc
    t * g * t⁻¹ = t * (t⁻¹ * g⁻¹ * t) * t⁻¹ := by rw [hi]
    _ = g⁻¹ := by group

theorem inversion_commutes_square {G : Type*} [Group G] (g t : G)
    (h : t⁻¹ * g * t = g⁻¹) : Commute g (t ^ 2) := by
  have hl := inverse_conjugation g t h
  have hc : t * (t * g * t⁻¹) * t⁻¹ = g := by
    rw [hl]
    have hi := congrArg Inv.inv hl
    simpa only [mul_inv_rev, inv_inv, ← mul_assoc] using hi
  change g * t ^ 2 = t ^ 2 * g
  calc
    g * t ^ 2 = (t * (t * g * t⁻¹) * t⁻¹) * t ^ 2 := by rw [hc]
    _ = t ^ 2 * g := by (try simp only [pow_two]); group

theorem commute_xy : Commute px py := inversion_commutes_square px pb presentation_x

theorem move_x_b : px * pb = pb * px⁻¹ := by
  apply (inv_mul_eq_iff_eq_mul).mp
  simpa only [mul_assoc] using presentation_x

theorem move_a_y : pa * py = py⁻¹ * pa := by
  exact (mul_inv_eq_iff_eq_mul).mp (inverse_conjugation py pa presentation_y)

theorem conjugate_z_a : pa⁻¹ * pz * pa = pz⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  calc
    pa⁻¹ * pz * pa * pz = pb * pa * pb * (px * pb) * pa * pb := by (try simp only [pow_two]); group
    _ = pb * pa * pb * (pb * px⁻¹) * pa * pb := by rw [move_x_b]
    _ = pb * (pa * py) * pa⁻¹ * pb := by (try simp only [pow_two]); group
    _ = pb * (py⁻¹ * pa) * pa⁻¹ * pb := by rw [move_a_y]
    _ = 1 := by (try simp only [pow_two]); group

theorem conjugate_z_b : pb⁻¹ * pz * pb = pz⁻¹ := by
  have hz : (pa * pb)⁻¹ * pz * (pa * pb) = pz := by (try simp only [pow_two]); group
  have ha := inverse_conjugation pz pa conjugate_z_a
  calc
    pb⁻¹ * pz * pb = (pa * pb)⁻¹ * (pa * pz * pa⁻¹) * (pa * pb) := by (try simp only [pow_two]); group
    _ = (pa * pb)⁻¹ * pz⁻¹ * (pa * pb) := by rw [ha]
    _ = ((pa * pb)⁻¹ * pz * (pa * pb))⁻¹ := by (try simp only [pow_two]); group
    _ = pz⁻¹ := by rw [hz]

theorem commute_xz : Commute px pz := by
  have h : Commute pz px := inversion_commutes_square pz pa conjugate_z_a
  exact h.symm

theorem commute_yz : Commute py pz := by
  have h : Commute pz py := inversion_commutes_square pz pb conjugate_z_b
  exact h.symm

end

end Promislow


/-! Reconstruction of the presented group from Gardam's four-coset model. -/

namespace Promislow

noncomputable section

open Coset

def transP (v : Vec) : UnitConjecture.P := px ^ v.x * py ^ v.y * pz ^ v.z

def sigma : Coset → UnitConjecture.P
  | one => 1 | a => pa | b => pb | ab => pa * pb

theorem transP_zero : transP zeroV = 1 := by simp [transP, zeroV]

theorem transP_add (v w : Vec) : transP (addV v w) = transP v * transP w := by
  symm
  calc
    transP v * transP w =
        (px ^ v.x * py ^ v.y) * (pz ^ v.z * px ^ w.x) * py ^ w.y * pz ^ w.z := by
      simp only [transP, mul_assoc]
    _ = (px ^ v.x * py ^ v.y) * (px ^ w.x * pz ^ v.z) * py ^ w.y * pz ^ w.z := by
      rw [(commute_xz.symm.zpow_zpow v.z w.x).eq]
    _ = (px ^ v.x * (py ^ v.y * px ^ w.x)) * (pz ^ v.z * py ^ w.y) * pz ^ w.z := by
      simp only [mul_assoc]
    _ = (px ^ v.x * (px ^ w.x * py ^ v.y)) * (py ^ w.y * pz ^ v.z) * pz ^ w.z := by
      rw [(commute_xy.symm.zpow_zpow v.y w.x).eq,
        (commute_yz.symm.zpow_zpow v.z w.y).eq]
    _ = transP (addV v w) := by simp only [transP, addV, zpow_add, mul_assoc]

theorem action_a (v : Vec) : pa * transP v = transP (rho a v) * pa := by
  have hx : SemiconjBy pa px px := (Commute.refl pa).pow_right 2
  have hy : SemiconjBy pa py py⁻¹ := move_a_y
  have hz : SemiconjBy pa pz pz⁻¹ :=
    (mul_inv_eq_iff_eq_mul).mp (inverse_conjugation pz pa conjugate_z_a)
  have h := ((hx.zpow_right v.x).mul_right (hy.zpow_right v.y)).mul_right
    (hz.zpow_right v.z)
  simpa only [transP, rho, inv_zpow', zpow_neg] using h.eq

theorem action_b (v : Vec) : pb * transP v = transP (rho b v) * pb := by
  have hx : SemiconjBy pb px px⁻¹ :=
    (mul_inv_eq_iff_eq_mul).mp (inverse_conjugation px pb presentation_x)
  have hy : SemiconjBy pb py py := (Commute.refl pb).pow_right 2
  have hz : SemiconjBy pb pz pz⁻¹ :=
    (mul_inv_eq_iff_eq_mul).mp (inverse_conjugation pz pb conjugate_z_b)
  have h := ((hx.zpow_right v.x).mul_right (hy.zpow_right v.y)).mul_right
    (hz.zpow_right v.z)
  simpa only [transP, rho, inv_zpow', zpow_neg] using h.eq

theorem section_action (q : Coset) (v : Vec) :
    sigma q * transP v = transP (rho q v) * sigma q := by
  cases q
  · simp [sigma, rho]
  · exact action_a v
  · exact action_b v
  · change (pa * pb) * transP v = transP (rho ab v) * (pa * pb)
    calc
      (pa * pb) * transP v = pa * (pb * transP v) := mul_assoc _ _ _
      _ = pa * (transP (rho b v) * pb) := by rw [action_b]
      _ = (pa * transP (rho b v)) * pb := (mul_assoc _ _ _).symm
      _ = (transP (rho a (rho b v)) * pa) * pb := by rw [action_a]
      _ = transP (rho ab v) * (pa * pb) := by simp [rho, mul_assoc]

theorem move_b_a : pb * pa = transP (factor b a) * sigma ab := by
  have hb : pb * px = px⁻¹ * pb :=
    (mul_inv_eq_iff_eq_mul).mp (inverse_conjugation px pb presentation_x)
  calc
    pb * pa = (pb * px) * pa⁻¹ := by (try simp only [pow_two]); group
    _ = (px⁻¹ * pb) * pa⁻¹ := by rw [hb]
    _ = transP (factor b a) * sigma ab := by
      simp only [transP, factor, sigma, zpow_neg_one, zpow_one, pow_two]
      group

theorem section_b_ab : sigma b * sigma ab = transP (factor b ab) * sigma a := by
  change pb * (pa * pb) = transP (factor b ab) * pa
  calc
    pb * (pa * pb) = (pb * pa) * pb := (mul_assoc _ _ _).symm
    _ = (transP (factor b a) * sigma ab) * pb := by rw [move_b_a]
    _ = transP (factor b a) * (pa * py) := by simp only [sigma, pow_two, mul_assoc]
    _ = transP (factor b a) * (py⁻¹ * pa) := by rw [move_a_y]
    _ = (transP (factor b a) * transP ⟨0, -1, 0⟩) * pa := by
      simp [transP, mul_assoc]
    _ = transP (addV (factor b a) ⟨0, -1, 0⟩) * pa := by rw [transP_add]
    _ = transP (factor b ab) * pa := rfl

theorem section_ab_a : sigma ab * sigma a = transP (factor ab a) * sigma b := by
  change (pa * pb) * pa = transP (factor ab a) * pb
  calc
    (pa * pb) * pa = pa * (pb * pa) := mul_assoc _ _ _
    _ = pa * (transP (factor b a) * sigma ab) := by rw [move_b_a]
    _ = (pa * transP (factor b a)) * sigma ab := (mul_assoc _ _ _).symm
    _ = (transP (rho a (factor b a)) * pa) * sigma ab := by rw [action_a]
    _ = transP (rho a (factor b a)) * (px * pb) := by simp only [sigma, pow_two, mul_assoc]
    _ = (transP (rho a (factor b a)) * transP ⟨1, 0, 0⟩) * pb := by
      simp [transP, mul_assoc]
    _ = transP (addV (rho a (factor b a)) ⟨1, 0, 0⟩) * pb := by rw [transP_add]
    _ = transP (factor ab a) * pb := rfl

theorem section_mul (q r : Coset) :
    sigma q * sigma r = transP (factor q r) * sigma (addQ q r) := by
  cases q <;> cases r
  all_goals first
    | exact move_b_a
    | exact section_b_ab
    | exact section_ab_a
    | simpa [sigma, factor, addQ, transP, zeroV, pow_two, mul_assoc] using move_a_y

def decodeFun (g : E) : UnitConjecture.P := transP g.v * sigma g.q

theorem decode_mul (g h : E) : decodeFun (g * h) = decodeFun g * decodeFun h := by
  rcases g with ⟨v, q⟩
  rcases h with ⟨w, r⟩
  symm
  calc
    decodeFun ⟨v, q⟩ * decodeFun ⟨w, r⟩ =
        transP v * (sigma q * transP w) * sigma r := by simp [decodeFun, mul_assoc]
    _ = transP v * (transP (rho q w) * sigma q) * sigma r := by rw [section_action]
    _ = (transP v * transP (rho q w)) * (sigma q * sigma r) := by simp only [mul_assoc]
    _ = transP (addV v (rho q w)) * (transP (factor q r) * sigma (addQ q r)) := by
      rw [← transP_add, section_mul]
    _ = decodeFun (⟨v, q⟩ * ⟨w, r⟩) := by
      simp only [decodeFun, mul_def, mulE, ← transP_add, ← mul_assoc]

def decode : E →* UnitConjecture.P where
  toFun := decodeFun
  map_one' := by simp [decodeFun, one_def, oneE, transP_zero, sigma]
  map_mul' := decode_mul

@[simp] theorem encode_a : encode pa = ea := PresentedGroup.toGroup.of relations_satisfied
@[simp] theorem encode_b : encode pb = eb := PresentedGroup.toGroup.of relations_satisfied

theorem encode_x : encode px = ⟨⟨1, 0, 0⟩, one⟩ := by
  rw [map_pow, encode_a]
  decide

theorem encode_y : encode py = ⟨⟨0, 1, 0⟩, one⟩ := by
  rw [map_pow, encode_b]
  decide

theorem encode_z : encode pz = ⟨⟨0, 0, 1⟩, one⟩ := by
  rw [map_pow, map_mul, encode_a, encode_b]
  decide

theorem encode_trans (v : Vec) : encode (transP v) = ⟨v, one⟩ := by
  simp only [transP, map_mul, map_zpow, encode_x, encode_y, encode_z, translation_zpow,
    mul_def]
  apply E.ext
  · apply Vec.ext <;> simp [mulE, addV, rho, factor, zeroV, scaleZ, addQ]
  · rfl

theorem encode_section (q : Coset) : encode (sigma q) = ⟨zeroV, q⟩ := by
  cases q <;> simp [sigma, ea, eb, mulE, rho, addV, zeroV, factor, addQ, oneE]

theorem decode_encode (g : UnitConjecture.P) : decode (encode g) = g := by
  have h : decode.comp encode = MonoidHom.id UnitConjecture.P := by
    apply PresentedGroup.ext
    intro t
    change decode (encode (PresentedGroup.of t)) = PresentedGroup.of t
    cases t
    · change decode (encode pa) = pa
      rw [encode_a]
      change transP zeroV * sigma a = pa
      simp [transP_zero, sigma]
    · change decode (encode pb) = pb
      rw [encode_b]
      change transP zeroV * sigma b = pb
      simp [transP_zero, sigma]
  exact DFunLike.congr_fun h g

theorem encode_decode (g : E) : encode (decode g) = g := by
  change encode (transP g.v * sigma g.q) = g
  rw [map_mul, encode_trans, encode_section, mul_def]
  rcases g with ⟨v, q⟩
  cases q <;> apply E.ext
  all_goals first | rfl | apply Vec.ext <;> simp [mulE, rho, addV, zeroV, factor, addQ]

/-- Both inverse identities certify faithfulness of the four-coset coordinates. -/
def normalEquiv : UnitConjecture.P ≃* E where
  toFun := encode
  invFun := decode
  left_inv := decode_encode
  right_inv := encode_decode
  map_mul' := encode.map_mul

theorem presented_torsion_free (g : UnitConjecture.P) (n : ℕ) (hn : n ≠ 0)
    (h : g ^ n = 1) : g = 1 := by
  apply normalEquiv.injective
  apply torsion_free (encode g) n hn
  simpa only [map_pow, map_one] using congrArg encode h

end

end Promislow


/-! Gardam's explicit inverse, checked over the four-coset group model. -/

namespace Promislow

noncomputable section

abbrev RE := MonoidAlgebra (ZMod 2) E

def basis (g : E) : RE := MonoidAlgebra.single g 1

def ex : E := ⟨⟨1, 0, 0⟩, .one⟩
def ey : E := ⟨⟨0, 1, 0⟩, .one⟩
def ez : E := ⟨⟨0, 0, 1⟩, .one⟩

def polyP : RE := (1 + basis ex) * (1 + basis ey) * (1 + basis ez⁻¹)
def polyQ : RE := basis ex⁻¹ * basis ey⁻¹ + basis ex + basis ey⁻¹ * basis ez + basis ez
def polyR : RE := 1 + basis ex + basis ey⁻¹ * basis ez + basis ex * basis ey * basis ez
def polyS : RE := 1 + (basis ex + basis ex⁻¹ + basis ey + basis ey⁻¹) * basis ez⁻¹

def unitE : RE := polyP + polyQ * basis ea + polyR * basis eb + polyS * basis (ea * eb)

def vOne : RE := basis ex⁻¹ * (basis ea⁻¹ * polyP * basis ea)
def vA : RE := (basis ex⁻¹ * polyQ) * basis ea
def vB : RE := (basis ey⁻¹ * polyR) * basis eb
def vAB : RE := (basis ez⁻¹ * (basis ea⁻¹ * polyS * basis ea)) * basis (ea * eb)
def uA : RE := polyQ * basis ea
def uB : RE := polyR * basis eb
def uAB : RE := polyS * basis (ea * eb)

def inverseE : RE := vOne + vA + vB + vAB

theorem left_coefficient_0 : vOne * polyP + vA * uA + vB * uB + vAB * uAB = 1 := by
  classical
  simp only [vOne, vA, vB, vAB, uA, uB, uAB, polyP, polyQ, polyR, polyS, basis,
    mul_add, add_mul, mul_one, one_mul, MonoidAlgebra.single_mul_single]
  ext g
  simp only [MonoidAlgebra.coeff_add, MonoidAlgebra.coeff_single,
    MonoidAlgebra.one_def, MonoidAlgebra.coeff_zero, Finsupp.add_apply, Finsupp.single_apply,
    Finsupp.zero_apply, mul_def, inv_def, one_def, mulE, invE, oneE,
    ex, ey, ez, ea, eb, rho, factor, addQ, addV, negV, zeroV]
  ring_nf
  simp [show (2 : ZMod 2) = 0 from by decide,
    show (4 : ZMod 2) = 0 from by decide,
    show (6 : ZMod 2) = 0 from by decide,
    show (8 : ZMod 2) = 0 from by decide,
    show (10 : ZMod 2) = 0 from by decide,
    show (12 : ZMod 2) = 0 from by decide,
    show (14 : ZMod 2) = 0 from by decide,
    show (16 : ZMod 2) = 0 from by decide,
    show (17 : ZMod 2) = 1 from by decide]

theorem left_coefficient_1 : vOne * uA + vA * polyP + vB * uAB + vAB * uB = 0 := by
  classical
  simp only [vOne, vA, vB, vAB, uA, uB, uAB, polyP, polyQ, polyR, polyS, basis,
    mul_add, add_mul, mul_one, one_mul, MonoidAlgebra.single_mul_single]
  ext g
  simp only [MonoidAlgebra.coeff_add, MonoidAlgebra.coeff_single,
    MonoidAlgebra.one_def, MonoidAlgebra.coeff_zero, Finsupp.add_apply, Finsupp.single_apply,
    Finsupp.zero_apply, mul_def, inv_def, one_def, mulE, invE, oneE,
    ex, ey, ez, ea, eb, rho, factor, addQ, addV, negV, zeroV]
  ring_nf
  simp [show (2 : ZMod 2) = 0 from by decide,
    show (4 : ZMod 2) = 0 from by decide,
    show (6 : ZMod 2) = 0 from by decide,
    show (8 : ZMod 2) = 0 from by decide,
    show (10 : ZMod 2) = 0 from by decide,
    show (12 : ZMod 2) = 0 from by decide,
    show (14 : ZMod 2) = 0 from by decide,
    show (16 : ZMod 2) = 0 from by decide,
    show (17 : ZMod 2) = 1 from by decide]

theorem left_coefficient_2 : vOne * uB + vA * uAB + vB * polyP + vAB * uA = 0 := by
  classical
  simp only [vOne, vA, vB, vAB, uA, uB, uAB, polyP, polyQ, polyR, polyS, basis,
    mul_add, add_mul, mul_one, one_mul, MonoidAlgebra.single_mul_single]
  ext g
  simp only [MonoidAlgebra.coeff_add, MonoidAlgebra.coeff_single,
    MonoidAlgebra.one_def, MonoidAlgebra.coeff_zero, Finsupp.add_apply, Finsupp.single_apply,
    Finsupp.zero_apply, mul_def, inv_def, one_def, mulE, invE, oneE,
    ex, ey, ez, ea, eb, rho, factor, addQ, addV, negV, zeroV]
  ring_nf
  simp [show (2 : ZMod 2) = 0 from by decide,
    show (4 : ZMod 2) = 0 from by decide,
    show (6 : ZMod 2) = 0 from by decide,
    show (8 : ZMod 2) = 0 from by decide,
    show (10 : ZMod 2) = 0 from by decide,
    show (12 : ZMod 2) = 0 from by decide,
    show (14 : ZMod 2) = 0 from by decide,
    show (16 : ZMod 2) = 0 from by decide,
    show (17 : ZMod 2) = 1 from by decide]

theorem left_coefficient_3 : vOne * uAB + vA * uB + vB * uA + vAB * polyP = 0 := by
  classical
  simp only [vOne, vA, vB, vAB, uA, uB, uAB, polyP, polyQ, polyR, polyS, basis,
    mul_add, add_mul, mul_one, one_mul, MonoidAlgebra.single_mul_single]
  ext g
  simp only [MonoidAlgebra.coeff_add, MonoidAlgebra.coeff_single,
    MonoidAlgebra.one_def, MonoidAlgebra.coeff_zero, Finsupp.add_apply, Finsupp.single_apply,
    Finsupp.zero_apply, mul_def, inv_def, one_def, mulE, invE, oneE,
    ex, ey, ez, ea, eb, rho, factor, addQ, addV, negV, zeroV]
  ring_nf
  simp [show (2 : ZMod 2) = 0 from by decide,
    show (4 : ZMod 2) = 0 from by decide,
    show (6 : ZMod 2) = 0 from by decide,
    show (8 : ZMod 2) = 0 from by decide,
    show (10 : ZMod 2) = 0 from by decide,
    show (12 : ZMod 2) = 0 from by decide,
    show (14 : ZMod 2) = 0 from by decide,
    show (16 : ZMod 2) = 0 from by decide,
    show (17 : ZMod 2) = 1 from by decide]

theorem inverseE_mul : inverseE * unitE = 1 := by
  calc
    inverseE * unitE = (vOne * polyP + vA * uA + vB * uB + vAB * uAB) + (vOne * uA + vA * polyP + vB * uAB + vAB * uB) + (vOne * uB + vA * uAB + vB * polyP + vAB * uA) + (vOne * uAB + vA * uB + vB * uA + vAB * polyP) := by
      simp only [inverseE, unitE, uA, uB, uAB, mul_add, add_mul]
      abel
    _ = 1 := by rw [left_coefficient_0, left_coefficient_1, left_coefficient_2, left_coefficient_3]; simp

theorem right_coefficient_0 : polyP * vOne + uA * vA + uB * vB + uAB * vAB = 1 := by
  classical
  simp only [vOne, vA, vB, vAB, uA, uB, uAB, polyP, polyQ, polyR, polyS, basis,
    mul_add, add_mul, mul_one, one_mul, MonoidAlgebra.single_mul_single]
  ext g
  simp only [MonoidAlgebra.coeff_add, MonoidAlgebra.coeff_single,
    MonoidAlgebra.one_def, MonoidAlgebra.coeff_zero, Finsupp.add_apply, Finsupp.single_apply,
    Finsupp.zero_apply, mul_def, inv_def, one_def, mulE, invE, oneE,
    ex, ey, ez, ea, eb, rho, factor, addQ, addV, negV, zeroV]
  ring_nf
  simp [show (2 : ZMod 2) = 0 from by decide,
    show (4 : ZMod 2) = 0 from by decide,
    show (6 : ZMod 2) = 0 from by decide,
    show (8 : ZMod 2) = 0 from by decide,
    show (10 : ZMod 2) = 0 from by decide,
    show (12 : ZMod 2) = 0 from by decide,
    show (14 : ZMod 2) = 0 from by decide,
    show (16 : ZMod 2) = 0 from by decide,
    show (17 : ZMod 2) = 1 from by decide]

theorem right_coefficient_1 : polyP * vA + uA * vOne + uB * vAB + uAB * vB = 0 := by
  classical
  simp only [vOne, vA, vB, vAB, uA, uB, uAB, polyP, polyQ, polyR, polyS, basis,
    mul_add, add_mul, mul_one, one_mul, MonoidAlgebra.single_mul_single]
  ext g
  simp only [MonoidAlgebra.coeff_add, MonoidAlgebra.coeff_single,
    MonoidAlgebra.one_def, MonoidAlgebra.coeff_zero, Finsupp.add_apply, Finsupp.single_apply,
    Finsupp.zero_apply, mul_def, inv_def, one_def, mulE, invE, oneE,
    ex, ey, ez, ea, eb, rho, factor, addQ, addV, negV, zeroV]
  ring_nf
  simp [show (2 : ZMod 2) = 0 from by decide,
    show (4 : ZMod 2) = 0 from by decide,
    show (6 : ZMod 2) = 0 from by decide,
    show (8 : ZMod 2) = 0 from by decide,
    show (10 : ZMod 2) = 0 from by decide,
    show (12 : ZMod 2) = 0 from by decide,
    show (14 : ZMod 2) = 0 from by decide,
    show (16 : ZMod 2) = 0 from by decide,
    show (17 : ZMod 2) = 1 from by decide]

theorem right_coefficient_2 : polyP * vB + uA * vAB + uB * vOne + uAB * vA = 0 := by
  classical
  simp only [vOne, vA, vB, vAB, uA, uB, uAB, polyP, polyQ, polyR, polyS, basis,
    mul_add, add_mul, mul_one, one_mul, MonoidAlgebra.single_mul_single]
  ext g
  simp only [MonoidAlgebra.coeff_add, MonoidAlgebra.coeff_single,
    MonoidAlgebra.one_def, MonoidAlgebra.coeff_zero, Finsupp.add_apply, Finsupp.single_apply,
    Finsupp.zero_apply, mul_def, inv_def, one_def, mulE, invE, oneE,
    ex, ey, ez, ea, eb, rho, factor, addQ, addV, negV, zeroV]
  ring_nf
  simp [show (2 : ZMod 2) = 0 from by decide,
    show (4 : ZMod 2) = 0 from by decide,
    show (6 : ZMod 2) = 0 from by decide,
    show (8 : ZMod 2) = 0 from by decide,
    show (10 : ZMod 2) = 0 from by decide,
    show (12 : ZMod 2) = 0 from by decide,
    show (14 : ZMod 2) = 0 from by decide,
    show (16 : ZMod 2) = 0 from by decide,
    show (17 : ZMod 2) = 1 from by decide]

theorem right_coefficient_3 : polyP * vAB + uA * vB + uB * vA + uAB * vOne = 0 := by
  classical
  simp only [vOne, vA, vB, vAB, uA, uB, uAB, polyP, polyQ, polyR, polyS, basis,
    mul_add, add_mul, mul_one, one_mul, MonoidAlgebra.single_mul_single]
  ext g
  simp only [MonoidAlgebra.coeff_add, MonoidAlgebra.coeff_single,
    MonoidAlgebra.one_def, MonoidAlgebra.coeff_zero, Finsupp.add_apply, Finsupp.single_apply,
    Finsupp.zero_apply, mul_def, inv_def, one_def, mulE, invE, oneE,
    ex, ey, ez, ea, eb, rho, factor, addQ, addV, negV, zeroV]
  ring_nf
  simp [show (2 : ZMod 2) = 0 from by decide,
    show (4 : ZMod 2) = 0 from by decide,
    show (6 : ZMod 2) = 0 from by decide,
    show (8 : ZMod 2) = 0 from by decide,
    show (10 : ZMod 2) = 0 from by decide,
    show (12 : ZMod 2) = 0 from by decide,
    show (14 : ZMod 2) = 0 from by decide,
    show (16 : ZMod 2) = 0 from by decide,
    show (17 : ZMod 2) = 1 from by decide]

theorem mul_inverseE : unitE * inverseE = 1 := by
  calc
    unitE * inverseE = (polyP * vOne + uA * vA + uB * vB + uAB * vAB) + (polyP * vA + uA * vOne + uB * vAB + uAB * vB) + (polyP * vB + uA * vAB + uB * vOne + uAB * vA) + (polyP * vAB + uA * vB + uB * vA + uAB * vOne) := by
      simp only [inverseE, unitE, uA, uB, uAB, mul_add, add_mul]
      abel
    _ = 1 := by rw [right_coefficient_0, right_coefficient_1, right_coefficient_2, right_coefficient_3]; simp

end
end Promislow


/-! The 21 distinct terms in Gardam's unit. -/

namespace Promislow

noncomputable section

open Coset

def supportE : Finset E :=
  {⟨⟨0, 0, 0⟩, one⟩, ⟨⟨1, 0, 0⟩, one⟩,
   ⟨⟨0, 1, 0⟩, one⟩, ⟨⟨1, 1, 0⟩, one⟩,
   ⟨⟨0, 0, -1⟩, one⟩, ⟨⟨1, 0, -1⟩, one⟩,
   ⟨⟨0, 1, -1⟩, one⟩, ⟨⟨1, 1, -1⟩, one⟩,
   ⟨⟨-1, -1, 0⟩, a⟩, ⟨⟨1, 0, 0⟩, a⟩,
   ⟨⟨0, -1, 1⟩, a⟩, ⟨⟨0, 0, 1⟩, a⟩,
   ⟨⟨0, 0, 0⟩, b⟩, ⟨⟨1, 0, 0⟩, b⟩,
   ⟨⟨0, -1, 1⟩, b⟩, ⟨⟨1, 1, 1⟩, b⟩,
   ⟨⟨0, 0, 0⟩, ab⟩, ⟨⟨1, 0, -1⟩, ab⟩,
   ⟨⟨-1, 0, -1⟩, ab⟩, ⟨⟨0, 1, -1⟩, ab⟩, ⟨⟨0, -1, -1⟩, ab⟩}

theorem supportE_card : supportE.card = 21 := by decide

theorem unitE_as_sum : unitE = ∑ g ∈ supportE, basis g := by
  classical
  simp [supportE, unitE, polyP, polyQ, polyR, polyS, basis, mul_add, add_mul,
    MonoidAlgebra.single_mul_single, MonoidAlgebra.one_def, mul_def, inv_def, one_def,
    mulE, invE, oneE, ex, ey, ez, ea, eb, rho, factor, addQ, addV, negV, zeroV]
  abel

theorem unitE_coeff (g : E) : unitE.coeff g = if g ∈ supportE then 1 else 0 := by
  classical
  rw [unitE_as_sum]
  simp [basis, MonoidAlgebra.coeff_sum, MonoidAlgebra.coeff_single, Finsupp.single_apply]

theorem unitE_support : unitE.coeff.support = supportE := by
  classical
  ext g
  rw [Finsupp.mem_support_iff, unitE_coeff]
  by_cases hg : g ∈ supportE <;> simp [hg]

theorem unitE_support_card : unitE.coeff.support.card = 21 := by
  rw [unitE_support, supportE_card]

theorem unitE_not_basis (g : E) : unitE ≠ basis g := by
  intro h
  have hc := unitE_support_card
  rw [h] at hc
  have hs : (basis g).coeff.support = {g} := by
    simp [basis, MonoidAlgebra.coeff_single]
  rw [hs] at hc
  norm_num at hc

end
end Promislow


/-! Transport of the exact official coefficients through the faithful normal form. -/

namespace Promislow

noncomputable section

def algebraEquiv : UnitConjecture.R ≃+* RE :=
  MonoidAlgebra.mapDomainRingEquiv (ZMod 2) normalEquiv

@[simp] theorem algebra_coe (g : UnitConjecture.P) :
    algebraEquiv (g : UnitConjecture.R) = basis (encode g) := by
  change MonoidAlgebra.mapDomainRingEquiv (ZMod 2) normalEquiv
    (MonoidAlgebra.single g 1) = MonoidAlgebra.single (normalEquiv g) 1
  exact MonoidAlgebra.mapDomainRingEquiv_single normalEquiv 1 g

theorem official_x : UnitConjecture.x = px := rfl
theorem official_y : UnitConjecture.y = py := rfl
theorem official_z : UnitConjecture.z = pz := rfl

theorem image_u : algebraEquiv UnitConjecture.u = unitE := by
  have ha : (UnitConjecture.a : UnitConjecture.P) = pa := rfl
  have hb : (UnitConjecture.b : UnitConjecture.P) = pb := rfl
  have hab : (UnitConjecture.a * UnitConjecture.b : UnitConjecture.P) = pa * pb := rfl
  simp only [UnitConjecture.u, UnitConjecture.p, UnitConjecture.q, UnitConjecture.r,
    UnitConjecture.s, map_add, map_mul, map_one, algebra_coe, official_x, official_y,
    official_z, map_inv, encode_x, encode_y, encode_z, ha, hb, hab, encode_a, encode_b,
    unitE, polyP, polyQ, polyR, polyS, ex, ey, ez]
  simp [basis, MonoidAlgebra.single_mul_single]

theorem official_isUnit : IsUnit UnitConjecture.u := by
  refine isUnit_iff_exists.mpr ⟨algebraEquiv.symm inverseE, ?_, ?_⟩
  · apply algebraEquiv.injective
    simpa only [map_mul, map_one, RingEquiv.apply_symm_apply, image_u] using mul_inverseE
  · apply algebraEquiv.injective
    simpa only [map_mul, map_one, RingEquiv.apply_symm_apply, image_u] using inverseE_mul

theorem official_not_basis : ¬ ∃ g : UnitConjecture.P, UnitConjecture.u = g := by
  rintro ⟨g, hg⟩
  apply unitE_not_basis (encode g)
  simpa only [image_u, algebra_coe] using congrArg algebraEquiv hg

end
end Promislow


/- The exact three clauses are checked transiently during native validation:
   `presented_torsion_free`, `official_isUnit`, and `official_not_basis`.
-/

end D5.S3.ArithUnits.Gardam
