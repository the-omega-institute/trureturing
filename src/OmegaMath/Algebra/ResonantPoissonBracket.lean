import OmegaMath.Algebra.ResonantCoordinateRing
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.RingTheory.Derivation.Lie
import Mathlib.Tactic.Abel
import Mathlib.Tactic.LinearCombination

/-!
Omega original.

Skew real biderivations and the signed Poisson bracket on the resonant coordinate ring.
The defining relation is central, and the bracket on the quotient satisfies cyclic Jacobi.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Omega.PaisPoisson

open MvPolynomial
open scoped BigOperators

/-- The two Poisson laws needed by this obstruction. The right Hamiltonians are
real derivations and the bracket is skew. -/
structure SkewBiderivation (S : Type*) [CommRing S] [Algebra ℝ S] where
  ham : S → Derivation ℝ S S
  skew : ∀ a b, ham a b = -ham b a

section Brackets
variable {S : Type*} [CommRing S] [Algebra ℝ S]

theorem SkewBiderivation.left_add (b : SkewBiderivation S) (a c d : S) :
    b.ham (a + c) d = b.ham a d + b.ham c d := by
  rw [b.skew (a + c) d, map_add, b.skew a d, b.skew c d]
  abel

theorem SkewBiderivation.self_zero (b : SkewBiderivation S) (a : S) : b.ham a a = 0 := by
  apply (smul_eq_zero_iff_right (by norm_num : (2 : ℝ) ≠ 0)).mp
  rw [two_smul, ← eq_neg_iff_add_eq_zero]
  exact b.skew a a

end Brackets

def PreservesBracket {S : Type*} [CommRing S] [Algebra ℝ S]
    (e : S ≃ₐ[ℝ] S) (a b : SkewBiderivation S) : Prop :=
  ∀ f g, e (a.ham f g) = b.ham (e f) (e g)

theorem leibniz_mul {S : Type*} [CommRing S] [Algebra ℝ S]
    (D : Derivation ℝ S S) (a b : S) :
    D (a * b) = a * D b + b * D a := D.leibniz a b

private abbrev PU : FourPolys := X 0
private abbrev PV : FourPolys := X 1
private abbrev PX : FourPolys := X 2
private abbrev PY : FourPolys := X 3

private def mixed (n m : ℕ) (Ω s : ℝ) : FourPolys :=
  C (-Ω / 2) * (PU ^ (n - 1) * PV ^ (m - 1) * ((n : FourPolys) * PV + C s * (m : FourPolys) * PU))

private abbrev PolyDer := Derivation ℝ FourPolys FourPolys
private abbrev pd (i : Fin 4) : PolyDer := pderiv i

private abbrev weight (r : FourPolys) (D : PolyDer) : PolyDer := r • D

private def wedge (D E : PolyDer) (f : FourPolys) : PolyDer :=
  weight (D f) E - weight (E f) D

@[simp] private theorem wedge_apply (D E : PolyDer) (f g : FourPolys) :
    wedge D E f g = D f * E g - E f * D g := by
  simp only [wedge, Derivation.sub_apply, Derivation.smul_apply, smul_eq_mul]

private def energyDirection (s : ℝ) : PolyDer := pd 0 + weight (C s) (pd 1)

private def rotatingDirection : PolyDer := weight PY (pd 2) - weight PX (pd 3)

private def ambient (n m : ℕ) (Ω s : ℝ) : SkewBiderivation FourPolys where
  ham f := weight (C Ω) (wedge (energyDirection s) rotatingDirection f) +
    weight (mixed n m Ω s) (wedge (pd 2) (pd 3) f)
  skew f g := by
    simp only [Derivation.add_apply, Derivation.smul_apply, smul_eq_mul, wedge_apply]
    ring

private theorem ambient_apply (n m : ℕ) (Ω s : ℝ) (f g : FourPolys) :
    (ambient n m Ω s).ham f g =
      C Ω * (energyDirection s f * rotatingDirection g - rotatingDirection f * energyDirection s g) +
      mixed n m Ω s * (pd 2 f * pd 3 g - pd 3 f * pd 2 g) := by
  simp only [ambient, Derivation.add_apply, Derivation.smul_apply, smul_eq_mul, wedge_apply]

private theorem ambient_gen (n m : ℕ) (Ω s : ℝ) (i j : Fin 4) :
    (ambient n m Ω s).ham (X i) (X j) =
      ![![0, 0, C Ω * PY, -(C Ω * PX)],
        ![0, 0, C Ω * (C s * PY), -(C Ω * (C s * PX))],
        ![-(C Ω * PY), -(C Ω * (C s * PY)), 0, mixed n m Ω s],
        ![C Ω * PX, C Ω * (C s * PX), -mixed n m Ω s, 0]] i j := by
  fin_cases i <;> fin_cases j <;>
    simp [ambient_apply, energyDirection, rotatingDirection, pd, Derivation.sub_apply, weight] <;>
    (ring_nf; simp)

def jacobiator {S : Type*} [CommRing S] [Algebra ℝ S]
    (b : SkewBiderivation S) (f g h : S) : S :=
  b.ham f (b.ham g h) + b.ham g (b.ham h f) + b.ham h (b.ham f g)

private def jacobiDerivation {S : Type*} [CommRing S] [Algebra ℝ S]
    (b : SkewBiderivation S) (f g : S) : Derivation ℝ S S :=
  ⁅b.ham f, b.ham g⁆ - b.ham (b.ham f g)

private theorem jacobiDerivation_apply {S : Type*} [CommRing S] [Algebra ℝ S]
    (b : SkewBiderivation S) (f g h : S) : jacobiDerivation b f g h = jacobiator b f g h := by
  simp only [jacobiDerivation, jacobiator, Derivation.sub_apply, Derivation.commutator_apply]
  rw [b.skew h f, map_neg (b.ham g), b.skew h (b.ham f g)]
  abel

private theorem jacobi_rotate {S : Type*} [CommRing S] [Algebra ℝ S]
    (b : SkewBiderivation S) (f g h : S) : jacobiator b f g h = jacobiator b g h f := by
  unfold jacobiator
  abel

private theorem derivation_zero_on_X (D : Derivation ℝ FourPolys FourPolys)
    (h : ∀ i, D (X i) = 0) (f : FourPolys) : D f = 0 := by
  have he : D = 0 := MvPolynomial.derivation_ext (by simpa only [Derivation.zero_apply] using h)
  rw [he, Derivation.zero_apply]

private theorem jacobi_of_generators (b : SkewBiderivation FourPolys)
    (h : ∀ i j k : Fin 4, jacobiator b (X i) (X j) (X k) = 0) :
    ∀ f g k, jacobiator b f g k = 0 := by
  have step (f g : FourPolys) (H : ∀ i : Fin 4, jacobiator b f g (X i) = 0) (k : FourPolys) :
      jacobiator b f g k = 0 := by
    rw [← jacobiDerivation_apply]
    exact derivation_zero_on_X (jacobiDerivation b f g)
      (fun i => (jacobiDerivation_apply b f g (X i)).trans (H i)) k
  intro f g k
  apply step f g
  intro i
  rw [jacobi_rotate b f g (X i)]
  apply step g (X i)
  intro j
  rw [jacobi_rotate b g (X i) (X j)]
  exact step (X i) (X j) (h i j) g

set_option maxHeartbeats 2500000 in
private theorem ambient_jacobi_gen (n m : ℕ) (Ω s : ℝ) (i j k : Fin 4) :
    jacobiator (ambient n m Ω s) (X i) (X j) (X k) = 0 := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    simp only [jacobiator, ambient_gen] <;>
    simp [ambient_apply, energyDirection, rotatingDirection, pd, weight,
      Derivation.sub_apply, mixed] <;> ring

private theorem ambient_jacobi (n m : ℕ) (Ω s : ℝ) :
    ∀ f g k, jacobiator (ambient n m Ω s) f g k = 0 :=
  jacobi_of_generators _ (ambient_jacobi_gen n m Ω s)

private theorem relation_central (n m : ℕ) (hn : 0 < n) (hm : 0 < m) (Ω s : ℝ)
    (f : FourPolys) : (ambient n m Ω s).ham f (relationPoly n m) = 0 := by
  rw [(ambient n m Ω s).skew]
  apply (neg_eq_zero (α := FourPolys)).mpr
  apply derivation_zero_on_X
  intro i
  have hn' : n - 1 + 1 = n := by omega
  have hm' : m - 1 + 1 = m := by omega
  have hU : PU ^ n = PU ^ (n - 1) * PU := by rw [← pow_succ, hn']
  have hV : PV ^ m = PV ^ (m - 1) * PV := by rw [← pow_succ, hm']
  have h2 : (2 : FourPolys) * C (-Ω / 2) = -C Ω := by
    rw [show (2 : FourPolys) = C (2 : ℝ) by exact map_ofNat MvPolynomial.C 2 |>.symm, ← C_mul, ← C_neg]
    congr 1
    ring
  let k : FourPolys :=
    PU ^ (n - 1) * PV ^ (m - 1) * ((n : FourPolys) * PV + C s * (m : FourPolys) * PU)
  fin_cases i <;>
    simp [ambient_apply, relationPoly, energyDirection, rotatingDirection, pd, Derivation.sub_apply,
      weight]
  case «0» => right; ring
  case «1» => right; left; ring
  · unfold mixed
    rw [hU, hV]
    linear_combination -k * PY * h2
  · unfold mixed
    rw [hU, hV]
    linear_combination k * PX * h2


private theorem ambient_preserves_kernel (n m : ℕ) (hn : 0 < n) (hm : 0 < m) (Ω s : ℝ)
    (f g : FourPolys) (hg : quot n m g = 0) :
    quot n m ((ambient n m Ω s).ham f g) = 0 := by
  have hmem : g ∈ relationIdeal n m := Ideal.Quotient.eq_zero_iff_mem.mp hg
  obtain ⟨k, rfl⟩ := Ideal.mem_span_singleton.mp hmem
  rw [leibniz_mul (S := FourPolys) ((ambient n m Ω s).ham f),
    relation_central n m hn hm Ω s]
  rw [map_add (quot n m), map_mul (quot n m), map_mul (quot n m),
    show quot n m (relationPoly n m) = 0 from
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))]
  simp

private theorem quot_surjective (n m : ℕ) : Function.Surjective (quot n m) :=
  Ideal.Quotient.mk_surjective

private def representative (n m : ℕ) : Paper n m → FourPolys :=
  Function.surjInv (quot_surjective n m)

private theorem representative_rightInverse (n m : ℕ) :
    Function.RightInverse (representative n m) (quot n m) :=
  Function.rightInverse_surjInv (quot_surjective n m)

/-- The signed polynomial bracket descends to the quotient by the Casimir relation. -/
def quotientBracket (n m : ℕ) (hn : 0 < n) (hm : 0 < m) (Ω s : ℝ) :
    SkewBiderivation (Paper n m) where
  ham f := Derivation.liftOfRightInverse (representative_rightInverse n m)
    (ambient_preserves_kernel n m hn hm Ω s (representative n m f))
  skew f g := by
    change quot n m ((ambient n m Ω s).ham (representative n m f) (representative n m g)) =
      -quot n m ((ambient n m Ω s).ham (representative n m g) (representative n m f))
    rw [(ambient n m Ω s).skew, map_neg (quot n m)]

set_option maxHeartbeats 1000000 in
private theorem quotientBracket_quot (n m : ℕ) (hn : 0 < n) (hm : 0 < m) (Ω s : ℝ)
    (f g : FourPolys) :
    (quotientBracket n m hn hm Ω s).ham (quot n m f) (quot n m g) =
      quot n m ((ambient n m Ω s).ham f g) := by
  let b := ambient n m Ω s
  let q := quot n m
  let r := representative n m
  change _ = q (b.ham f g)
  calc
    _ = q (b.ham (r (q f)) g) :=
      Derivation.liftOfRightInverse_apply (representative_rightInverse n m) (d := b.ham (r (q f)))
        (ambient_preserves_kernel n m hn hm Ω s (r (q f))) g
    _ = -q (b.ham g (r (q f))) := by rw [b.skew (r (q f)) g, map_neg q]
    _ = -q (b.ham g f) := by
      apply congrArg (fun z : Paper n m => -z)
      exact Derivation.liftOfRightInverse_apply (representative_rightInverse n m) (d := b.ham g)
        (ambient_preserves_kernel n m hn hm Ω s g) f
    _ = q (b.ham f g) := by rw [b.skew f g, map_neg q]

private theorem quotientBracket_jacobi (n m : ℕ) (hn : 0 < n) (hm : 0 < m) (Ω s : ℝ)
    (f g h : Paper n m) : jacobiator (quotientBracket n m hn hm Ω s) f g h = 0 := by
  obtain ⟨f, rfl⟩ := quot_surjective n m f
  obtain ⟨g, rfl⟩ := quot_surjective n m g
  obtain ⟨h, rfl⟩ := quot_surjective n m h
  simp only [jacobiator, quotientBracket_quot, ← map_add (quot n m)]
  change (quot n m) (jacobiator (ambient n m Ω s) f g h) = 0
  rw [ambient_jacobi, map_zero]


/-- The generator table, with sign (s=1) for (23) and (s=-1) for (26)–(27). -/
structure GeneratorTable {S : Type*} [CommRing S] [Algebra ℝ S]
    {n m : ℕ} (b : SkewBiderivation S) (u v x y : S) (Ω s : ℝ) : Prop where
  uv : b.ham u v = 0
  ux : b.ham u x = Ω • y
  vx : b.ham v x = Ω • (s • y)
  uy : b.ham u y = -(Ω • x)
  vy : b.ham v y = -(Ω • (s • x))
  xy : b.ham x y = (-Ω / 2) •
    (u ^ (n - 1) * v ^ (m - 1) *
      ((n : S) * v + s • ((m : S) * u)))

abbrev PaperTable {n m : ℕ} (b : SkewBiderivation (Paper n m)) (Ω s : ℝ) :=
  GeneratorTable (n := n) (m := m) b (qu n m) (qv n m) (qx n m) (qy n m) Ω s

theorem quotientBracket_table (n m : ℕ) (hn : 0 < n) (hm : 0 < m) (Ω s : ℝ) :
    PaperTable (quotientBracket n m hn hm Ω s) Ω s := by
  have hs (r : ℝ) (z : Paper n m) : r • z = algebraMap ℝ (Paper n m) r * z :=
    Algebra.smul_def r z
  constructor <;>
    simp [qu, qv, qx, qy, quotientBracket_quot, ambient_gen, mixed, hs, mul_assoc]

/-- A real Poisson bracket, expressed by skew real derivations and cyclic Jacobi. -/
structure RealPoissonBracket (S : Type*) [CommRing S] [Algebra ℝ S] where
  bracket : SkewBiderivation S
  jacobi : ∀ f g h, jacobiator bracket f g h = 0

def paperPoisson (n m : ℕ) (hn : 0 < n) (hm : 0 < m) (Ω s : ℝ) :
    RealPoissonBracket (Paper n m) :=
  ⟨quotientBracket n m hn hm Ω s, quotientBracket_jacobi n m hn hm Ω s⟩

end Omega.PaisPoisson
