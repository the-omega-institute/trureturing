/- GID: D5/S3/Arith/CharacterSums/PascadiPrimeCubePairRigidity
   generality: G
   mirror-B: D5/B/S3/Arith/CharacterSums/PascadiPrimeCubePairRigidity
   mirror-E: none(waiver:prime-cube-pair-rigidity)
   anchors: []
   utility: none
   digest: Prime-square midpoint rigidity for exact word pairs on simple unit branches. -/

module

public import D5.S3.Arith.CharacterSums.PascadiPrimeSquareHyperbola
public import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-! Symmetric word pairs over the prime cube and their reduction to the prime square. -/

namespace D5.S3.Arith.CharacterSums.Original

@[expose] public section

open Polynomial

/-- Reduction of a prime-cube residue to the prime-square ring. -/
def primeCubeReduction (p : ℕ) : ZMod (p ^ 3) →+* ZMod (p ^ 2) :=
  ZMod.castHom ⟨p, by ring⟩ _

/-- Sum of the three word coordinates. -/
def wordSum {R : Type*} [Add R] (z : Fin 3 → R) : R :=
  z 0 + z 1 + z 2

/-- Product of the three word coordinates. -/
def wordProd {R : Type*} [Mul R] (z : Fin 3 → R) : R :=
  z 0 * z 1 * z 2

/-- Coefficient of the linear term of the product along the displacement `u`. -/
def wordProdLinear {R : Type*} [Add R] [Mul R] (z u : Fin 3 → R) : R :=
  u 0 * z 1 * z 2 + u 1 * z 0 * z 2 + u 2 * z 0 * z 1

/-- The weighted complementary pair products in the difference quartic. -/
def pairWeighted {R : Type*} [Add R] [Mul R] (d u : Fin 3 → R) : R :=
  u 0 * d 1 * d 2 * (d 1 + d 2) + u 1 * d 0 * d 2 * (d 0 + d 2) +
    u 2 * d 0 * d 1 * (d 0 + d 1)

/-- The difference polynomial `X P + N Q`, with `Dᵢ = vᵢ − X uᵢ`,
`N = sum D`, `Q = prod D` and `P = ∑ᵢ uᵢ Dⱼ Dₖ (Dⱼ + Dₖ)`. -/
noncomputable def differenceQuartic {R : Type*} [CommRing R] (u v : Fin 3 → R) : R[X] :=
  let d i := C (v i) - X * C (u i)
  X * pairWeighted d (C ∘ u) + wordSum d * wordProd d

private theorem differenceQuartic_eval {R : Type*} [CommRing R] (u v : Fin 3 → R) (a : R) :
    (differenceQuartic u v).eval a =
      let d i := v i - a * u i
      a * pairWeighted d u + wordSum d * wordProd d := by
  simp only [differenceQuartic, pairWeighted, wordSum, wordProd, eval_add, eval_mul, eval_sub,
    eval_X, eval_C, Function.comp_apply]

/-- The scalar half of the displacement `p` in the prime-cube ring for odd `p`. -/
def primeCubeHalfStep (p : ℕ) : ZMod (p ^ 3) :=
  (p : ZMod (p ^ 3)) * (2 : ZMod (p ^ 3))⁻¹

/-- The two endpoints use the same difference data `u` and the indicated midpoint
and slope. The positive endpoint is indexed by `true`. -/
structure PrimeCubePair (p : ℕ) where
  z : Fin 3 → ZMod (p ^ 3)
  slope : ZMod (p ^ 3)
  slopeStep : ZMod (p ^ 3)
  y : Bool → Fin 3 → ZMod (p ^ 3)

namespace PrimeCubePair

/-- The first triple at each endpoint. -/
def x {p : ℕ} (A : PrimeCubePair p) (u : Fin 3 → ZMod (p ^ 3))
    (s : Bool) (i : Fin 3) : ZMod (p ^ 3) :=
  if s then A.z i + primeCubeHalfStep p * u i else A.z i - primeCubeHalfStep p * u i

/-- The full slope at each endpoint. -/
def rho {p : ℕ} (A : PrimeCubePair p) (s : Bool) : ZMod (p ^ 3) :=
  if s then A.slope + primeCubeHalfStep p * A.slopeStep
  else A.slope - primeCubeHalfStep p * A.slopeStep

/-- Both exact words, both full slopes, and the difference of their second triples. -/
structure Exact {p : ℕ} (A : PrimeCubePair p) (g : ZMod (p ^ 3))
    (u v : Fin 3 → ZMod (p ^ 3)) : Prop where
  word : ∀ s, wordSum (A.x u s) = g * A.rho s * wordProd (A.x u s)
  fullSlope : ∀ s i, A.y s i = A.rho s * A.x u s i
  difference : ∀ i, A.y true i - A.y false i = (p : ZMod (p ^ 3)) * v i

end PrimeCubePair

/-- The midpoint equations over the prime-square ring and the two consequences
after replacing `t z` by `D = v − a u`. -/
structure PrimeSquareMidpointEquations {p : ℕ} (g : ZMod (p ^ 2))
    (u v z : Fin 3 → ZMod (p ^ 2)) (a t : ZMod (p ^ 2)) : Prop where
  velocity : ∀ i, v i = a * u i + t * z i
  word : wordSum z = g * a * wordProd z
  linearWord : wordSum u = g * (a * wordProdLinear z u + t * wordProd z)
  square : let d i := v i - a * u i
    t ^ 2 * wordSum d = g * a * wordProd d
  quartic : (differenceQuartic u v).eval a = 0

private theorem two_unit_primePow {p k : ℕ} (hp : p.Prime) (hodd : p ≠ 2)
    (hk : 0 < k) : IsUnit (2 : ZMod (p ^ k)) :=
  (ZMod.isUnit_natCast_iff_not_dvd_pow hp hk).2
    (fun h => hodd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h))

private theorem two_mul_halfStep {p : ℕ} (hp : p.Prime) (hodd : p ≠ 2) :
    2 * primeCubeHalfStep p = (p : ZMod (p ^ 3)) := by
  rw [primeCubeHalfStep, mul_left_comm,
    ZMod.mul_inv_of_unit _ (two_unit_primePow hp hodd (by decide)), mul_one]

private theorem reduce_of_prime_mul_eq_zero {p : ℕ} (hp : p.Prime)
    {b : ZMod (p ^ 3)} (h : (p : ZMod (p ^ 3)) * b = 0) : primeCubeReduction p b = 0 := by
  obtain ⟨b, rfl⟩ := ZMod.intCast_surjective b
  rw [map_intCast, ZMod.intCast_zmod_eq_zero_iff_dvd]
  rw [← Int.cast_natCast, ← Int.cast_mul, ZMod.intCast_zmod_eq_zero_iff_dvd,
    Nat.cast_pow, pow_succ, mul_comm ((p : ℤ) ^ 2)] at h
  rw [Nat.cast_pow]
  exact (mul_dvd_mul_iff_left (by exact_mod_cast hp.ne_zero : (p : ℤ) ≠ 0)).mp h

/-- Symmetric subtraction over the cube retains the linear coefficient after
division by `p`. Averaging gives the central word over the square. -/
theorem primeCube_midpoint_equations {p : ℕ} (hp : p.Prime) (hodd : p ≠ 2)
    {g : ZMod (p ^ 3)} (hg : IsUnit g) {u v : Fin 3 → ZMod (p ^ 3)}
    {A : PrimeCubePair p} (hA : A.Exact g u v) :
    let r := primeCubeReduction p
    PrimeSquareMidpointEquations (r g) (r ∘ u) (r ∘ v) (r ∘ A.z)
      (r A.slope) (r A.slopeStep) := by
  dsimp only
  let r := primeCubeReduction p
  let h := primeCubeHalfStep p
  have hpStep : 2 * h = (p : ZMod (p ^ 3)) := two_mul_halfStep hp hodd
  have hcubed : h ^ 3 = 0 := by
    rw [show h = (p : ZMod (p ^ 3)) * (2 : ZMod (p ^ 3))⁻¹ from rfl,
      mul_pow, ← Nat.cast_pow, ZMod.natCast_self, zero_mul]
  have hsquared : (r h) ^ 2 = 0 := by
    rw [show h = (p : ZMod (p ^ 3)) * (2 : ZMod (p ^ 3))⁻¹ from rfl,
      map_mul, mul_pow, map_natCast, ← Nat.cast_pow, ZMod.natCast_self, zero_mul]
  have velocity (i : Fin 3) :
      (r ∘ v) i = (r A.slope) * (r ∘ u) i + (r A.slopeStep) * (r ∘ A.z) i := by
    have hi := hA.difference i
    rw [hA.fullSlope true i, hA.fullSlope false i] at hi
    change (A.slope + h * A.slopeStep) * (A.z i + h * u i) -
      (A.slope - h * A.slopeStep) * (A.z i - h * u i) = _ at hi
    have he : (p : ZMod (p ^ 3)) *
        (v i - (A.slope * u i + A.slopeStep * A.z i)) = 0 := by
      rw [← hpStep] at hi
      rw [← hpStep]
      linear_combination -hi
    exact sub_eq_zero.mp (by simpa only [r, Function.comp_apply, map_sub, map_add, map_mul] using
      reduce_of_prime_mul_eq_zero hp he)
  have word : wordSum (r ∘ A.z) = r g * r A.slope * wordProd (r ∘ A.z) := by
    have hwPlus := congrArg r (hA.word true)
    have hwMinus := congrArg r (hA.word false)
    simp only [PrimeCubePair.x, PrimeCubePair.rho, ite_true, Bool.false_eq_true, ite_false,
      wordSum, wordProd, map_add, map_sub, map_mul] at hwPlus hwMinus
    apply (two_unit_primePow hp hodd (k := 2) (by decide)).mul_left_cancel
    simp only [wordSum, wordProd, Function.comp_apply]
    linear_combination hwPlus + hwMinus + 2 * r g *
      ((r A.slope *
        (r (A.z 0) * r (u 1) * r (u 2) + r (A.z 1) * r (u 0) * r (u 2) +
          r (A.z 2) * r (u 0) * r (u 1)) +
      r A.slopeStep *
        (r (u 0) * r (A.z 1) * r (A.z 2) + r (u 1) * r (A.z 0) * r (A.z 2) +
          r (u 2) * r (A.z 0) * r (A.z 1))) +
        (r h)^2 * r A.slopeStep * (r (u 0) * r (u 1) * r (u 2))) * hsquared
  have linearWord : wordSum (r ∘ u) =
      r g * (r A.slope * wordProdLinear (r ∘ A.z) (r ∘ u) +
        r A.slopeStep * wordProd (r ∘ A.z)) := by
    have hwPlus := hA.word true
    have hwMinus := hA.word false
    simp only [PrimeCubePair.x, PrimeCubePair.rho, ite_true, Bool.false_eq_true, ite_false,
      wordSum, wordProd] at hwPlus hwMinus
    have he : (p : ZMod (p ^ 3)) *
        (wordSum u - g * (A.slope * wordProdLinear A.z u + A.slopeStep * wordProd A.z)) = 0 := by
      rw [← hpStep]
      simp only [wordSum, wordProd, wordProdLinear] at *
      linear_combination hwPlus - hwMinus + 2 * g *
        (A.slope * (u 0 * u 1 * u 2) +
          A.slopeStep * (A.z 0 * u 1 * u 2 + A.z 1 * u 0 * u 2 + A.z 2 * u 0 * u 1)) *
        hcubed
    exact sub_eq_zero.mp (by simpa only [wordSum, wordProd, wordProdLinear, map_sub, map_add,
      map_mul, Function.comp_apply, r] using reduce_of_prime_mul_eq_zero hp he)
  let a := r A.slope
  let t := r A.slopeStep
  let d i := (r ∘ v) i - a * (r ∘ u) i
  have hd (i : Fin 3) : d i = t * (r ∘ A.z) i := by
    dsimp only [d, a, t]
    rw [velocity i]
    ring
  have hs : wordSum d = t * wordSum (r ∘ A.z) := by
    simp only [wordSum, hd]
    ring
  have hq : wordProd d = t ^ 3 * wordProd (r ∘ A.z) := by
    simp only [wordProd, hd]
    ring
  have hl : wordProdLinear d (r ∘ u) = t ^ 2 * wordProdLinear (r ∘ A.z) (r ∘ u) := by
    simp only [wordProdLinear, hd]
    ring
  have hn : t ^ 2 * wordSum d = r g * a * wordProd d := by
    rw [hs, hq, word]
    ring
  refine ⟨velocity, word, linearWord, hn, ?_⟩
  rw [differenceQuartic_eval]
  change a * pairWeighted d (r ∘ u) + wordSum d * wordProd d = 0
  have hP : pairWeighted d (r ∘ u) =
      wordSum d * wordProdLinear d (r ∘ u) - wordSum (r ∘ u) * wordProd d := by
    unfold pairWeighted wordSum wordProdLinear wordProd
    ring
  apply (hg.map r).mul_left_cancel
  rw [mul_zero, hP]
  have hder : t ^ 2 * wordSum (r ∘ u) =
      r g * (a * wordProdLinear d (r ∘ u) + wordProd d) := by
    rw [linearWord, hl, hq]
    ring
  linear_combination wordSum (r ∘ u) * hn - wordSum d * hder

private theorem square_zero_of_lower_zero {p : ℕ} {d : ZMod (p ^ 2)}
    (h : primeSquareReduction p d = 0) : d ^ 2 = 0 := by
  obtain ⟨b, rfl⟩ := ZMod.intCast_surjective d
  rw [map_intCast, ZMod.intCast_zmod_eq_zero_iff_dvd] at h
  obtain ⟨k, hk⟩ := h
  rw [hk, Int.cast_mul, mul_pow, Int.cast_natCast, ← Nat.cast_pow, ZMod.natCast_self, zero_mul]

private theorem primeSquare_isUnit_iff {p : ℕ} (hp : p.Prime) (v : ZMod (p ^ 2)) :
    IsUnit v ↔ primeSquareReduction p v ≠ 0 := by
  let : NeZero (p ^ 2) := ⟨pow_ne_zero _ hp.ne_zero⟩
  obtain ⟨n, rfl⟩ := ZMod.natCast_zmod_surjective v
  rw [map_natCast, ZMod.isUnit_natCast_iff_not_dvd_pow hp (by decide : 0 < 2),
    ne_eq, ZMod.natCast_eq_zero_iff]

/-- A lower simple root admits at most one prime-square root of the given polynomial. -/
private theorem primeSquare_root_unique {p : ℕ} (hp : p.Prime)
    (f : (ZMod (p ^ 2))[X]) {a b : ZMod (p ^ 2)} {α : ZMod p}
    (ha : primeSquareReduction p a = α) (hb : primeSquareReduction p b = α)
    (hsimple : ((f.map (primeSquareReduction p)).derivative).eval α ≠ 0)
    (hfa : f.eval a = 0) (hfb : f.eval b = 0) : a = b := by
  have hd : (b - a) ^ 2 = 0 := square_zero_of_lower_zero (by rw [map_sub, ha, hb, sub_self])
  have he := f.eval_add_of_sq_eq_zero a (b - a) hd
  rw [add_sub_cancel, hfa, hfb, zero_add] at he
  have hunit : IsUnit (f.derivative.eval a) := (primeSquare_isUnit_iff hp _).2 (by
    rw [← Polynomial.eval_map_apply, ← Polynomial.derivative_map, ha]
    exact hsimple)
  exact (sub_eq_zero.mp (hunit.mul_left_cancel (he.symm.trans (mul_zero _).symm))).symm

/-- Two exact pairs with fixed coefficient and difference data on the same simple
lower slope root and nonzero lower square-root branch have the same slope, slope
step and midpoint modulo the prime square. -/
theorem primeCube_midpoint_unique {p : ℕ} (hp : p.Prime) (hodd : p ≠ 2)
    {g : ZMod (p ^ 3)} (hg : IsUnit g) {u v : Fin 3 → ZMod (p ^ 3)}
    {A B : PrimeCubePair p} (hA : A.Exact g u v) (hB : B.Exact g u v)
    {α τ : ZMod p}
    (haA : primeSquareReduction p (primeCubeReduction p A.slope) = α)
    (haB : primeSquareReduction p (primeCubeReduction p B.slope) = α)
    (htA : primeSquareReduction p (primeCubeReduction p A.slopeStep) = τ)
    (htB : primeSquareReduction p (primeCubeReduction p B.slopeStep) = τ)
    (ht : τ ≠ 0)
    (hN : wordSum (fun i => primeSquareReduction p (primeCubeReduction p (v i)) -
      α * primeSquareReduction p (primeCubeReduction p (u i))) ≠ 0)
    (hsimple : ((differenceQuartic (primeCubeReduction p ∘ u) (primeCubeReduction p ∘ v)).map
      (primeSquareReduction p)).derivative.eval α ≠ 0) :
    let r := primeCubeReduction p
    r A.slope = r B.slope ∧ r A.slopeStep = r B.slopeStep ∧ r ∘ A.z = r ∘ B.z := by
  dsimp only
  let r := primeCubeReduction p
  let lower := primeSquareReduction p
  let a := r A.slope
  let t := r A.slopeStep
  let t' := r B.slopeStep
  let d i := (r ∘ v) i - a * (r ∘ u) i
  have eqA := primeCube_midpoint_equations hp hodd hg hA
  have eqB := primeCube_midpoint_equations hp hodd hg hB
  have ha : a = r B.slope :=
    primeSquare_root_unique hp _ haA haB hsimple eqA.quartic eqB.quartic
  have hread : lower a = α := haA
  have hNunit : IsUnit (wordSum d) := (primeSquare_isUnit_iff hp _).2 (by
    change lower (wordSum d) ≠ 0
    simp only [d, Function.comp_apply, wordSum, map_add, map_sub, map_mul, hread]
    exact hN)
  have hsquare : t ^ 2 = t' ^ 2 := by
    apply hNunit.mul_right_cancel
    have hb := eqB.square
    change t' ^ 2 * wordSum (fun i => r (v i) - r B.slope * r (u i)) =
      r g * r B.slope * wordProd (fun i => r (v i) - r B.slope * r (u i)) at hb
    rw [← ha] at hb
    exact eqA.square.trans hb.symm
  have htunit : IsUnit t := (primeSquare_isUnit_iff hp _).2 (htA.trans_ne ht)
  have hsum : IsUnit (t + t') := by
    apply (primeSquare_isUnit_iff hp _).2
    change lower (t + t') ≠ 0
    rw [map_add, htA, htB, ← htA, ← map_add, ← two_mul]
    have htwo : lower (2 : ZMod (p ^ 2)) ≠ 0 :=
      (primeSquare_isUnit_iff hp _).mp (two_unit_primePow hp hodd (by decide))
    let : Fact p.Prime := ⟨hp⟩
    rw [map_mul, htA]
    exact mul_ne_zero htwo ht
  have he : t = t' := by
    apply sub_eq_zero.mp
    apply hsum.mul_left_cancel
    rw [mul_zero]
    linear_combination hsquare
  refine ⟨ha, he, funext fun i => ?_⟩
  apply htunit.mul_left_cancel
  have vA := eqA.velocity i
  have vB := eqB.velocity i
  change r (v i) = r B.slope * r (u i) + t' * r (B.z i) at vB
  rw [← ha, ← he] at vB
  exact add_left_cancel (vA.symm.trans vB)

private theorem int_eq_of_cast_eq_of_abs_sub_lt {m : ℕ} {x y : ℤ}
    (hres : (x : ZMod m) = y) (hclose : |x - y| < (m : ℤ)) : x = y := by
  by_contra hne
  have hd := (ZMod.intCast_eq_intCast_iff_dvd_sub y x m).1 hres.symm
  have hle := Int.natAbs_le_of_dvd_ne_zero hd (sub_ne_zero.mpr hne)
  have hlt : (x - y).natAbs < m := by
    exact_mod_cast (show ((x - y).natAbs : ℤ) < (m : ℤ) by simpa using hclose)
  omega

/-- Literal endpoint uniqueness on a simple unit branch. The first triples need
width less than `p²`. The full words and unit coordinates recover the second
triples modulo `p³`, allowing width less than `p³` for them. -/
theorem primeCube_literal_pair_unique {p : ℕ} (hp : p.Prime) (hodd : p ≠ 2)
    {g : ZMod (p ^ 3)} (hg : IsUnit g) {u v : Fin 3 → ZMod (p ^ 3)}
    {A B : PrimeCubePair p} (hA : A.Exact g u v) (hB : B.Exact g u v)
    {α τ : ZMod p}
    (haA : primeSquareReduction p (primeCubeReduction p A.slope) = α)
    (haB : primeSquareReduction p (primeCubeReduction p B.slope) = α)
    (htA : primeSquareReduction p (primeCubeReduction p A.slopeStep) = τ)
    (htB : primeSquareReduction p (primeCubeReduction p B.slopeStep) = τ)
    (ht : τ ≠ 0)
    (hN : wordSum (fun i => primeSquareReduction p (primeCubeReduction p (v i)) -
      α * primeSquareReduction p (primeCubeReduction p (u i))) ≠ 0)
    (hsimple : ((differenceQuartic (primeCubeReduction p ∘ u) (primeCubeReduction p ∘ v)).map
      (primeSquareReduction p)).derivative.eval α ≠ 0)
    (hxunit : ∀ s i, IsUnit (A.x u s i))
    {X X' Y Y' : Bool → Fin 3 → ℤ}
    (hx : ∀ s i, (X s i : ZMod (p ^ 3)) = A.x u s i)
    (hx' : ∀ s i, (X' s i : ZMod (p ^ 3)) = B.x u s i)
    (hy : ∀ s i, (Y s i : ZMod (p ^ 3)) = A.y s i)
    (hy' : ∀ s i, (Y' s i : ZMod (p ^ 3)) = B.y s i)
    (hX : ∀ s i, |X s i - X' s i| < (p : ℤ) ^ 2)
    (hY : ∀ s i, |Y s i - Y' s i| < (p : ℤ) ^ 3) :
    X = X' ∧ Y = Y' := by
  let r := primeCubeReduction p
  obtain ⟨_, _, hz⟩ := primeCube_midpoint_unique hp hodd hg hA hB haA haB htA htB ht hN hsimple
  have hxEq : X = X' := by
    funext s i
    have hzi : r (A.z i) = r (B.z i) := congrFun hz i
    have hc : r (A.x u s i) = r (B.x u s i) := by
      cases s <;> simp only [PrimeCubePair.x, Bool.false_eq_true, ite_false, ite_true,
        map_add, map_sub, hzi]
    apply int_eq_of_cast_eq_of_abs_sub_lt (m := p ^ 2)
    · rw [← map_intCast r, ← map_intCast r, hx, hx']
      exact hc
    · simpa only [Nat.cast_pow] using hX s i
  have hfullx (s : Bool) : A.x u s = B.x u s := by
    funext i
    rw [← hx, ← hx', hxEq]
  refine ⟨hxEq, ?_⟩
  funext s i
  have hprod : IsUnit (wordProd (A.x u s)) :=
    ((hxunit s 0).mul (hxunit s 1)).mul (hxunit s 2)
  have hrho : A.rho s = B.rho s := by
    apply hprod.mul_right_cancel
    apply hg.mul_left_cancel
    have h := (hA.word s).symm.trans ((hfullx s).symm ▸ hB.word s)
    simpa only [mul_assoc] using h
  apply int_eq_of_cast_eq_of_abs_sub_lt (m := p ^ 3)
  · rw [hy, hy', hA.fullSlope, hB.fullSlope, hrho, hfullx]
  · simpa only [Nat.cast_pow] using hY s i

end

end D5.S3.Arith.CharacterSums.Original
