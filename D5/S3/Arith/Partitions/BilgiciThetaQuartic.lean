/- GID: D5/S3/Arith/Partitions/BilgiciThetaQuartic
   generality: I
   mirror-B: D5/B/S3/Arith/Partitions/BilgiciThetaQuartic
   mirror-E: none(waiver:finite-certificate-in-lean)
   anchors: []
   utility: none
   digest: The weight-eleven component has a nonzero quartic in Bilgici's theta quotient. -/


import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Tactic

/-!
# Bilgici's quartic theta factorization

A sparse polynomial identity gives the factorization modulo the integer theta family.
A truncated univariate specialization detects that the cofactor survives in the quotient.
-/

set_option autoImplicit false


open MvPolynomial
namespace D5.S3.Arith.Partitions.BilgiciThetaQuartic

private abbrev K := ZMod 19
private abbrev R := MvPolynomial (Fin 9) K
private abbrev Word := List (Fin 9)
private abbrev Sparse := List (Word × K)

def index (j : Fin 9) : ℤ := (j.val : ℤ) + 1

def sign (n : ℤ) : K := if n % 2 = 0 then 1 else -1

theorem sign_add (a b : ℤ) : sign (a+b) = sign a * sign b := by
  unfold sign
  split <;> split <;> split <;> simp_all <;> omega

private theorem sign_succ (a : ℤ) : sign (a+1) = -sign a := by
  rw [sign_add]
  have h : sign 1 = -1 := by decide
  rw [h, mul_neg_one]

def digit (r : ℤ) : Fin 9 := Fin.ofNat 9 (min r (19 - r) - 1).toNat

private def zTerms (x : ℤ) : Sparse :=
  if x % 19 = 0 then [] else [([digit (x % 19)], sign (x / 19))]

noncomputable def exponent : Word → (Fin 9 →₀ ℕ)
  | [] => 0
  | i :: is => Finsupp.single i 1 + exponent is

noncomputable def term (t : Word × K) : R := monomial (exponent t.1) t.2

noncomputable def denote (p : Sparse) : R := (p.map term).sum

@[simp] private theorem denote_nil : denote [] = 0 := rfl
@[simp] theorem denote_cons (t : Word × K) (p : Sparse) :
    denote (t :: p) = term t + denote p := rfl

private theorem exponent_append (a b : Word) :
    exponent (a ++ b) = exponent a + exponent b := by
  induction a with
  | nil => simp [exponent]
  | cons i a ih => simp [exponent, ih, add_assoc]

@[simp] theorem term_singleton (i : Fin 9) (c : K) :
    term ([i], c) = C c * X i := by
  simp [term, exponent, MvPolynomial.X, C_mul_monomial]

/-- The signed extension of the nine variables to all integer indices. -/
noncomputable def Z (x : ℤ) : MvPolynomial (Fin 9) (ZMod 19) :=
  if x % 19 = 0 then 0 else C (sign (x / 19)) * X (digit (x % 19))

private theorem denote_zTerms (x : ℤ) : denote (zTerms x) = Z x := by
  unfold zTerms Z
  split <;> simp

theorem Z_mul19 (k : ℤ) : Z (19*k) = 0 := by
  rw [Z, ite_eq_left (by omega)]

private theorem Z_shift (x : ℤ) : Z (x+19) = -Z x := by
  have hr : (x+19) % 19 = x % 19 := by omega
  have hq : (x+19) / 19 = x / 19 + 1 := by omega
  rw [Z, Z, hr, hq, sign_succ]
  split <;> simp

theorem Z_reflect (x : ℤ) : Z (19-x) = Z x := by
  by_cases h : x % 19 = 0
  · have hr : (19-x) % 19 = 0 := by omega
    simp [Z, h, hr]
  · have hr : (19-x) % 19 = 19 - x % 19 := by omega
    have hn : (19-x) % 19 ≠ 0 := by omega
    have hq : (19-x) / 19 = -(x / 19) := by omega
    have hd : digit (19 - x % 19) = digit (x % 19) := by
      simp [digit, min_comm]
    have hs : sign (-(x / 19)) = sign (x / 19) := by
      unfold sign
      split <;> split <;> simp_all
    rw [Z, Z, ite_eq_right h, ite_eq_right hn, hr, hq, hd, hs]

theorem Z_neg (x : ℤ) : Z (-x) = -Z x := by
  have h := Z_shift (-x)
  rw [show -x+19 = 19-x by omega, Z_reflect] at h
  rw [h, neg_neg]

theorem Z_base (i : Fin 9) : Z (index i) = X i := by
  have hb : 1 ≤ index i ∧ index i ≤ 9 := by unfold index; omega
  have hr : index i % 19 = index i := by omega
  have hn : index i % 19 ≠ 0 := by omega
  have hq : index i / 19 = 0 := by omega
  have hd : digit (index i) = i := by
    apply Fin.ext
    change ((min (index i) (19 - index i) - 1).toNat % 9) = i.val
    rw [min_eq_left (show index i ≤ 19 - index i by omega)]
    simp [index, Nat.mod_eq_of_lt i.isLt]
  rw [Z, ite_eq_right hn, hr, hq, hd, show sign 0 = 1 by decide, map_one, one_mul]

def w (i : Fin 9) : ZMod 19 :=
  (((9 - index i) * (10 - index i) / 2 : ℤ) : K)

-- The sparse computations below are connected to Mathlib by denote.
def sortWord (m : Word) : Word := m.insertionSort (fun i j => i ≤ j)

theorem exponent_perm {a b : Word} (h : a.Perm b) : exponent a = exponent b := by
  induction h with
  | nil => rfl
  | cons i h ih => simp only [exponent, ih]
  | swap i j p => simp [exponent, add_left_comm]
  | trans h h' ih ih' => exact ih.trans ih'

theorem exponent_sort (m : Word) : exponent (sortWord m) = exponent m :=
  exponent_perm (List.perm_insertionSort _ _)

private def wordKey (m : Word) : Nat := m.foldl (fun k i => 10*k + i.val + 1) 0

private def keep (m : Word) (c : K) (p : Sparse) : Sparse :=
  if c = 0 then p else (m,c) :: p

private def insertTerm (m : Word) (c : K) : Sparse → Sparse
  | [] => keep m c []
  | (n,d) :: q =>
    if m = n then keep m (c+d) q
    else if wordKey m ≤ wordKey n then keep m c ((n,d) :: q)
    else (n,d) :: insertTerm m c q

def normalize (p : Sparse) : Sparse := p.foldr (fun (m,c) q => insertTerm m c q) []

private theorem denote_keep (m : Word) (c : K) (p : Sparse) :
    denote (keep m c p) = term (m,c) + denote p := by
  unfold keep
  split <;> simp_all [term]

private theorem denote_insertTerm (m : Word) (c : K) (p : Sparse) :
    denote (insertTerm m c p) = term (m,c) + denote p := by
  induction p with
  | nil => exact denote_keep m c []
  | cons t q ih =>
    obtain ⟨n,d⟩ := t
    by_cases h : m = n
    · subst n
      simp [insertTerm, denote_keep, term, add_assoc]
    · by_cases hk : wordKey m ≤ wordKey n
      · simp [insertTerm, h, hk, denote_keep]
      · simp [insertTerm, h, hk, ih, add_left_comm]

theorem denote_normalize (p : Sparse) : denote (normalize p) = denote p := by
  induction p with
  | nil => rfl
  | cons t p ih =>
    obtain ⟨m,c⟩ := t
    change denote (insertTerm m c (normalize p)) = _
    rw [denote_insertTerm, ih, denote_cons]

theorem denote_append (p q : Sparse) : denote (p ++ q) = denote p + denote q := by
  simp [denote]

def timesTerm (a b : Word × K) : Word × K :=
  (sortWord (a.1 ++ b.1), a.2 * b.2)

theorem term_timesTerm (a b : Word × K) : term (timesTerm a b) = term a * term b := by
  simp [term, timesTerm, exponent_sort, exponent_append]

def rawMul (p q : Sparse) : Sparse := p.flatMap fun a => q.map (timesTerm a)
private def spMul (p q : Sparse) : Sparse := normalize (rawMul p q)

theorem denote_rawMul (p q : Sparse) : denote (rawMul p q) = denote p * denote q := by
  unfold rawMul
  induction p with
  | nil =>
    change denote [] = denote [] * denote q
    rw [denote_nil, zero_mul]
  | cons t p ih =>
    simp [List.flatMap_cons, denote_append, ih, add_mul]
    simp [denote, List.map_map, Function.comp_def, term_timesTerm, List.sum_map_mul_left]

private theorem denote_spMul (p q : Sparse) : denote (spMul p q) = denote p * denote q := by
  rw [spMul, denote_normalize, denote_rawMul]

private def scalar (c : K) : Sparse := [([], c)]

@[simp] private theorem denote_scalar (c : K) : denote (scalar c) = C c := by
  simp [scalar, term, exponent]

def wordWeight (m : Word) : K := (m.map w).sum

theorem exponent_weight (m : Word) : Finsupp.weight w (exponent m) = wordWeight m := by
  induction m with
  | nil => simp [wordWeight, exponent]
  | cons i m ih => simp [wordWeight, exponent, Finsupp.weight_single, ih]

theorem exponent_degree (m : Word) : (exponent m).degree = m.length := by
  induction m with
  | nil => simp [exponent]
  | cons i m ih => simp [exponent, ih, add_comm]

theorem denote_component (n : K) (p : Sparse) :
    denote (p.filter fun t => decide (n = wordWeight t.1)) =
      weightedHomogeneousComponent w n (denote p) := by
  induction p with
  | nil => simp
  | cons t p ih =>
    have ht := isWeightedHomogeneous_monomial w (exponent t.1) t.2 (exponent_weight t.1)
    by_cases h : n = wordWeight t.1
    · subst n
      simp [ih, term, weightedHomogeneousComponent_of_mem ht]
    · simp [h, ih, term, weightedHomogeneousComponent_of_mem ht]

private theorem Z_congr_38 {a b : ℤ} (h : a % 38 = b % 38) : Z a = Z b := by
  have hr : a % 19 = b % 19 := by omega
  have hs : sign (a/19) = sign (b/19) := by
    unfold sign
    have : (a/19) % 2 = (b/19) % 2 := by omega
    rw [this]
  rw [Z, Z, hr, hs]

theorem Z_remainder (x : ℤ) :
    Z x = C (sign (x/19)) * Z (x%19) := by
  have hm : (x%19) % 19 = x%19 := by omega
  have hq : (x%19) / 19 = 0 := by omega
  simp only [Z]
  rw [hm, hq, show sign 0 = 1 by decide]
  split <;> simp

noncomputable def T : R →ₐ[K] R :=
  aeval fun i => C (sign (index i + 1)) * Z (2 * index i)

theorem T_Z_base (i : Fin 9) :
    T (Z (index i)) = C (sign (index i + 1)) * Z (2 * index i) := by
  rw [Z_base]
  exact aeval_X _ _

private theorem T_Z_reduced (r : ℤ) (h0 : 0 ≤ r) (h19 : r < 19) :
    T (Z r) = C (sign (r+1)) * Z (2*r) := by
  have low (u : ℤ) (hu : 0 < u) (hu' : u ≤ 9) :
      T (Z u) = C (sign (u+1)) * Z (2*u) := by
    let i : Fin 9 := ⟨(u-1).toNat, by omega⟩
    have hi : index i = u := by
      change ((u-1).toNat : ℤ) + 1 = u
      omega
    simpa only [hi] using T_Z_base i
  by_cases hr : r = 0
  · subst r
    have hzero : Z 0 = 0 := Z_mul19 0
    simp [hzero]
  by_cases h9 : r ≤ 9
  · exact low r (by omega) h9
  have hz : Z (2*(19-r)) = -Z (2*r) := by
    rw [Z_congr_38 (b := -(2*r)) (by omega), Z_neg]
  have hs : sign (19-r+1) = -sign (r+1) := by
    rw [← sign_succ]
    unfold sign
    have : (19-r+1) % 2 = (r+1+1) % 2 := by omega
    rw [this]
  calc
    T (Z r) = T (Z (19-r)) := by rw [Z_reflect]
    _ = C (sign (19-r+1)) * Z (2*(19-r)) := low _ (by omega) (by omega)
    _ = C (sign (r+1)) * Z (2*r) := by rw [hs, hz, map_neg, neg_mul_neg]

theorem T_Z (x : ℤ) : T (Z x) = C (sign (x+1)) * Z (2*x) := by
  have hz : Z (2*(x%19)) = Z (2*x) := Z_congr_38 (by omega)
  have hs : sign (x+1) = sign (x/19 + (x%19+1)) := by
    unfold sign
    have : (x+1) % 2 = (x/19 + (x%19+1)) % 2 := by omega
    rw [this]
  have hc : T (C (sign (x/19))) = C (sign (x/19)) := by simp
  rw [Z_remainder x, map_mul, T_Z_reduced _ (by omega) (by omega), hz, hc,
    ← mul_assoc, ← map_mul, ← sign_add, ← hs]

private theorem T_pair (u v : ℤ) :
    T (Z (u+v) * Z (u-v)) = Z (2*u+2*v) * Z (2*u-2*v) := by
  have hs : sign (u+v+1) * sign (u-v+1) = 1 := by
    rw [← sign_add]
    unfold sign
    rw [ite_eq_left (by omega)]
  rw [map_mul, T_Z, T_Z, show 2*(u+v) = 2*u+2*v by omega,
    show 2*(u-v) = 2*u-2*v by omega]
  rw [mul_mul_mul_comm, ← map_mul, hs, map_one, one_mul]

private abbrev Indices := ℤ × ℤ × ℤ × ℤ

private def double : Indices → Indices
  | (a,b,c,d) => (2*a,2*b,2*c,2*d)

noncomputable def theta : (ℤ × ℤ × ℤ × ℤ) → MvPolynomial (Fin 9) (ZMod 19)
  | (a,b,c,d) => (Z (a+d) * Z (a-d)) * (Z (b+c) * Z (b-c))
      - (Z (a+c) * Z (a-c)) * (Z (b+d) * Z (b-d))
      + (Z (a+b) * Z (a-b)) * (Z (c+d) * Z (c-d))

private theorem T_theta (x : Indices) : T (theta x) = theta (double x) := by
  obtain ⟨a,b,c,d⟩ := x
  simp only [double, theta, map_add, map_sub,
    map_mul T (_ * _) (_ * _), T_pair]

noncomputable def ITheta : Ideal (MvPolynomial (Fin 9) (ZMod 19)) := Ideal.span (Set.range theta)

def sparseSum {α : Type} (xs : List α) (f : α → Sparse) : Sparse := xs.flatMap f

theorem denote_sparseSum {α : Type} (xs : List α) (f : α → Sparse) :
    denote (sparseSum xs f) = (xs.map fun x => denote (f x)).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    change denote (f x ++ sparseSum xs f) = _
    rw [denote_append, ih]
    rfl

def scale (c : K) (p : Sparse) : Sparse :=
  p.map fun (m,d) => (m, c*d)

theorem denote_scale (c : K) (p : Sparse) : denote (scale c p) = C c * denote p := by
  induction p with
  | nil => simp [scale]
  | cons t p ih =>
    obtain ⟨m,d⟩ := t
    change term (m,c*d) + denote (scale c p) = C c * (term (m,d) + denote p)
    simp [ih, term, C_mul_monomial, mul_add]

private def spPair (u v : ℤ) : Sparse := spMul (zTerms (u+v)) (zTerms (u-v))

private def spTheta : Indices → Sparse
  | (a,b,c,d) => spMul (spPair a d) (spPair b c)
      ++ scale (-1) (spMul (spPair a c) (spPair b d))
      ++ spMul (spPair a b) (spPair c d)

private theorem denote_spPair (u v : ℤ) :
    denote (spPair u v) = Z (u+v) * Z (u-v) := by
  rw [spPair, denote_spMul, denote_zTerms, denote_zTerms]

private theorem denote_spTheta (x : Indices) : denote (spTheta x) = theta x := by
  obtain ⟨a,b,c,d⟩ := x
  simp [spTheta, theta, denote_append, denote_spMul, denote_spPair, denote_scale,
    sub_eq_add_neg, add_assoc]

private def paperIndices : List ℤ := List.map (fun j : ℕ => Int.ofNat j + 1) (List.range 9)

private def paperPairs : List (ℤ × ℤ) :=
  paperIndices.flatMap fun a => (paperIndices.filter fun b => a < b).map fun b => (a,b)

private theorem mem_paperIndices (a : ℤ) : a ∈ paperIndices ↔ 1 ≤ a ∧ a ≤ 9 := by
  simp only [paperIndices, List.mem_map]
  constructor
  · rintro ⟨j,hj,rfl⟩
    have hj' := List.mem_range.mp hj
    change 1 ≤ (j : ℤ) + 1 ∧ (j : ℤ) + 1 ≤ 9
    omega
  · intro h
    refine ⟨(a-1).toNat, List.mem_range.mpr (by omega), ?_⟩
    change ((a-1).toNat : ℤ) + 1 = a
    omega

private theorem mem_paperPairs (a b : ℤ) : (a,b) ∈ paperPairs ↔ 1 ≤ a ∧ a < b ∧ b ≤ 9 := by
  simp [paperPairs, mem_paperIndices, and_assoc]
  omega

def cCoefficient (a : ℤ) : K := sign a * 2 * (a : K)

def bCoefficient (a b : ℤ) : K :=
  -3 * sign (a+b) * (a : K) * (b : K) * ((b : K)^2 - (a : K)^2)

private theorem paperIndices_toFinset : paperIndices.toFinset = Finset.Icc 1 9 := by
  ext a
  simp [mem_paperIndices]

private theorem paperPairs_toFinset :
    paperPairs.toFinset =
      ((Finset.Icc (1 : ℤ) 9) ×ˢ (Finset.Icc (1 : ℤ) 9)).filter (fun p => p.1 < p.2) := by
  ext ⟨a, b⟩
  simp only [List.mem_toFinset, mem_paperPairs, Finset.mem_filter, Finset.mem_product,
    Finset.mem_Icc]
  omega

/-- The sum in Section 6.1 over all nine indices. -/
noncomputable def paperC : MvPolynomial (Fin 9) (ZMod 19) :=
  ∑ a ∈ Finset.Icc 1 9, C (cCoefficient a) * Z a

/-- The sum in Section 6.1 over every increasing pair of paper indices. -/
noncomputable def paperB : MvPolynomial (Fin 9) (ZMod 19) :=
  ∑ p ∈ ((Finset.Icc (1 : ℤ) 9) ×ˢ (Finset.Icc (1 : ℤ) 9)).filter (fun p => p.1 < p.2),
    C (bCoefficient p.1 p.2) * ((Z p.1 * Z p.2) * (Z (p.1 + p.2) * Z (p.2 - p.1)))

noncomputable def F11 : R :=
  weightedHomogeneousComponent w (11 : K) (paperB * paperC ^ 3)

def fullC : Sparse :=
  normalize (sparseSum paperIndices fun a => scale (cCoefficient a) (zTerms a))

def fullB : Sparse :=
  normalize (sparseSum paperPairs fun (a,b) => scale (bCoefficient a b)
    (spMul (spMul (zTerms a) (zTerms b)) (spMul (zTerms (a+b)) (zTerms (b-a)))))

theorem denote_fullC : denote fullC = paperC := by
  have h : paperIndices.Nodup := by decide
  rw [paperC, ← paperIndices_toFinset, List.sum_toFinset _ h]
  simp only [fullC, denote_normalize, denote_sparseSum, denote_scale, denote_zTerms]

theorem denote_fullB : denote fullB = paperB := by
  have h : paperPairs.Nodup := by decide
  rw [paperB, ← paperPairs_toFinset, List.sum_toFinset _ h]
  simp only [fullB, denote_normalize, denote_sparseSum, denote_scale, denote_spMul, denote_zTerms]

private def leftSparse : Sparse :=
  (rawMul fullB (spMul (spMul fullC fullC) fullC)).filter fun t => decide (11 = wordWeight t.1)

private theorem denote_leftSparse : denote leftSparse = F11 := by
  rw [leftSparse, denote_component]
  simp only [F11, denote_rawMul, denote_spMul, denote_fullB, denote_fullC, pow_succ,
    pow_zero, one_mul]

noncomputable def S_Z : MvPolynomial (Fin 9) (ZMod 19) :=
  Z 1 * Z 7 * Z 8 - Z 2 * Z 3 * Z 5 + Z 4 * Z 6 * Z 9

noncomputable def Tpow : ℕ → R →ₐ[K] R
  | 0 => AlgHom.id K R
  | j+1 => (Tpow j).comp T

private def doubleIter : ℕ → Indices → Indices
  | 0, x => x
  | j+1, x => doubleIter j (double x)

theorem Tpow_theta (j : ℕ) (x : Indices) : Tpow j (theta x) = theta (doubleIter j x) := by
  induction j generalizing x with
  | zero => rfl
  | succ j ih => simpa only [Tpow, doubleIter, AlgHom.comp_apply, T_theta] using ih (double x)

private def zOrbitTerms : ℕ → ℤ → Sparse
  | 0, x => zTerms x
  | j+1, x => scale (sign (x+1)) (zOrbitTerms j (2*x))

private theorem denote_zOrbitTerms (j : ℕ) (x : ℤ) :
    denote (zOrbitTerms j x) = Tpow j (Z x) := by
  induction j generalizing x with
  | zero => exact denote_zTerms x
  | succ j ih =>
    have hc : Tpow j (C (sign (x+1))) = C (sign (x+1)) := by simp
    simp only [zOrbitTerms, denote_scale, ih, Tpow, AlgHom.comp_apply, T_Z, map_mul, hc]

noncomputable def monomialWord (digits : List ℤ) : R := (digits.map Z).prod

def orbitWordSparse (j : ℕ) : List ℤ → Sparse
  | [] => scalar 1
  | x :: xs => spMul (zOrbitTerms j x) (orbitWordSparse j xs)

theorem denote_orbitWordSparse (j : ℕ) (digits : List ℤ) :
    denote (orbitWordSparse j digits) = Tpow j (monomialWord digits) := by
  induction digits with
  | nil => simp [orbitWordSparse, monomialWord]
  | cons x xs ih =>
    simp [orbitWordSparse, denote_spMul, denote_zOrbitTerms, ih, monomialWord]

def sSparse : Sparse :=
  orbitWordSparse 0 [1,7,8] ++ scale (-1) (orbitWordSparse 0 [2,3,5])
    ++ orbitWordSparse 0 [4,6,9]

theorem denote_sSparse : denote sSparse = S_Z := by
  simp [sSparse, S_Z, denote_append, denote_scale, denote_orbitWordSparse,
    Tpow, monomialWord, sub_eq_add_neg, mul_assoc, add_assoc]

private def orbitScalar (j : ℕ) : K := (5 : K)^j


private def orbitSteps : List ℕ := List.range 9

private noncomputable def orbitSum (p : R) : R :=
  (orbitSteps.map fun j => C (orbitScalar j) * Tpow j p).sum

private noncomputable def Q : R :=
  orbitSum (C 6 * monomialWord [1,2,3,9] + C 14 * monomialWord [1,1,5,7])

private def qSparse : Sparse := normalize (sparseSum orbitSteps fun j =>
    scale (orbitScalar j)
      (scale 6 (orbitWordSparse j [1,2,3,9]) ++ scale 14 (orbitWordSparse j [1,1,5,7])))

private theorem denote_qSparse : denote qSparse = Q := by
  have hc (j : ℕ) (c : K) : Tpow j (C c) = C c := by simp
  simp only [qSparse, Q, orbitSum, denote_normalize, denote_sparseSum, denote_scale,
    denote_append, denote_orbitWordSparse, map_add, map_mul, hc]

private structure Seed where
  coefficient : K
  digits : List ℤ
  args : Indices

private def seeds (first : K) : List Seed :=
  [⟨first, [5,6,7], (0,1,2,4)⟩,
   ⟨6, [2,5,9], (0,1,2,4)⟩,
   ⟨2, [1,2,7], (0,1,2,5)⟩,
   ⟨18, [1,1,7], (0,1,2,6)⟩,
   ⟨15, [2,4,9], (0,1,3,5)⟩,
   ⟨1, [2,2,6], (0,1,3,5)⟩,
   ⟨11, [4,4,9], (0,2,3,4)⟩,
   ⟨17, [1,4,8], (0,2,4,5)⟩,
   ⟨4, [6,7,9], (0,3,4,5)⟩,
   ⟨14, [2,4,4], (1,2,3,5)⟩,
   ⟨4, [1,3,3], (1,2,4,6)⟩,
   ⟨2, [3,7,7], (1,3,4,5)⟩,
   ⟨8, [3,4,5], (1,3,4,5)⟩]

private noncomputable def orbitRelations (first : K) : R :=
  ((seeds first).map fun row =>
    C row.coefficient * orbitSum (monomialWord row.digits * theta row.args)).sum

private def relationSparse (first : K) : Sparse :=
  sparseSum (seeds first) fun row =>
    scale row.coefficient (sparseSum orbitSteps fun j =>
      scale (orbitScalar j)
        (spMul (orbitWordSparse j row.digits) (spTheta (doubleIter j row.args))))

private theorem denote_relationSparse (first : K) :
    denote (relationSparse first) = orbitRelations first := by
  simp only [relationSparse, orbitRelations, orbitSum, denote_sparseSum, denote_scale, denote_spMul,
    denote_orbitWordSparse, denote_spTheta, map_mul, Tpow_theta]

private def rightSparse (first : K) : Sparse := spMul sSparse qSparse ++ relationSparse first

private theorem denote_rightSparse (first : K) :
    denote (rightSparse first) = S_Z * Q + orbitRelations first := by
  simp only [rightSparse, denote_append, denote_spMul, denote_sSparse, denote_qSparse,
    denote_relationSparse]

theorem denote_grades (p : Sparse) (d : ℕ) (n : K)
    (h : ∀ t ∈ p, t.1.length = d ∧ wordWeight t.1 = n) :
    (denote p).IsHomogeneous d ∧ (denote p).IsWeightedHomogeneous w n := by
  induction p with
  | nil => exact ⟨isHomogeneous_zero _ _ _, isWeightedHomogeneous_zero _ _ _⟩
  | cons t p ih =>
    have ht := h t (by simp)
    have hp := ih (fun u hu => h u (by simp [hu]))
    exact ⟨
      (isHomogeneous_monomial t.2 ((exponent_degree t.1).trans ht.1)).add hp.1,
      (isWeightedHomogeneous_monomial w _ _ ((exponent_weight t.1).trans ht.2)).add hp.2⟩

private theorem relations_mem (first : K) : orbitRelations first ∈ ITheta := by
  unfold orbitRelations
  apply list_sum_mem
  intro p hp
  obtain ⟨row, _, rfl⟩ := List.mem_map.mp hp
  apply Ideal.mul_mem_left
  unfold orbitSum
  apply list_sum_mem
  intro p hp
  obtain ⟨j, _, rfl⟩ := List.mem_map.mp hp
  rw [map_mul, Tpow_theta]
  exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_left _ _
    (Ideal.subset_span ⟨doubleIter j row.args, rfl⟩))

private theorem Z_shift_multiple (u k : ℤ) :
    Z (u + 19*k) = C (sign k) * Z u := by
  have hm : (u + 19*k) % 19 = u % 19 := by omega
  have hd : (u + 19*k) / 19 = k + u / 19 := by omega
  rw [Z, Z, hm, hd, sign_add, map_mul]
  split <;> simp [mul_assoc]

noncomputable def pair (u v : ℤ) : R := Z (u+v) * Z (u-v)

private theorem pair_shift (u v k l : ℤ) :
    pair (u+19*k) (v+19*l) = pair u v := by
  have hs : sign (k+l) * sign (k-l) = 1 := by
    rw [← sign_add]
    unfold sign
    rw [ite_eq_left (by omega)]
  rw [pair, pair,
      show u+19*k+(v+19*l) = u+v+19*(k+l) by ring,
      show u+19*k-(v+19*l) = u-v+19*(k-l) by ring,
      Z_shift_multiple, Z_shift_multiple, mul_mul_mul_comm, ← map_mul, hs, map_one, one_mul]

private theorem pair_neg_left (u v : ℤ) : pair (-u) v = pair u v := by
  rw [pair, pair, show -u+v = -(u-v) by ring, show -u-v = -(u+v) by ring, Z_neg, Z_neg,
    neg_mul_neg, mul_comm]

private theorem pair_neg_right (u v : ℤ) : pair u (-v) = pair u v := by
  simp [pair, sub_eq_add_neg, mul_comm]

def representative (x : ℤ) : ℤ := min (x % 19) (19 - x % 19)

theorem representative_bounds (x : ℤ) :
    0 ≤ representative x ∧ representative x < 10 := by
  unfold representative
  omega

private theorem pair_reduce_left (u v : ℤ) : pair u v = pair (representative u) v := by
  have h : pair u v = pair (u%19) v := by
    simpa only [Int.mul_zero, Int.add_zero, show u%19+19*(u/19) = u by omega]
      using pair_shift (u%19) v (u/19) 0
  by_cases hl : u%19 ≤ 19-u%19
  · simpa only [representative, min_eq_left hl] using h
  · have h' : pair (19-u%19) v = pair (u%19) v := by
      have h'' := pair_shift (-(u%19)) v 1 0
      simpa only [Int.mul_zero, Int.add_zero, pair_neg_left,
        show -(u%19)+19*1 = 19-u%19 by ring] using h''
    rw [representative, min_eq_right (le_of_not_ge hl), h, h']

private theorem pair_reduce_right (u v : ℤ) : pair u v = pair u (representative v) := by
  have h : pair u v = pair u (v%19) := by
    simpa only [Int.mul_zero, Int.add_zero, show v%19+19*(v/19) = v by omega]
      using pair_shift u (v%19) 0 (v/19)
  by_cases hl : v%19 ≤ 19-v%19
  · simpa only [representative, min_eq_left hl] using h
  · have h' : pair u (19-v%19) = pair u (v%19) := by
      have h'' := pair_shift u (-(v%19)) 0 1
      simpa only [Int.mul_zero, Int.add_zero, pair_neg_right,
        show -(v%19)+19*1 = 19-v%19 by ring] using h''
    rw [representative, min_eq_right (le_of_not_ge hl), h, h']

theorem theta_reduce (a b c d : ℤ) :
    theta (a,b,c,d) =
      theta (representative a, representative b, representative c, representative d) := by
  change pair a d * pair b c - pair a c * pair b d + pair a b * pair c d = _
  rw [pair_reduce_left a d, pair_reduce_left b c, pair_reduce_left a c,
    pair_reduce_left b d, pair_reduce_left a b, pair_reduce_left c d,
    pair_reduce_right (representative a) d, pair_reduce_right (representative b) c,
    pair_reduce_right (representative a) c, pair_reduce_right (representative b) d,
    pair_reduce_right (representative a) b, pair_reduce_right (representative c) d]
  rfl

def tNatural (i : Fin 9) : ℕ := (9 - index i).toNat * (10 - index i).toNat / 2

def traceDegree (m : Word) : ℕ := (m.map tNatural).sum

noncomputable def trace : R →ₐ[K] Polynomial K :=
  aeval fun i => Polynomial.X ^ tNatural i

private theorem trace_term (m : Word) (c : K) :
    trace (term (m,c)) = Polynomial.monomial (traceDegree m) c := by
  induction m with
  | nil =>
    change trace (monomial 0 c) = Polynomial.monomial 0 c
    simp [trace, ← Polynomial.C_mul_X_pow_eq_monomial]
  | cons i m ih =>
    have ht : term (i::m,c) = X i * term (m,c) := by
      simp [term, exponent, MvPolynomial.X]
    rw [ht, map_mul, ih, show trace (X i) = Polynomial.X ^ tNatural i from aeval_X _ _]
    rw [← Polynomial.C_mul_X_pow_eq_monomial, ← Polynomial.C_mul_X_pow_eq_monomial]
    simp [traceDegree, pow_add, mul_left_comm]

def traceCoeff (n : ℕ) (p : Sparse) : K :=
  (p.map fun (m,c) => if traceDegree m = n then c else 0).sum

theorem trace_coeff (n : ℕ) (p : Sparse) :
    (trace (denote p)).coeff n = traceCoeff n p := by
  induction p with
  | nil => simp [traceCoeff]
  | cons t p ih =>
    obtain ⟨m,c⟩ := t
    rw [denote_cons, map_add, Polynomial.coeff_add, trace_term, ih]
    simp [traceCoeff, Polynomial.coeff_monomial]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem theta_trace_low (x : Indices) (n : ℕ) (hn : n < 10) :
    (trace (theta x)).coeff n = 0 := by
  obtain ⟨a,b,c,d⟩ := x
  let toFin (x : ℤ) : Fin 10 := ⟨(representative x).toNat, by
    have := representative_bounds x
    omega⟩
  have cast_toFin (x : ℤ) : ((toFin x).val : ℤ) = representative x := by
    change ((representative x).toNat : ℤ) = representative x
    have := representative_bounds x
    omega
  let finTheta (a b c d : Fin 10) : Sparse :=
    spTheta ((a.val : ℤ), (b.val : ℤ), (c.val : ℤ), (d.val : ℤ))
  let vanishesOnSupport (p : Sparse) : Bool :=
    p.all fun t => if traceDegree t.1 < 10 then decide (traceCoeff (traceDegree t.1) p = 0)
      else true
  let checkSlice (a : Fin 10) : Bool :=
    (List.finRange 10).all fun b => (List.finRange 10).all fun c => (List.finRange 10).all fun d =>
      vanishesOnSupport (finTheta a b c d)
  -- Discharge the representative cases in the proof of the integer-indexed statement.
  have checked (r : Fin 10) : checkSlice r = true := by
    dsimp only [checkSlice, finTheta, vanishesOnSupport]
    fin_cases r <;> decide
  have hc := checked (toFin a)
  let p := finTheta (toFin a) (toFin b) (toFin c) (toFin d)
  have hs : vanishesOnSupport p = true :=
    List.all_eq_true.mp (List.all_eq_true.mp (List.all_eq_true.mp hc
      (toFin b) (List.mem_finRange _)) (toFin c) (List.mem_finRange _))
      (toFin d) (List.mem_finRange _)
  have hcoeff : traceCoeff n p = 0 := by
    by_cases he : ∃ t ∈ p, traceDegree t.1 = n
    · obtain ⟨t, ht, hw⟩ := he
      have h := List.all_eq_true.mp hs t ht
      simpa [hw, hn] using h
    · simp only [not_exists, not_and] at he
      unfold traceCoeff
      apply List.sum_eq_zero
      intro c hc
      obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hc
      exact ite_eq_right (he t ht)
  rw [theta_reduce, ← denote_spTheta, trace_coeff]
  simpa only [p, finTheta, cast_toFin] using hcoeff

private noncomputable def traceIdeal : Ideal (Polynomial K) :=
  Ideal.span {Polynomial.X ^ 10}

private theorem theta_le_traceIdeal : ITheta ≤ Ideal.comap trace.toRingHom traceIdeal := by
  apply Ideal.span_le.mpr
  rintro _ ⟨x,rfl⟩
  change trace (theta x) ∈ traceIdeal
  rw [traceIdeal, Ideal.mem_span_singleton, Polynomial.X_pow_dvd_iff]
  exact theta_trace_low x

private theorem quotient_ne_zero_of_trace_coeff (p : R) (n : ℕ) (hn : n < 10)
    (hcoeff : (trace p).coeff n ≠ 0) : Ideal.Quotient.mk ITheta p ≠ 0 := by
  intro he
  have hm := theta_le_traceIdeal (Ideal.Quotient.eq_zero_iff_mem.mp he)
  change trace p ∈ traceIdeal at hm
  rw [traceIdeal, Ideal.mem_span_singleton, Polynomial.X_pow_dvd_iff] at hm
  exact hcoeff (hm n hn)

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
/-- The algebraic existence clause of Bilgici's Question 1, with a cofactor whose class
is nonzero in the same theta quotient. -/
theorem result :
    ∃ q : MvPolynomial (Fin 9) (ZMod 19),
      q ≠ 0 ∧ q.IsHomogeneous 4 ∧ q.IsWeightedHomogeneous w (9 : ZMod 19) ∧
      (weightedHomogeneousComponent w (11 : ZMod 19) (paperB * paperC ^ 3) - S_Z * q
        ∈ Ideal.span (Set.range theta)) ∧ Ideal.Quotient.mk ITheta q ≠ 0 := by
  have hgrades : Q.IsHomogeneous 4 ∧ Q.IsWeightedHomogeneous w (9 : K) := by
    rw [← denote_qSparse]
    apply denote_grades
    have h : qSparse.all (fun t => decide (t.1.length = 4 ∧ wordWeight t.1 = (9 : K))) := by
      decide
    simpa only [List.all_eq_true, decide_eq_true_eq] using h
  have hclass : Ideal.Quotient.mk ITheta Q ≠ 0 := by
    apply quotient_ne_zero_of_trace_coeff Q 9 (by decide)
    rw [← denote_qSparse, trace_coeff]
    decide
  refine ⟨Q, fun h => hclass (by rw [h, map_zero]), hgrades.1, hgrades.2, ?_, hclass⟩
  change F11 - S_Z * Q ∈ ITheta
  -- Compare the complete normalized degree-seven polynomials.
  have hsparse : normalize leftSparse = normalize (rightSparse 3) := by decide
  have hpoly : F11 = S_Z * Q + orbitRelations 3 := by
    simpa only [denote_normalize, denote_leftSparse, denote_rightSparse] using congrArg denote hsparse
  rw [hpoly, add_comm, add_sub_cancel_right]
  exact relations_mem 3

end D5.S3.Arith.Partitions.BilgiciThetaQuartic
