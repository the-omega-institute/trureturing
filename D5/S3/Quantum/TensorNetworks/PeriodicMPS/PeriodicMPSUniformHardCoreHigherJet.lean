/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSUniformHardCoreHigherJet
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSUniformHardCoreHigherJet
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: [lake/module/D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSUniformHardCoreFirstJet]
   utility: none
   digest: Sparse coefficient calculations and the transfer recurrence certify quadratic through quartic raw marginal coefficients from length seven onward. -/
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSUniformHardCoreFirstJet
import Mathlib.Data.Nat.Factorization.Defs
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Tactic.Eval

/-!
# Higher raw coefficients of the uniform hard-core transfer

The five slots use η = i ε. Integer monomials have prime-product keys, and their
specialization gives complex Taylor coefficients of the actual raw two-site transfer.
The Python certificate supplies the candidate weights. Lean checks the 6, 8, and 10
initial lengths for each of its seven entries and applies the length recurrence.
-/

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.PeriodicMPSUniformHardCoreHigherJet

open PeriodicMPSUniformHardCoreTransferRecurrence
open PeriodicMPSUniformHardCoreFirstJet (entry)
open Polynomial
open scoped Matrix Kronecker

/-- Parameters in the order t, β, a₂, b₂, c₂, d₂, b₃, c₃, d₃, a₄, b₄, c₄, d₄. -/
abbrev Parameters := Fin 13 → ℝ

def primeCode (i : Fin 13) : ℕ :=
  ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41] i

private theorem primeCode_prime (i : Fin 13) : (primeCode i).Prime := by
  fin_cases i <;> decide

private theorem primeCode_injective : Function.Injective primeCode := by
  intro i j h
  fin_cases i <;> fin_cases j <;> first | rfl | contradiction

/-- A monomial is encoded by the product of prime codes for its factors.
The list stores (monomial code, integer coefficient) pairs. -/
abbrev Sparse := List (ℕ × ℤ)

namespace Sparse

def term (m : ℕ) (a : ℤ) : Sparse := if a = 0 then [] else [(m, a)]

def insert (m : ℕ) (a : ℤ) : Sparse → Sparse
  | [] => term m a
  | (k, b) :: tail =>
    if m = k then
      if a + b = 0 then tail else (k, a + b) :: tail
    else if m < k then term m a ++ (k, b) :: tail
    else (k, b) :: insert m a tail

def add (p q : Sparse) : Sparse := p.foldr (fun (m, a) acc => insert m a acc) q

def scale (z : ℤ) (p : Sparse) : Sparse :=
  p.foldr (fun (m, a) acc => term m (z * a) ++ acc) []

def addProducts (m : ℕ) (a : ℤ) (q acc : Sparse) : Sparse :=
  q.foldr (fun (k, b) s => insert (m * k) (a * b) s) acc

def mul (p q : Sparse) : Sparse :=
  p.foldr (fun (m, a) acc => addProducts m a q acc) []

noncomputable section

def monomialValue (x : Parameters) (m : ℕ) : ℝ :=
  if m = 0 then 0 else ∏ i : Fin 13, x i ^ m.factorization (primeCode i)

@[simp] theorem monomialValue_one (x : Parameters) : monomialValue x 1 = 1 := by
  simp [monomialValue]

@[simp] theorem monomialValue_primeCode (x : Parameters) (i : Fin 13) :
    monomialValue x (primeCode i) = x i := by
  have hp := primeCode_prime i
  rw [monomialValue, ite_eq_right hp.ne_zero, hp.factorization]
  rw [Finset.prod_eq_single i]
  · simp
  · intro j _ hj
    simp [Finsupp.single_eq_of_ne (mt (fun h => primeCode_injective h) hj)]
  · simp

theorem monomialValue_mul (x : Parameters) (m k : ℕ) :
    monomialValue x (m * k) = monomialValue x m * monomialValue x k := by
  rcases eq_or_ne m 0 with rfl | hm
  · simp [monomialValue]
  rcases eq_or_ne k 0 with rfl | hk
  · simp [monomialValue]
  simp [monomialValue, hm, hk, mul_ne_zero hm hk, Nat.factorization_mul hm hk,
    pow_add, Finset.prod_mul_distrib]

def value (x : Parameters) : Sparse → ℝ
  | [] => 0
  | (m, a) :: p => (a : ℝ) * monomialValue x m + value x p

@[simp] theorem value_nil (x : Parameters) : value x [] = 0 := rfl

@[simp] theorem value_append (x : Parameters) (p q : Sparse) :
    value x (p ++ q) = value x p + value x q := by
  induction p with
  | nil => simp
  | cons hd tl ih =>
    rcases hd with ⟨m, a⟩
    simp [value, ih, add_assoc]

@[simp] theorem value_term (x : Parameters) (m : ℕ) (a : ℤ) :
    value x (term m a) = (a : ℝ) * monomialValue x m := by
  by_cases ha : a = 0 <;> simp [term, value, ha]

theorem value_insert (x : Parameters) (m : ℕ) (a : ℤ) (p : Sparse) :
    value x (insert m a p) = (a : ℝ) * monomialValue x m + value x p := by
  induction p with
  | nil => simp [insert]
  | cons hd tl ih =>
    rcases hd with ⟨k, b⟩
    by_cases he : m = k
    · subst k
      by_cases hz : a + b = 0
      · simp only [insert, ite_true, ite_eq_left hz, value]
        rw [← add_assoc, ← add_mul, ← Int.cast_add, hz, Int.cast_zero, zero_mul, zero_add]
      · simp [insert, value, hz, add_mul, add_assoc]
    · by_cases hl : m < k
      · simp [insert, he, hl]
      · simp [insert, he, hl, value, ih, add_left_comm]

@[simp] theorem value_add (x : Parameters) (p q : Sparse) :
    value x (add p q) = value x p + value x q := by
  induction p with
  | nil => simp [add]
  | cons hd tl ih =>
    rcases hd with ⟨m, a⟩
    change value x (insert m a (add tl q)) = _
    rw [value_insert, ih]
    simp [value, add_assoc]

@[simp] theorem value_scale (x : Parameters) (z : ℤ) (p : Sparse) :
    value x (scale z p) = (z : ℝ) * value x p := by
  induction p with
  | nil => simp [scale]
  | cons hd tl ih =>
    rcases hd with ⟨m, a⟩
    change value x (term m (z * a) ++ scale z tl) = _
    simp [ih, value, mul_add, mul_assoc]

private theorem value_addProducts (x : Parameters) (m : ℕ) (a : ℤ) (q acc : Sparse) :
    value x (addProducts m a q acc) =
      (a * monomialValue x m) * value x q + value x acc := by
  induction q with
  | nil => simp [addProducts]
  | cons hd tl ih =>
    rcases hd with ⟨k, b⟩
    change value x (insert (m * k) (a * b) (addProducts m a tl acc)) = _
    simp only [value_insert, ih,
      Int.cast_mul, monomialValue_mul, value]
    ring

@[simp] theorem value_mul (x : Parameters) (p q : Sparse) :
    value x (mul p q) = value x p * value x q := by
  induction p with
  | nil => simp [mul]
  | cons hd tl ih =>
    rcases hd with ⟨m, a⟩
    change value x (addProducts m a q (mul tl q)) = _
    simp only [value_addProducts, ih, value, add_mul]

end
end Sparse

/-- The five coefficients in the auxiliary variable η = i ε. -/
abbrev Jet := Vector Sparse 5

namespace Jet

def zero : Jet := Vector.replicate 5 []
def one : Jet := #v[[(1, 1)], [], [], [], []]

def add (a b : Jet) : Jet := Vector.ofFn fun i => Sparse.add a[i] b[i]

def mul (a b : Jet) : Jet := Vector.ofFn fun i =>
  (List.range (i.val + 1)).foldr
    (fun j s => Sparse.add (Sparse.mul (a.toArray[j]?.getD []) (b.toArray[i.val - j]?.getD [])) s) []

noncomputable section

def value (x : Parameters) (a : Jet) (r : Fin 5) : ℂ :=
  Complex.I ^ r.val * (Sparse.value x a[r.val] : ℂ)

def Matches (x : Parameters) (a : Jet) (p : Polynomial ℂ) : Prop :=
  ∀ r : Fin 5, value x a r = p.coeff r

theorem matches_zero (x : Parameters) : Matches x zero 0 := by
  intro r
  simp [value, zero]

theorem matches_one (x : Parameters) : Matches x one 1 := by
  intro r
  fin_cases r <;> simp [value, one, Sparse.value, coeff_one]

theorem matches_add {x : Parameters} {a b : Jet} {p q : Polynomial ℂ}
    (ha : Matches x a p) (hb : Matches x b q) : Matches x (add a b) (p + q) := by
  intro r
  rw [coeff_add, ← ha r, ← hb r]
  simp [value, add, mul_add]

private theorem value_fold (x : Parameters) (l : List ℕ) (f : ℕ → Sparse) :
    Sparse.value x (l.foldr (fun k s => Sparse.add (f k) s) []) =
      (l.map fun k => Sparse.value x (f k)).sum := by
  induction l <;> simp [*]

theorem matches_mul {x : Parameters} {a b : Jet} {p q : Polynomial ℂ}
    (ha : Matches x a p) (hb : Matches x b q) : Matches x (mul a b) (p * q) := by
  intro r
  simp only [value, mul, Vector.getElem_ofFn, value_fold]
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  have hsum (f : ℕ → ℂ) :
      (∑ j ∈ Finset.range (r.val + 1), f j) = ((List.range (r.val + 1)).map f).sum := by
    rw [← List.toFinset_range, List.sum_toFinset _ List.nodup_range]
  rw [hsum]
  change Complex.I ^ r.val * Complex.ofRealHom ((List.map _ _).sum) = _
  have hmul (z : ℂ) (l : List ℂ) : z * l.sum = (l.map (z * ·)).sum := by
    induction l <;> simp [mul_add, *]
  rw [map_list_sum, hmul]
  simp only [List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro j hj
  have hj' : j ≤ r.val := by simpa using List.mem_range.mp hj
  have h₁ : j < 5 := lt_of_le_of_lt hj' r.isLt
  have h₂ : r.val - j < 5 := by omega
  rw [← ha ⟨j, h₁⟩, ← hb ⟨r.val - j, h₂⟩]
  simp only [value, Function.comp_apply, Sparse.value_mul]
  rw [Array.getElem?_eq_getElem (by simpa using h₁),
    Array.getElem?_eq_getElem (by simpa using h₂)]
  change Complex.I ^ r.val * _ =
    (Complex.I ^ j * (Sparse.value x a[j] : ℂ)) *
      (Complex.I ^ (r.val - j) * (Sparse.value x b[r.val - j] : ℂ))
  have hpow : Complex.I ^ r.val = Complex.I ^ j * Complex.I ^ (r.val - j) :=
    (congrArg (Complex.I ^ ·) (show r.val = j + (r.val - j) by omega)).trans (pow_add _ _ _)
  rw [hpow]
  change (Complex.I ^ j * Complex.I ^ (r.val - j)) *
      ((Sparse.value x a[j] * Sparse.value x b[r.val - j] : ℝ) : ℂ) = _
  rw [Complex.ofReal_mul]
  ring

end
end Jet

namespace Jet

def conjugate (a : Jet) : Jet :=
  Vector.ofFn fun r => Sparse.scale ((-1) ^ r.val) a[r.val]

def sum {α : Type*} (l : List α) (f : α → Jet) : Jet :=
  l.foldr (fun i acc => Jet.add (f i) acc) Jet.zero

noncomputable section

theorem matches_conjugate {x : Parameters} {a : Jet} {p : Polynomial ℂ}
    (h : Matches x a p) : Matches x (conjugate a) (p.map (starRingEnd ℂ)) := by
  intro r
  rw [coeff_map, ← h r]
  simp only [value, conjugate, Vector.getElem_ofFn, Sparse.value_scale,
    Complex.ofReal_mul,
    map_mul, map_pow, Complex.conj_I, Complex.conj_ofReal]
  push_cast
  rw [← mul_assoc, ← mul_pow]
  simp

theorem matches_sum {α : Type*} {x : Parameters} (l : List α)
    (f : α → Jet) (p : α → Polynomial ℂ) (h : ∀ i, Matches x (f i) (p i)) :
    Matches x (sum l f) ((l.map p).sum) := by
  induction l with
  | nil => exact matches_zero x
  | cons i l ih => exact matches_add (h i) ih

theorem matches_sum_fin {m : ℕ} {x : Parameters} (f : Fin m → Jet)
    (p : Fin m → Polynomial ℂ) (h : ∀ i, Matches x (f i) (p i)) :
    Matches x (sum (List.finRange m) f) (∑ i, p i) := by
  simpa [← List.ofFn_eq_map, List.sum_ofFn] using matches_sum (List.finRange m) f p h

end
end Jet

/-- Storing each matrix entry once prevents repeated expansion of matrix powers. -/
abbrev Table (m : ℕ) := Vector (Vector Jet m) m

namespace Table

def get {m : ℕ} (T : Table m) (i j : Fin m) : Jet := T[i.val][j.val]

def tabulate {m : ℕ} (f : Fin m → Fin m → Jet) : Table m :=
  Vector.ofFn fun i => Vector.ofFn (f i)

@[simp] theorem get_tabulate {m : ℕ} (f : Fin m → Fin m → Jet) (i j : Fin m) :
    (tabulate f).get i j = f i j := by
  simp [get, tabulate]

def one (m : ℕ) : Table m := tabulate fun i j => if i = j then Jet.one else Jet.zero

def add {m : ℕ} (T U : Table m) : Table m :=
  tabulate fun i j => (T.get i j).add (U.get i j)

def mul {m : ℕ} (T U : Table m) : Table m :=
  tabulate fun i j => Jet.sum (List.finRange m) fun k => (T.get i k).mul (U.get k j)

def pow {m : ℕ} (T : Table m) : ℕ → Table m
  | 0 => one m
  | k + 1 => (pow T k).mul T

private def pairIndex : TwoBits ≃ Fin 4 := finProdFinEquiv

def kron (T U : Table 2) : Table 4 :=
  tabulate fun i j =>
    let a := pairIndex.symm i
    let b := pairIndex.symm j
    (T.get a.1 b.1).mul (U.get a.2 b.2)

def trace {m : ℕ} (T : Table m) : Jet := Jet.sum (List.finRange m) fun i => T.get i i

noncomputable section

def Matches {m : ℕ} {ι : Type*} (x : Parameters) (e : ι ≃ Fin m)
    (T : Table m) (U : Matrix ι ι (Polynomial ℂ)) : Prop :=
  ∀ i j, Jet.Matches x (T.get (e i) (e j)) (U i j)

theorem matches_one {m : ℕ} {ι : Type*} [DecidableEq ι] (x : Parameters) (e : ι ≃ Fin m) :
    Matches x e (one m) 1 := by
  intro i j
  by_cases h : i = j
  · subst j
    simpa [one, Matrix.one_apply] using Jet.matches_one x
  · simpa [one, Matrix.one_apply, h, e.injective.ne h] using Jet.matches_zero x

theorem matches_add {m : ℕ} {ι : Type*} {x : Parameters} {e : ι ≃ Fin m}
    {T U : Table m} {P Q : Matrix ι ι (Polynomial ℂ)}
    (hT : Matches x e T P) (hU : Matches x e U Q) : Matches x e (T.add U) (P + Q) := by
  intro i j
  simpa [add] using Jet.matches_add (hT i j) (hU i j)

theorem matches_mul {m : ℕ} {ι : Type*} [Fintype ι] {x : Parameters} {e : ι ≃ Fin m}
    {T U : Table m} {P Q : Matrix ι ι (Polynomial ℂ)}
    (hT : Matches x e T P) (hU : Matches x e U Q) : Matches x e (T.mul U) (P * Q) := by
  intro i j
  rw [mul, get_tabulate, Matrix.mul_apply, ← e.symm.sum_comp (fun k => P i k * Q k j)]
  apply Jet.matches_sum_fin
  intro k
  simpa using Jet.matches_mul (hT i (e.symm k)) (hU (e.symm k) j)

theorem matches_pow {m : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    {x : Parameters} {e : ι ≃ Fin m} {T : Table m} {P : Matrix ι ι (Polynomial ℂ)}
    (h : Matches x e T P) (k : ℕ) : Matches x e (T.pow k) (P ^ k) := by
  induction k with
  | zero => simpa [pow] using matches_one x e
  | succ k ih => simpa [pow, pow_succ] using matches_mul ih h

theorem matches_kron {x : Parameters}
    {T U : Table 2} {P Q : Matrix (Fin 2) (Fin 2) (Polynomial ℂ)}
    (hT : Matches x (Equiv.refl _) T P) (hU : Matches x (Equiv.refl _) U Q) :
    Matches x pairIndex (T.kron U) (P ⊗ₖ Q) := by
  intro i j
  simpa [kron, Matrix.kroneckerMap_apply] using
    Jet.matches_mul (hT i.1 j.1) (hU i.2 j.2)

theorem matches_trace {m : ℕ} {ι : Type*} [Fintype ι] {x : Parameters} {e : ι ≃ Fin m}
    {T : Table m} {P : Matrix ι ι (Polynomial ℂ)} (h : Matches x e T P) :
    Jet.Matches x T.trace P.trace := by
  rw [trace, Matrix.trace, ← e.symm.sum_comp (fun i => P.diag i)]
  apply Jet.matches_sum_fin
  intro i
  simpa using h (e.symm i) (e.symm i)

end
end Table

private def atom (i : Fin 13) (a : ℤ := 1) : Sparse := Sparse.term (primeCode i) a

def symbolicCoordinate (i : Fin 4) : Jet :=
  ![#v[[], atom 0, atom 2 (-1), [], atom 9],
    #v[[(1, 1)], atom 1, atom 3 (-1), atom 6 (-1), atom 10],
    #v[[], [(1, 1)], atom 4 (-1), atom 7 (-1), atom 11],
    #v[[], [], atom 5 (-1), atom 8 (-1), atom 12]] i

noncomputable section

/-- Real coefficients in η, with η = i ε on the complex polynomial path. -/
def pathTerms (x : Parameters) (i : Fin 4) : Fin 5 → ℝ :=
  ![![0, x 0, -x 2, 0, x 9], ![1, x 1, -x 3, -x 6, x 10],
    ![0, 1, -x 4, -x 7, x 11], ![0, 0, -x 5, -x 8, x 12]] i

def pathCoordinate (x : Parameters) (i : Fin 4) : Polynomial ℂ :=
  ∑ r : Fin 5, monomial r.val (Complex.I ^ r.val * (pathTerms x i r : ℂ))

@[simp] theorem coeff_pathCoordinate (x : Parameters) (i : Fin 4) (r : Fin 5) :
    (pathCoordinate x i).coeff r = Complex.I ^ r.val * (pathTerms x i r : ℂ) := by
  rw [pathCoordinate, finsetSum_coeff, Finset.sum_eq_single r]
  · simp
  · intro j _ hj
    simp [coeff_monomial, show j.val ≠ r.val from mt Fin.ext hj]
  · simp

theorem matches_coordinate (x : Parameters) (i : Fin 4) :
    Jet.Matches x (symbolicCoordinate i) (pathCoordinate x i) := by
  intro r
  rw [coeff_pathCoordinate]
  fin_cases i <;> fin_cases r <;> simp [Jet.value, symbolicCoordinate, pathTerms, atom,
    Sparse.value]

def pathChart (x : Parameters) : Fin 2 → Matrix (Fin 2) (Fin 2) (Polynomial ℂ) :=
  hardCoreChart (pathCoordinate x 0) (pathCoordinate x 1)
    (pathCoordinate x 2) (pathCoordinate x 3)

def pathRaw (x : Parameters) (row : Fin 8) (n : ℕ) : Polynomial ℂ :=
  binaryRawTransfer (pathChart x) (entry row).1 (entry row).2 n

end

private local instance : Zero Jet := ⟨Jet.zero⟩
private local instance : One Jet := ⟨Jet.one⟩

def symbolicChart (i : Fin 2) : Table 2 :=
  Table.tabulate fun u v => hardCoreChart (symbolicCoordinate 0) (symbolicCoordinate 1)
    (symbolicCoordinate 2) (symbolicCoordinate 3) i u v

def conjugateChart (i : Fin 2) : Table 2 :=
  Table.tabulate fun u v => (Table.get (symbolicChart i) u v).conjugate

def symbolicTransfer : Table 4 :=
  ((symbolicChart 0).kron (conjugateChart 0)).add
    ((symbolicChart 1).kron (conjugateChart 1))

def symbolicInsertion (row : Fin 8) : Table 4 :=
  let (p, q) := entry row
  ((symbolicChart p.1).mul (symbolicChart p.2)).kron
    ((conjugateChart q.1).mul (conjugateChart q.2))

def symbolicRaw (row : Fin 8) (n : ℕ) : Jet :=
  ((symbolicInsertion row).mul (symbolicTransfer.pow (n - 2))).trace

noncomputable section

private theorem matches_chart (x : Parameters) (i : Fin 2) :
    Table.Matches x (Equiv.refl _) (symbolicChart i) (pathChart x i) := by
  intro u v
  change Jet.Matches x ((symbolicChart i).get u v) (hardCoreChart _ _ _ _ i u v)
  rw [symbolicChart, Table.get_tabulate]
  fin_cases i <;> fin_cases u <;> fin_cases v <;> simp [hardCoreChart] <;>
    first | exact Jet.matches_zero x | exact Jet.matches_one x | apply matches_coordinate

private theorem matches_conjugateChart (x : Parameters) (i : Fin 2) :
    Table.Matches x (Equiv.refl _) (conjugateChart i) (conjugateJet (pathChart x) i) := by
  intro u v
  simpa [conjugateChart, conjugateJet] using Jet.matches_conjugate (matches_chart x i u v)

/-- All five bounded executable coefficients specialize to the actual raw polynomial. -/
theorem symbolicRaw_specializes (x : Parameters) (row : Fin 8) (n : ℕ) :
    Jet.Matches x (symbolicRaw row n) (pathRaw x row n) := by
  let p := (entry row).1
  let q := (entry row).2
  have hA := matches_chart x
  have hB := matches_conjugateChart x
  exact Table.matches_trace (Table.matches_mul
    (Table.matches_kron (Table.matches_mul (hA p.1) (hA p.2))
      (Table.matches_mul (hB q.1) (hB q.2)))
    (Table.matches_pow (Table.matches_add
      (Table.matches_kron (hA 0) (hB 0))
      (Table.matches_kron (hA 1) (hB 1))) (n - 2)))

open PeriodicMPSTwoSiteAmbiguity (rawTwo)

/-- The specialized raw polynomial evaluates to the two-site entry at length s+4. -/
theorem pathRaw_eval (x : Parameters) (row : Fin 8) (s : ℕ) (ε : ℝ) :
    (pathRaw x row (s + 4)).eval (ε : ℂ) =
      rawTwo (fun i => (Polynomial.evalRingHom (ε : ℂ)).mapMatrix (pathChart x i))
        s (entry row).1 (entry row).2 :=
  eval_binaryRawTransfer _ _ _ _ _

end

/-- Denominators clearing both Fibonacci weights at each degree. -/
def denominator : ℕ → ℤ
  | 2 => 5
  | 3 => 5
  | 4 => 50
  | _ => 1

/-- Cleared coefficients in order F, G, nF, nG, … . -/
def weights : ℕ → ℕ → List (Sparse × Sparse)
  | 2, 0 => [ -- 00
      ([(1, 7), (2, -16), (4, -42), (5, -12), (7, 4), (9, 2)],
       [(1, -5), (2, 20), (4, 70), (5, 20)]),
      ([(1, -2), (2, 6), (4, 7), (5, 2), (7, -4), (9, -2)],
       [(1, 1), (2, -8), (4, -11), (5, -6), (7, 2), (9, 1)]),
      ([],
       [])]
  | 2, 1 => [ -- p
      ([(1, -6), (2, 8), (4, 21), (5, 6), (7, -2), (9, -1)],
       [(1, 10), (2, -10), (4, -35), (5, -10)]),
      ([(1, 1), (2, -8), (4, -11), (5, -6), (7, 2), (9, 1)],
       [(1, -3), (2, 14), (4, 18), (5, 8), (7, -6), (9, -3)]),
      ([],
       [])]
  | 2, 2 => [ -- q
      ([(1, -12), (2, -94), (3, 10), (4, -108), (5, -38), (7, 6), (9, 3), (11, 10), (13, 10)],
       [(1, 20), (2, 150), (3, -20), (4, 175), (5, 60), (7, -10), (9, -5), (11, -20), (13, -20)]),
      ([(1, -3), (2, 14), (4, 18), (5, 8), (7, -6), (9, -3)],
       [(1, 4), (2, -22), (4, -29), (5, -14), (7, 8), (9, 4)]),
      ([],
       [])]
  | 2, 3 => [ -- z
      ([(1, -1), (2, 23), (4, 26), (5, 16), (6, 10), (7, -2), (9, -1), (11, -5), (13, -5)],
       [(1, 5), (2, -40), (4, -40), (5, -25), (6, -15), (7, 5), (9, 5), (11, 5), (13, 5)]),
      ([(1, 1), (2, -8), (4, -11), (5, -6), (7, 2), (9, 1)],
       [(1, -3), (2, 14), (4, 18), (5, 8), (7, -6), (9, -3)]),
      ([],
       [])]
  | 2, 4 => [ -- w
      ([(1, 10), (2, 30), (3, -5), (11, 5), (13, -5)],
       [(1, -15), (2, -50), (3, 15), (11, -15), (13, 5)]),
      ([],
       []),
      ([],
       [])]
  | 2, 5 => [ -- v
      ([(1, 5), (2, 5), (13, -5)],
       [(1, -10), (2, -10), (11, -5), (13, 5)]),
      ([],
       []),
      ([],
       [])]
  | 2, 6 => [ -- j
      ([(1, 5)],
       [(1, -15)]),
      ([],
       []),
      ([],
       [])]
  | 3, 0 => [ -- 00
      ([],
       []),
      ([],
       []),
      ([],
       []),
      ([],
       [])]
  | 3, 1 => [ -- p
      ([],
       []),
      ([],
       []),
      ([],
       []),
      ([],
       [])]
  | 3, 2 => [ -- q
      ([],
       []),
      ([],
       []),
      ([],
       []),
      ([],
       [])]
  | 3, 3 => [ -- z
      ([(1, -8), (2, 57), (3, 1), (4, 264), (5, 33), (6, -28), (7, -6), (8, 207), (9, -3), (10, 72), (12, -26), (13, -5), (14, -24), (15, -16), (18, -17), (19, 5), (21, 2), (22, -5), (23, 5), (26, -20), (27, 1)],
       [(1, 10), (2, -90), (3, -5), (4, -425), (5, -50), (6, 50), (7, 10), (8, -335), (9, 5), (10, -120), (12, 40), (13, 10), (14, 35), (15, 25), (17, 5), (18, 25), (19, -5), (21, -10), (22, 10), (23, -5), (26, 35), (27, -5)]),
      ([(1, 3), (2, -7), (3, -1), (4, -54), (5, -8), (6, 8), (7, 6), (8, -47), (9, 3), (10, -22), (12, 11), (14, 14), (15, 6), (18, 7), (21, -2), (27, -1)],
       [(1, -4), (2, 11), (3, 3), (4, 87), (5, 14), (6, -14), (7, -8), (8, 76), (9, -4), (10, 36), (12, -18), (14, -22), (15, -8), (18, -11), (21, 6), (27, 3)]),
      ([],
       []),
      ([],
       [])]
  | 3, 4 => [ -- w
      ([(2, 120), (4, 125), (5, 70), (6, 30), (7, -15), (9, -10), (11, -20), (13, -10), (19, 5), (22, -30), (23, -5), (26, 15), (33, 5), (39, -5)],
       [(1, 5), (2, -200), (4, -200), (5, -110), (6, -50), (7, 25), (9, 20), (11, 30), (13, 10), (19, -15), (22, 50), (23, 5), (26, -25), (33, -15), (39, 5)]),
      ([(1, 5), (2, -30), (4, -40), (5, -20), (7, 10), (9, 5)],
       [(1, -10), (2, 50), (4, 65), (5, 30), (7, -20), (9, -10)]),
      ([],
       []),
      ([],
       [])]
  | 3, 5 => [ -- v
      ([(1, -11), (2, -22), (3, 5), (4, -9), (5, 1), (7, -2), (9, -1), (13, 10), (22, -5), (23, -5), (26, 10)],
       [(1, 20), (2, 35), (3, -10), (4, 15), (13, -20), (19, -5), (22, 10), (23, 5), (26, -15)]),
      ([(1, 1), (2, -8), (4, -11), (5, -6), (7, 2), (9, 1)],
       [(1, -3), (2, 14), (4, 18), (5, 8), (7, -6), (9, -3)]),
      ([],
       []),
      ([],
       [])]
  | 3, 6 => [ -- j
      ([],
       []),
      ([],
       []),
      ([],
       []),
      ([],
       [])]
  | 4, 0 => [ -- 00
      ([(1, 92), (2, -432), (4, 2184), (5, -224), (7, 68), (8, 10392), (9, 34), (10, 2432), (13, -160), (14, -384), (15, -160), (16, 7972), (18, -272), (19, -140), (20, 3944), (23, 20), (25, 692), (26, -540), (28, -1368), (29, 120), (31, -40), (35, -208), (36, -684), (38, 160), (45, -104), (46, 160), (49, 28), (51, -40), (52, -480), (55, -160), (63, 48), (65, -160), (66, -160), (78, -160), (81, 12), (121, -70), (143, 20), (169, 10)],
       [(1, -100), (2, 600), (4, -3500), (5, 400), (7, -100), (8, -16800), (9, -50), (10, -4000), (13, 200), (14, 600), (15, 200), (16, -12900), (18, 400), (19, 100), (20, -6400), (23, -100), (25, -1100), (26, 900), (28, 2200), (29, -200), (35, 400), (36, 1100), (38, -200), (45, 200), (46, -200), (52, 800), (55, 200), (65, 200), (66, 200), (78, 200), (121, 50), (143, -100), (169, -50)]),
      ([(1, -47), (2, 272), (4, -534), (5, 144), (7, -88), (8, -3452), (9, -44), (10, -1152), (13, 60), (14, 364), (15, 60), (16, -2742), (18, 212), (19, 40), (20, -2004), (23, -20), (25, -382), (26, 140), (28, 868), (29, -20), (31, 40), (35, 248), (36, 434), (38, -60), (45, 124), (46, -60), (49, -48), (51, 40), (52, 80), (55, 60), (63, -68), (65, 60), (66, 60), (78, 60), (81, -17), (121, 20), (143, -20), (169, -10)],
       [(1, 51), (2, -396), (4, 852), (5, -272), (7, 104), (8, 5576), (9, 52), (10, 1896), (13, -80), (14, -552), (15, -80), (16, 4441), (18, -316), (19, -20), (20, 3232), (23, 60), (25, 626), (26, -220), (28, -1404), (29, 60), (31, -20), (35, -424), (36, -702), (38, 80), (45, -212), (46, 80), (49, 34), (51, -20), (52, -140), (55, -80), (63, 44), (65, -80), (66, -80), (78, -80), (81, 11), (121, -10), (143, 60), (169, 30)]),
      ([(1, 5), (2, -40), (4, 50), (5, -20), (7, 20), (8, 260), (9, 10), (10, 120), (14, -80), (16, 170), (18, -40), (20, 160), (25, 40), (28, -100), (35, -40), (36, -50), (45, -20), (49, 20), (63, 20), (81, 5)],
       [(1, -5), (2, 60), (4, -80), (5, 40), (7, -20), (8, -420), (9, -10), (10, -200), (14, 120), (16, -275), (18, 60), (20, -260), (25, -60), (28, 160), (35, 80), (36, 80), (45, 40), (49, -20), (63, -20), (81, -5)]),
      ([],
       []),
      ([],
       [])]
  | 4, 1 => [ -- p
      ([(1, -96), (2, 516), (4, -692), (5, 312), (7, -84), (8, -5196), (9, -42), (10, -1216), (13, 180), (14, 192), (15, 80), (16, -3986), (18, 136), (19, 120), (20, -1972), (23, -60), (25, -346), (26, 420), (28, 684), (29, -60), (31, 20), (35, 104), (36, 342), (38, -80), (45, 52), (46, -80), (49, -14), (51, 20), (52, 240), (55, 80), (63, -24), (65, 80), (66, 80), (78, 80), (81, -6), (121, 60), (143, -60), (169, -30)],
       [(1, 150), (2, -800), (4, 1100), (5, -500), (7, 100), (8, 8400), (9, 50), (10, 2000), (13, -300), (14, -300), (15, -100), (16, 6450), (18, -200), (19, -200), (20, 3200), (23, 100), (25, 550), (26, -700), (28, -1100), (29, 100), (35, -200), (36, -550), (38, 100), (45, -100), (46, 100), (52, -400), (55, -100), (65, -100), (66, -100), (78, -100), (121, -100), (143, 100), (169, 50)]),
      ([(1, 51), (2, -276), (4, 672), (5, -152), (7, 104), (8, 3016), (9, 52), (10, 1016), (13, -80), (14, -312), (15, -80), (16, 2061), (18, -196), (19, -20), (20, 1432), (23, 60), (25, 306), (26, -220), (28, -644), (29, 60), (31, -20), (35, -184), (36, -322), (38, 80), (45, -92), (46, 80), (49, 34), (51, -20), (52, -140), (55, -80), (63, 44), (65, -80), (66, -80), (78, -80), (81, 11), (121, -10), (143, 60), (169, 30)],
       [(1, -88), (2, 448), (4, -1076), (5, 236), (7, -152), (8, -4888), (9, -76), (10, -1648), (13, 140), (14, 476), (15, 140), (16, -3333), (18, 308), (19, 60), (20, -2316), (23, -80), (25, -488), (26, 360), (28, 1052), (29, -80), (31, 60), (35, 312), (36, 526), (38, -140), (45, 156), (46, -140), (49, -42), (51, 60), (52, 220), (55, 140), (63, -72), (65, 140), (66, 140), (78, 140), (81, -18), (121, 30), (143, -80), (169, -40)]),
      ([(1, -5), (2, 60), (4, -80), (5, 40), (7, -20), (8, -420), (9, -10), (10, -200), (14, 120), (16, -275), (18, 60), (20, -260), (25, -60), (28, 160), (35, 80), (36, 80), (45, 40), (49, -20), (63, -20), (81, -5)],
       [(1, 10), (2, -100), (4, 130), (5, -60), (7, 40), (8, 680), (9, 20), (10, 320), (14, -200), (16, 445), (18, -100), (20, 420), (25, 100), (28, -260), (35, -120), (36, -130), (45, -60), (49, 40), (63, 40), (81, 10)]),
      ([],
       []),
      ([],
       [])]
  | 4, 2 => [ -- q
      ([(1, -32), (2, 4192), (3, -20), (4, 27086), (5, 2144), (6, -2440), (7, -368), (8, 47468), (9, -184), (10, 15288), (11, -20), (12, -2480), (13, -1060), (14, -3276), (15, -1820), (16, 25028), (17, -100), (18, -2108), (19, 240), (20, 15276), (21, 360), (22, -2440), (23, 680), (25, 2928), (26, -5000), (27, 180), (28, -4512), (29, 380), (31, -60), (35, -1112), (36, -2256), (37, -100), (38, 940), (41, -100), (44, -2480), (45, -556), (46, 740), (49, 82), (51, -60), (52, -4200), (55, -1820), (57, -100), (63, 112), (65, -1620), (66, -940), (69, -100), (77, 260), (78, -740), (81, 28), (91, 260), (99, 180), (117, 180), (121, 120), (143, 680), (169, 240)],
       [(1, 50), (2, -6800), (4, -43800), (5, -3400), (6, 4000), (7, 600), (8, -76800), (9, 300), (10, -24800), (12, 4000), (13, 1700), (14, 5300), (15, 2900), (16, -40500), (17, 200), (18, 3400), (19, -400), (20, -24700), (21, -600), (22, 4000), (23, -1100), (25, -4750), (26, 8100), (27, -300), (28, 7300), (29, -600), (31, 100), (35, 1800), (36, 3650), (37, 200), (38, -1500), (41, 200), (44, 4000), (45, 900), (46, -1200), (49, -150), (51, 100), (52, 6800), (55, 2900), (57, 200), (63, -200), (65, 2600), (66, 1500), (69, 200), (77, -400), (78, 1200), (81, -50), (91, -400), (99, -300), (117, -300), (121, -200), (143, -1100), (169, -400)]),
      ([(1, 72), (2, 208), (3, -80), (4, -4766), (5, -84), (6, 440), (7, 128), (8, -11748), (9, 64), (10, -4608), (11, -80), (12, 580), (13, 60), (14, 1876), (15, 420), (16, -6973), (18, 1008), (19, 60), (20, -5396), (21, -160), (22, 440), (23, -80), (25, -1128), (26, 800), (27, -80), (28, 2372), (29, -80), (31, 60), (35, 832), (36, 1186), (38, -140), (44, 580), (45, 416), (46, -140), (49, -122), (51, 60), (52, 800), (55, 420), (63, -152), (65, 420), (66, 140), (77, -160), (78, 140), (81, -38), (91, -160), (99, -80), (117, -80), (121, 30), (143, -80), (169, -40)],
       [(1, -121), (2, -324), (3, 140), (4, 7708), (5, 132), (6, -720), (7, -204), (8, 19004), (9, -102), (10, 7464), (11, 140), (12, -940), (13, -80), (14, -3028), (15, -660), (16, 11284), (18, -1624), (19, -80), (20, 8728), (21, 280), (22, -720), (23, 140), (25, 1834), (26, -1300), (27, 140), (28, -3836), (29, 140), (31, -80), (35, -1336), (36, -1918), (38, 220), (44, -940), (45, -668), (46, 220), (49, 196), (51, -80), (52, -1300), (55, -660), (63, 236), (65, -660), (66, -220), (77, 280), (78, -220), (81, 59), (91, 280), (99, 140), (117, 140), (121, -40), (143, 140), (169, 70)]),
      ([(1, 10), (2, -100), (4, 130), (5, -60), (7, 40), (8, 680), (9, 20), (10, 320), (14, -200), (16, 445), (18, -100), (20, 420), (25, 100), (28, -260), (35, -120), (36, -130), (45, -60), (49, 40), (63, 40), (81, 10)],
       [(1, -15), (2, 160), (4, -210), (5, 100), (7, -60), (8, -1100), (9, -30), (10, -520), (14, 320), (16, -720), (18, 160), (20, -680), (25, -160), (28, 420), (35, 200), (36, 210), (45, 100), (49, -60), (63, -60), (81, -15)]),
      ([],
       []),
      ([],
       [])]
  | 4, 3 => [ -- z
      ([(1, -16), (2, -154), (4, -5152), (5, -98), (6, 70), (7, -34), (8, -10056), (9, -22), (10, -4396), (11, -80), (12, -1860), (13, 250), (14, 812), (15, 280), (16, -5016), (18, 686), (19, 20), (20, -4422), (22, 640), (23, -210), (24, -2070), (25, -1116), (26, 1210), (28, 1104), (29, -160), (30, -720), (31, 20), (34, -100), (35, 404), (36, 682), (37, 50), (38, -230), (39, 50), (41, 50), (42, 340), (44, 780), (45, 282), (46, -80), (49, -34), (51, 20), (52, 820), (54, 170), (55, 610), (63, -54), (65, 460), (66, 280), (77, -60), (78, 280), (81, -16), (91, -60), (99, -30), (117, -30), (121, 10), (143, -210), (169, -80)],
       [(1, 50), (2, 200), (4, 8350), (5, 200), (6, -100), (7, 50), (8, 16300), (9, 50), (10, 7100), (11, 100), (12, 3000), (13, -450), (14, -1300), (15, -500), (16, 8100), (18, -1150), (19, -100), (20, 7150), (22, -1000), (23, 300), (24, 3350), (25, 1800), (26, -1950), (28, -1800), (29, 250), (30, 1200), (31, -50), (34, 150), (35, -650), (36, -1100), (37, -50), (38, 400), (39, -100), (41, -50), (42, -500), (44, -1250), (45, -450), (46, 150), (49, 50), (51, -100), (52, -1300), (54, -250), (55, -1000), (63, 150), (65, -750), (66, -500), (77, 100), (78, -500), (81, 50), (91, 100), (99, 50), (117, 50), (121, -50), (143, 300), (169, 100)]),
      ([(1, 21), (2, -256), (4, 1482), (5, -142), (6, -70), (7, 54), (8, 4026), (9, 32), (10, 1796), (11, 30), (12, 360), (13, -50), (14, -632), (15, -80), (16, 2241), (18, -396), (19, -20), (20, 1982), (22, -140), (23, 60), (24, 470), (25, 526), (26, -360), (28, -814), (29, 60), (30, 220), (31, -20), (35, -384), (36, -462), (38, 80), (42, -140), (44, -180), (45, -222), (46, 80), (49, 54), (51, -20), (52, -320), (54, -70), (55, -160), (63, 74), (65, -160), (66, -80), (77, 60), (78, -80), (81, 21), (91, 60), (99, 30), (117, 30), (121, -10), (143, 60), (169, 30)],
       [(1, -48), (2, 438), (4, -2406), (5, 206), (6, 110), (7, -102), (8, -6518), (9, -66), (10, -2888), (11, -40), (12, -580), (13, 100), (14, 1036), (15, 140), (16, -3623), (18, 658), (19, 60), (20, -3216), (22, 220), (23, -80), (24, -760), (25, -848), (26, 580), (28, 1312), (29, -80), (30, -360), (31, 60), (35, 612), (36, 746), (38, -140), (42, 220), (44, 290), (45, 346), (46, -140), (49, -102), (51, 60), (52, 510), (54, 110), (55, 280), (63, -162), (65, 280), (66, 140), (77, -80), (78, 140), (81, -48), (91, -80), (99, -40), (117, -40), (121, 30), (143, -80), (169, -40)]),
      ([(1, -5), (2, 60), (4, -80), (5, 40), (7, -20), (8, -420), (9, -10), (10, -200), (14, 120), (16, -275), (18, 60), (20, -260), (25, -60), (28, 160), (35, 80), (36, 80), (45, 40), (49, -20), (63, -20), (81, -5)],
       [(1, 10), (2, -100), (4, 130), (5, -60), (7, 40), (8, 680), (9, 20), (10, 320), (14, -200), (16, 445), (18, -100), (20, 420), (25, 100), (28, -260), (35, -120), (36, -130), (45, -60), (49, 40), (63, 40), (81, 10)]),
      ([],
       []),
      ([],
       [])]
  | 4, 4 => [ -- w
      ([(1, 70), (2, -2240), (4, -9330), (5, -1120), (6, 1200), (7, 240), (8, -7420), (9, 120), (10, -2820), (12, 1250), (13, 320), (14, 940), (15, 700), (17, 50), (18, 620), (19, -200), (21, -200), (22, -1200), (23, -100), (26, 1140), (27, -100), (37, -50), (38, -300), (41, 50), (44, -1250), (46, 150), (52, 580), (55, -700), (57, 50), (65, 330), (66, -300), (69, -50), (77, 150), (78, 150), (91, -110), (99, 100), (117, -80), (121, 100), (143, 100), (169, -100)],
       [(1, -100), (2, 3600), (3, 50), (4, 15100), (5, 1800), (6, -2000), (7, -400), (8, 12000), (9, -200), (10, 4600), (11, -50), (12, -2000), (13, -550), (14, -1500), (15, -1100), (17, -150), (18, -1000), (19, 300), (21, 400), (22, 2000), (23, 100), (26, -1800), (27, 200), (37, 150), (38, 500), (41, -50), (44, 2000), (46, -250), (52, -950), (55, 1100), (57, -150), (65, -550), (66, 500), (69, 50), (77, -250), (78, -250), (91, 150), (99, -200), (117, 100), (121, -150), (143, -100), (169, 200)]),
      ([(1, -70), (2, 140), (3, 50), (4, 1630), (5, 220), (6, -300), (7, -140), (8, 1520), (9, -70), (10, 720), (11, -50), (12, -400), (13, 30), (14, -440), (15, -200), (18, -220), (21, 100), (22, 300), (26, -140), (27, 50), (44, 400), (52, -180), (55, 200), (65, -80), (77, -100), (91, 60), (99, -50), (117, 30)],
       [(1, 110), (2, -220), (3, -100), (4, -2640), (5, -360), (6, 500), (7, 220), (8, -2460), (9, 110), (10, -1160), (11, 100), (12, 650), (13, -40), (14, 720), (15, 300), (18, 360), (21, -200), (22, -500), (26, 220), (27, -100), (44, -650), (52, 290), (55, -300), (65, 140), (77, 200), (91, -80), (99, 100), (117, -40)]),
      ([],
       []),
      ([],
       []),
      ([],
       [])]
  | 4, 5 => [ -- v
      ([(1, -10), (2, -1230), (4, -2460), (5, -640), (6, -200), (7, 130), (8, -1240), (9, 90), (10, -440), (11, 110), (13, 170), (14, 180), (18, 90), (19, -100), (22, 20), (26, 490), (38, -50), (41, 50), (44, 90), (46, 100), (52, 680), (55, -10), (65, 280), (77, 20), (91, -60), (99, 10), (117, -30), (121, -50), (143, -100), (169, -50)],
       [(2, 2000), (4, 4000), (5, 1050), (6, 350), (7, -200), (8, 2000), (9, -150), (10, 700), (11, -200), (13, -250), (14, -300), (18, -150), (19, 200), (26, -750), (37, 50), (38, 100), (41, -50), (44, -150), (46, -150), (52, -1100), (65, -450), (91, 100), (117, 50), (121, 100), (143, 200), (169, 100)]),
      ([(1, -40), (2, 180), (4, 510), (5, 140), (7, -80), (8, 290), (9, -40), (10, 140), (11, -10), (13, 30), (14, -80), (18, -40), (22, 80), (26, -140), (44, 110), (52, -180), (55, 60), (65, -80), (77, -20), (91, 60), (99, -10), (117, 30)],
       [(1, 70), (2, -290), (4, -830), (5, -220), (7, 140), (8, -470), (9, 70), (10, -220), (11, 30), (13, -40), (14, 140), (18, 70), (22, -140), (26, 220), (44, -180), (52, 290), (55, -80), (65, 140), (77, 60), (91, -80), (99, 30), (117, -40)]),
      ([],
       []),
      ([],
       []),
      ([],
       [])]
  | 4, 6 => [ -- j
      ([(1, 100), (2, -600), (4, -800), (5, -400), (7, 100), (9, 50), (13, -200), (19, -100), (23, 100), (26, -300), (121, -50), (143, 100), (169, 50)],
       [(1, -200), (2, 1000), (4, 1300), (5, 600), (7, -100), (9, -50), (13, 400), (19, 300), (23, -100), (26, 500), (121, 150), (143, -100), (169, -50)]),
      ([(1, -50), (2, 300), (4, 400), (5, 200), (7, -100), (9, -50)],
       [(1, 100), (2, -500), (4, -650), (5, -300), (7, 200), (9, 100)]),
      ([],
       []),
      ([],
       []),
      ([],
       [])]
  | _, _ => []

private def buildCandidate (f g n : ℤ) : List (Sparse × Sparse) → Sparse
  | [] => []
  | (a, b) :: rest =>
    (Sparse.add (Sparse.scale f a) (Sparse.scale g b)).add
      (Sparse.scale n (buildCandidate f g n rest))

def integerCandidate (r row n : ℕ) : Sparse :=
  buildCandidate (Nat.fib n) (Nat.fib (n - 1)) n (weights r row)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
/-- Literal powers shared across all comparisons. The interpreter supplies only
candidate data, and the next lemmas verify each multiplication in the kernel. -/
private noncomputable def storedPowers : Array (Array (Array (Array Sparse))) :=
  eval% Array.ofFn (fun k : Fin 15 =>
    (symbolicTransfer.pow k.val).toArray.map fun row =>
      row.toArray.map Vector.toArray)

private noncomputable def samplePower (k : ℕ) : Table 4 :=
  Table.tabulate fun i j => Vector.ofFn fun r =>
    let rows := storedPowers[k]?.getD #[]
    let columns := rows[i.val]?.getD #[]
    let coeffs := columns[j.val]?.getD #[]
    coeffs[r.val]?.getD []

private theorem samplePower_zero : samplePower 0 = Table.one 4 := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
private theorem samplePower_succ (k : Fin 14) :
    samplePower (k.val + 1) = (samplePower k.val).mul symbolicTransfer := by
  fin_cases k <;> decide +kernel

private theorem samplePower_correct (k : ℕ) (hk : k < 15) :
    samplePower k = symbolicTransfer.pow k := by
  induction k with
  | zero => exact samplePower_zero
  | succ k ih =>
    rw [samplePower_succ ⟨k, by omega⟩, Table.pow, ih (by omega)]

private noncomputable def sampleRaw (row : Fin 8) (n : ℕ) : Jet :=
  ((symbolicInsertion row).mul (samplePower (n - 2))).trace

private theorem sampleRaw_correct (row : Fin 8) (n : ℕ) (hn : n ≤ 16) :
    sampleRaw row n = symbolicRaw row n := by
  unfold sampleRaw symbolicRaw
  rw [samplePower_correct _ (by omega)]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 12000000 in
private theorem quadraticSamples (row : Fin 7) (k : Fin 6) :
    Sparse.scale (denominator 2) (sampleRaw row.castSucc (7 + k.val))[2] =
      integerCandidate 2 row.val (7 + k.val) := by
  fin_cases k <;> fin_cases row <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 12000000 in
private theorem cubicSamples (row : Fin 7) (k : Fin 8) :
    Sparse.scale (denominator 3) (sampleRaw row.castSucc (7 + k.val))[3] =
      integerCandidate 3 row.val (7 + k.val) := by
  fin_cases k <;> fin_cases row <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 12000000 in
private theorem quarticSamples (row : Fin 7) (k : Fin 10) :
    Sparse.scale (denominator 4) (sampleRaw row.castSucc (7 + k.val))[4] =
      integerCandidate 4 row.val (7 + k.val) := by
  fin_cases k <;> fin_cases row <;> decide +kernel

noncomputable section

private def weightFrom (specialize : Sparse → ℂ) (second : Bool) :
    List (Sparse × Sparse) → Polynomial ℂ
  | [] => 0
  | (p, q) :: rest =>
    C (specialize (if second then q else p)) + X * weightFrom specialize second rest

private theorem weightFrom_natDegree (specialize : Sparse → ℂ) (second : Bool)
    (ws : List (Sparse × Sparse)) :
    (weightFrom specialize second ws).natDegree ≤ ws.length - 1 := by
  induction ws with
  | nil => simp [weightFrom]
  | cons head tail ih =>
    rcases head with ⟨p, q⟩
    cases tail with
    | nil => simp [weightFrom]
    | cons h rest =>
      apply (natDegree_add_le _ _).trans
      refine max_le (by simp) (natDegree_mul_le.trans ?_)
      rw [natDegree_X]
      simp only [List.length_cons] at *
      omega

/-- Length polynomial multiplying F or G in the certified raw coefficient. -/
def pathWeight (x : Parameters) (r row : ℕ) (second : Bool) : Polynomial ℂ :=
  weightFrom (fun p => (Complex.I ^ r / (denominator r : ℂ)) * (Sparse.value x p : ℂ))
    second (weights r row)

private theorem specialize_build (x : Parameters) (c : ℂ) (f g n : ℤ)
    (ws : List (Sparse × Sparse)) :
    c * (Sparse.value x (buildCandidate f g n ws) : ℂ) =
      (weightFrom (fun p => c * (Sparse.value x p : ℂ)) false ws).eval (n : ℂ) * (f : ℂ) +
      (weightFrom (fun p => c * (Sparse.value x p : ℂ)) true ws).eval (n : ℂ) * (g : ℂ) := by
  induction ws with
  | nil => simp [buildCandidate, weightFrom]
  | cons head tail ih =>
    rcases head with ⟨p, q⟩
    simp only [buildCandidate, Sparse.value_add, Sparse.value_scale, Complex.ofReal_add,
      Complex.ofReal_mul, Complex.ofReal_intCast, weightFrom, Bool.false_eq_true, ite_false,
      ite_true, eval_add, eval_mul, eval_C, eval_X]
    calc
      _ =
          c * (Sparse.value x p : ℂ) * (f : ℂ) +
          c * (Sparse.value x q : ℂ) * (g : ℂ) +
          (n : ℂ) * (c * (Sparse.value x (buildCandidate f g n tail) : ℂ)) := by ring
      _ = _ := by rw [ih]; ring

private theorem specialize_candidate (x : Parameters) (r row n : ℕ) :
    (Complex.I ^ r / (denominator r : ℂ)) * (Sparse.value x (integerCandidate r row n) : ℂ) =
      fibonacciCandidate (pathWeight x r row false) (pathWeight x r row true) n := by
  simpa [integerCandidate, fibonacciCandidate, pathWeight] using
    specialize_build x (Complex.I ^ r / (denominator r : ℂ))
      (Nat.fib n) (Nat.fib (n - 1)) n (weights r row)

private theorem path_eval_zero (x : Parameters) (i : Fin 4) :
    (pathCoordinate x i).eval 0 = if i = 1 then 1 else 0 := by
  rw [← coeff_zero_eq_eval_zero, show (0 : ℕ) = (0 : Fin 5).val by rfl, coeff_pathCoordinate]
  fin_cases i <;> simp [pathTerms]

private theorem raw_eq_from_samples (x : Parameters) (r : Fin 5) (row : Fin 8)
    (hd : (denominator r.val : ℂ) ≠ 0) (hlen : (weights r.val row.val).length ≤ r.val + 1)
    (hs : ∀ k : Fin (2 * (r.val + 1)),
      Sparse.scale (denominator r.val) (symbolicRaw row (7 + k.val))[r.val] =
        integerCandidate r.val row.val (7 + k.val))
    (n : ℕ) (hn : 7 ≤ n) :
    (pathRaw x row n).coeff r.val =
      fibonacciCandidate (pathWeight x r.val row.val false) (pathWeight x r.val row.val true) n := by
  have hdegree (b : Bool) : (pathWeight x r.val row.val b).degree ≤ (r.val : WithBot ℕ) := by
    apply degree_le_of_natDegree_le
    exact (weightFrom_natDegree _ _ _).trans (by omega)
  have ha : (pathCoordinate x 0).eval 0 = 0 := by simpa using path_eval_zero x 0
  have hb : (pathCoordinate x 1).eval 0 = 1 := by simpa using path_eval_zero x 1
  have hc : (pathCoordinate x 2).eval 0 = 0 := by simpa using path_eval_zero x 2
  have hd' : (pathCoordinate x 3).eval 0 = 0 := by simpa using path_eval_zero x 3
  apply (hardCoreRaw_fibonacci_iff_initial _ _ _ _ ha hb hc hd' (entry row).1 (entry row).2
    r.val (by omega) _ _ (hdegree false) (hdegree true)).mpr _ n hn
  intro k hk
  change (pathRaw x row (7 + k)).coeff r.val = _
  rw [← symbolicRaw_specializes x row (7 + k) r, ← specialize_candidate]
  have h := congrArg (Sparse.value x) (hs ⟨k, hk⟩)
  rw [← h, Sparse.value_scale]
  unfold Jet.value
  push_cast
  field_simp [hd]

private theorem sample_comparison (r : Fin 5) (hr : 2 ≤ r.val) (row : Fin 7)
    (k : Fin (2 * (r.val + 1))) :
    Sparse.scale (denominator r.val) (symbolicRaw row.castSucc (7 + k.val))[r.val] =
      integerCandidate r.val row.val (7 + k.val) := by
  rw [← sampleRaw_correct _ _ (by omega)]
  fin_cases r
  · norm_num at hr
  · norm_num at hr
  · exact quadraticSamples row k
  · exact cubicSamples row k
  · exact quarticSamples row k

/-- Degrees two through four for the seven Python-certificate rows at every length n ≥ 7. -/
theorem pathRaw_coeff_eq (x : Parameters) (r : Fin 5) (hr : 2 ≤ r.val) (row : Fin 7)
    (n : ℕ) (hn : 7 ≤ n) :
    (pathRaw x row.castSucc n).coeff r.val =
      fibonacciCandidate (pathWeight x r.val row.val false) (pathWeight x r.val row.val true) n := by
  apply raw_eq_from_samples x r row.castSucc _ _ (sample_comparison r hr row) n hn
  · fin_cases r <;> norm_num [denominator]
  · fin_cases r <;> fin_cases row <;> decide

/-- The quartic forbidden-corner coefficient at every chain length n ≥ 7. -/
theorem forbiddenCorner_coeff_four (x : Parameters) (n : ℕ) (hn : 7 ≤ n) :
    (pathRaw x 6 n).coeff 4 =
      fibonacciCandidate (pathWeight x 4 6 false) (pathWeight x 4 6 true) n :=
  pathRaw_coeff_eq x 4 (by decide) 6 n hn

end

#print axioms symbolicRaw_specializes
#print axioms pathRaw_eval
#print axioms pathRaw_coeff_eq
#print axioms forbiddenCorner_coeff_four

end D5.S3.Quantum.TensorNetworks.PeriodicMPSUniformHardCoreHigherJet
