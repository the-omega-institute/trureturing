/- GID: D5/S0/Computability/Diophantine/IntegerToRational
   generality: G
   mirror-B: none(waiver:unbounded-symbolic-proof)
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: A finite polynomial definition of the integers gives a uniform integer-to-rational solvability compiler. -/

import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Computability.Primrec.List
import Mathlib.Computability.Partrec

/-! The conditional construction of UPPM_RG_002, Theorem 3.1. The defining
polynomial is a premise, not a constructed solution of the integer-definition
problem. Neither integer H10 undecidability nor the arithmetic premises of
ZInQ.FrozenTarget are asserted here. See local preregistration #31217. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S0.Computability.Diophantine.IntegerToRational

open MvPolynomial

/-- The entire integer-definition clause, with all witnesses rational. -/
def DefinesIntegers {m : ℕ} (P : MvPolynomial (Fin (m + 1)) ℤ) : Prop :=
  ∀ q : ℚ, (∃ w : Fin m → ℚ, eval₂ (Int.castRingHom ℚ) (Fin.cons q w) P = 0) ↔
    ∃ z : ℤ, (z : ℚ) = q

/-- Row-major finite indexing: coordinate `(i,j)` has number `j+(m+1)*i`. -/
def coordinate {n m : ℕ} (i : Fin n) (j : Fin (m + 1)) : Fin (n * (m + 1)) :=
  finProdFinEquiv (i, j)

/-- Each original variable is the first coordinate of its own witness block. -/
def original {n m : ℕ} (i : Fin n) : Fin (n * (m + 1)) := coordinate i 0

/-- One polynomial over integers, evaluated at one joint assignment. -/
noncomputable def compile {n m : ℕ} (P : MvPolynomial (Fin (m + 1)) ℤ)
    (f : MvPolynomial (Fin n) ℤ) : MvPolynomial (Fin (n * (m + 1))) ℤ :=
  let rows : Fin (n + 1) → MvPolynomial (Fin (n * (m + 1))) ℤ :=
    Fin.cons (rename original f) (fun i => rename (coordinate i) P)
  ∑ k : Fin (n + 1), (rows k) ^ 2

private theorem compile_zero_iff {n m : ℕ} (P : MvPolynomial (Fin (m + 1)) ℤ)
    (f : MvPolynomial (Fin n) ℤ) (x : Fin (n * (m + 1)) → ℚ) :
    eval₂ (Int.castRingHom ℚ) x (compile P f) = 0 ↔
      eval₂ (Int.castRingHom ℚ) (x ∘ original) f = 0 ∧
      ∀ i : Fin n, eval₂ (Int.castRingHom ℚ) (x ∘ coordinate i) P = 0 := by
  rw [compile, eval₂_sum]
  simp only [eval₂_pow]
  rw [Finset.sum_sq_eq_zero_iff]
  simp only [Finset.mem_univ, forall_true_left]
  constructor
  · intro h
    constructor
    · simpa only [Fin.cons_zero, eval₂_rename] using h 0
    · intro i
      simpa only [Fin.cons_succ, eval₂_rename] using h i.succ
  · rintro ⟨hf, hP⟩ k
    refine Fin.cases ?_ (fun i => ?_) k
    · simpa only [Fin.cons_zero, eval₂_rename] using hf
    · simpa only [Fin.cons_succ, eval₂_rename] using hP i

/-- For every finite input dimension, rational solvability of the compiled
polynomial is exactly integer solvability of the input polynomial. -/
theorem solvability {n m : ℕ} (P : MvPolynomial (Fin (m + 1)) ℤ)
    (hP : DefinesIntegers P) (f : MvPolynomial (Fin n) ℤ) :
    (∃ x : Fin (n * (m + 1)) → ℚ, eval₂ (Int.castRingHom ℚ) x (compile P f) = 0) ↔
      ∃ z : Fin n → ℤ, eval z f = 0 := by
  classical
  constructor
  · rintro ⟨x, hx⟩
    obtain ⟨hf, hw⟩ := (compile_zero_iff P f x).mp hx
    have hz : ∀ i : Fin n, ∃ z : ℤ, (z : ℚ) = x (original i) := by
      intro i
      apply (hP (x (original i))).mp
      refine ⟨fun j => x (coordinate i j.succ), ?_⟩
      convert hw i using 1
      congr 1
      funext j
      exact Fin.cases rfl (fun _ => rfl) j
    choose z hz using hz
    refine ⟨z, Rat.intCast_injective ?_⟩
    have heq : (fun i => (z i : ℚ)) = x ∘ original := by
      funext i
      exact hz i
    have hzc : eval₂ (Int.castRingHom ℚ) (fun i => (z i : ℚ)) f = 0 := by
      rw [heq]
      exact hf
    have hc := MvPolynomial.eval₂_comp (Int.castRingHom ℚ) z f
    change (Int.castRingHom ℚ) (eval z f) = 0
    calc
      (Int.castRingHom ℚ) (eval z f) =
          eval₂ (Int.castRingHom ℚ) (⇑(Int.castRingHom ℚ) ∘ z) f := hc
      _ = eval₂ (Int.castRingHom ℚ) (fun i => (z i : ℚ)) f := by
        rfl
      _ = 0 := hzc
  · rintro ⟨z, hz⟩
    have hw : ∀ i : Fin n, ∃ w : Fin m → ℚ,
        eval₂ (Int.castRingHom ℚ) (Fin.cons (z i : ℚ) w) P = 0 := by
      intro i
      exact (hP (z i)).mpr ⟨z i, rfl⟩
    choose w hw using hw
    let y : Fin n × Fin (m + 1) → ℚ := fun ij =>
      (Fin.cons (z ij.1 : ℚ) (w ij.1) : Fin (m + 1) → ℚ) ij.2
    let x : Fin (n * (m + 1)) → ℚ := y ∘ finProdFinEquiv.symm
    refine ⟨x, (compile_zero_iff P f x).mpr ⟨?_, ?_⟩⟩
    · have hcast := congrArg (Int.castRingHom ℚ) hz
      rw [eval₂_comp] at hcast
      convert hcast using 1
      simp only [Function.comp_def, x, y, original, coordinate,
        Equiv.symm_apply_apply, Fin.cons_zero]
      rfl
    · intro i
      convert hw i using 1
      congr 1
      funext j
      simp only [Function.comp_def, x, y, coordinate, Equiv.symm_apply_apply]

/-- A distributed polynomial code: terms carry a difference-of-naturals
coefficient and a word of variable indices. Repetition encodes exponents. -/
abbrev PolynomialCode := List ((ℕ × ℕ) × List ℕ)

/-- Invalid indices denote zero, including in dimension zero. -/
noncomputable def codeVariable (n k : ℕ) : MvPolynomial (Fin n) ℤ :=
  if h : k < n then X ⟨k, h⟩ else 0

noncomputable def decodePolynomial (n : ℕ) (c : PolynomialCode) : MvPolynomial (Fin n) ℤ :=
  (c.map fun t => C ((t.1.1 : ℤ) - t.1.2) * (t.2.map (codeVariable n)).prod).sum

def multiplyCode (a b : PolynomialCode) : PolynomialCode :=
  a.flatMap fun s => b.map fun t =>
    ((s.1.1 * t.1.1 + s.1.2 * t.1.2,
      s.1.1 * t.1.2 + s.1.2 * t.1.1), s.2 ++ t.2)

def renameCode (n N : ℕ) (r : ℕ → ℕ) (c : PolynomialCode) : PolynomialCode :=
  c.map fun t => (t.1, t.2.map fun k => if k < n then r k else N)

private theorem decode_append (n : ℕ) (a b : PolynomialCode) :
    decodePolynomial n (a ++ b) = decodePolynomial n a + decodePolynomial n b := by
  simp [decodePolynomial]

private theorem decode_multiply (n : ℕ) (a b : PolynomialCode) :
    decodePolynomial n (multiplyCode a b) = decodePolynomial n a * decodePolynomial n b := by
  induction a with
  | nil => simp [multiplyCode, decodePolynomial]
  | cons s a ih =>
    change decodePolynomial n
      ((b.map fun t => ((s.1.1 * t.1.1 + s.1.2 * t.1.2,
        s.1.1 * t.1.2 + s.1.2 * t.1.1), s.2 ++ t.2)) ++ multiplyCode a b) = _
    rw [decode_append, ih]
    simp only [decodePolynomial, List.map_cons, List.sum_cons, add_mul]
    congr 1
    clear ih a
    induction b with
    | nil => simp
    | cons t b ihb =>
      simp only [List.map_cons, List.sum_cons, List.map_map, List.map_append,
        List.prod_append, mul_add] at *
      rw [ihb]
      congr 1
      have hc : (((s.1.1 * t.1.1 + s.1.2 * t.1.2 : ℕ) : ℤ) -
          (s.1.1 * t.1.2 + s.1.2 * t.1.1 : ℕ)) =
          ((s.1.1 : ℤ) - s.1.2) * ((t.1.1 : ℤ) - t.1.2) := by
        push_cast
        ring
      rw [hc, map_mul]
      ring

/-- Completeness holds for all dimensions and every signed coefficient. -/
theorem code_complete {n : ℕ} (f : MvPolynomial (Fin n) ℤ) :
    ∃ c : PolynomialCode, decodePolynomial n c = f := by
  classical
  induction f using MvPolynomial.induction_on with
  | C z =>
    refine ⟨[((z.toNat, (-z).toNat), [])], ?_⟩
    have hz : (z.toNat : ℤ) - (-z).toNat = z := by omega
    simp only [decodePolynomial, List.map_cons, List.map_nil, List.prod_nil,
      List.sum_cons, List.sum_nil, mul_one, add_zero]
    exact congrArg C hz
  | add f g hf hg =>
    obtain ⟨a, ha⟩ := hf
    obtain ⟨b, hb⟩ := hg
    exact ⟨a ++ b, by rw [decode_append, ha, hb]⟩
  | mul_X f i hf =>
    obtain ⟨a, ha⟩ := hf
    refine ⟨multiplyCode a [((1, 0), [i.val])], ?_⟩
    rw [decode_multiply, ha]
    simp [decodePolynomial, codeVariable, i.isLt]

private theorem decode_rename {n N : ℕ} (r : Fin n → Fin N) (r' : ℕ → ℕ)
    (hr : ∀ k : Fin n, r' k.val = (r k).val) (c : PolynomialCode) :
    decodePolynomial N (renameCode n N r' c) = rename r (decodePolynomial n c) := by
  have hv (k : ℕ) : codeVariable N (if k < n then r' k else N) =
      rename r (codeVariable n k) := by
    by_cases hk : k < n
    · have h := hr ⟨k, hk⟩
      simp [codeVariable, hk, h, (r ⟨k, hk⟩).isLt]
    · simp [codeVariable, hk]
  unfold decodePolynomial renameCode
  rw [map_list_sum (rename r)]
  simp only [List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro t _
  dsimp only [Function.comp_apply]
  rw [map_mul, rename_C, map_list_prod (rename r)]
  congr 1
  simp only [List.map_map]
  apply congrArg List.prod
  exact List.map_congr_left fun k _ => hv k

private theorem decode_flatMap {A : Type} (n : ℕ) (l : List A) (g : A → PolynomialCode) :
    decodePolynomial n (l.flatMap g) = (l.map fun i => decodePolynomial n (g i)).sum := by
  induction l with
  | nil => simp [decodePolynomial]
  | cons i l ih => simp only [List.flatMap_cons, decode_append, ih, List.map_cons, List.sum_cons]

def rowCode (n m i : ℕ) (P : PolynomialCode) : PolynomialCode :=
  let b := renameCode (m + 1) (n * (m + 1)) (fun k => k + (m + 1) * i) P
  multiplyCode b b

/-- A total compiler whose two dimensions and both polynomial codes are inputs. -/
def compileCode (n m : ℕ) (P f : PolynomialCode) : PolynomialCode :=
  let N := n * (m + 1)
  let a := renameCode n N (fun k => (m + 1) * k) f
  multiplyCode a a ++ (List.range n).flatMap (rowCode n m · P)

private theorem multiplyCode_primrec : Primrec₂ multiplyCode := by
  have ht : Primrec₂ (fun s t : (ℕ × ℕ) × List ℕ =>
      ((s.1.1 * t.1.1 + s.1.2 * t.1.2,
        s.1.1 * t.1.2 + s.1.2 * t.1.1), s.2 ++ t.2)) := by
    have a : Primrec (fun p : ((ℕ × ℕ) × List ℕ) × ((ℕ × ℕ) × List ℕ) => p.1.1.1) :=
      Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
    have b : Primrec (fun p : ((ℕ × ℕ) × List ℕ) × ((ℕ × ℕ) × List ℕ) => p.1.1.2) :=
      Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
    have c : Primrec (fun p : ((ℕ × ℕ) × List ℕ) × ((ℕ × ℕ) × List ℕ) => p.2.1.1) :=
      Primrec.fst.comp (Primrec.fst.comp Primrec.snd)
    have d : Primrec (fun p : ((ℕ × ℕ) × List ℕ) × ((ℕ × ℕ) × List ℕ) => p.2.1.2) :=
      Primrec.snd.comp (Primrec.fst.comp Primrec.snd)
    exact ((Primrec.nat_add.comp (Primrec.nat_mul.comp a c) (Primrec.nat_mul.comp b d)).pair
      (Primrec.nat_add.comp (Primrec.nat_mul.comp a d) (Primrec.nat_mul.comp b c))).pair
        (Primrec.list_append.comp (Primrec.snd.comp Primrec.fst) (Primrec.snd.comp Primrec.snd))
  unfold multiplyCode
  apply Primrec.list_flatMap Primrec.fst
  apply Primrec.list_map (Primrec.snd.comp Primrec.fst)
  exact (ht.comp (Primrec.snd.comp Primrec.fst) Primrec.snd).to₂

private theorem renameCode_primrec {A : Type} [Primcodable A]
    (n N : A → ℕ) (r : A → ℕ → ℕ) (c : A → PolynomialCode)
    (hn : Primrec n) (hN : Primrec N) (hr : Primrec₂ r) (hc : Primrec c) :
    Primrec (fun a => renameCode (n a) (N a) (r a) (c a)) := by
  unfold renameCode
  apply Primrec.list_map hc
  apply Primrec.pair (Primrec.fst.comp Primrec.snd)
  apply Primrec.list_map (Primrec.snd.comp Primrec.snd)
  exact (Primrec.ite
    (Primrec.nat_lt.comp Primrec.snd (hn.comp (Primrec.fst.comp Primrec.fst)))
    (hr.comp (Primrec.fst.comp Primrec.fst) Primrec.snd)
    (hN.comp (Primrec.fst.comp Primrec.fst))).to₂

/-- A single primitive recursive map takes arbitrary dimensions and codes to
both the output dimension and the compiled polynomial code. The coding is the
pinned Mathlib `Primcodable` product/list coding on naturals. -/
theorem compileCode_primrec :
    Primrec (fun p : ℕ × ℕ × PolynomialCode × PolynomialCode =>
      (p.1 * (p.2.1 + 1), compileCode p.1 p.2.1 p.2.2.1 p.2.2.2)) := by
  let A := ℕ × ℕ × PolynomialCode × PolynomialCode
  have hn : Primrec (fun p : A => p.1) := Primrec.fst
  have hm : Primrec (fun p : A => p.2.1 + 1) := Primrec.succ.comp (Primrec.fst.comp Primrec.snd)
  have hN : Primrec (fun p : A => p.1 * (p.2.1 + 1)) := Primrec.nat_mul.comp hn hm
  have hP : Primrec (fun p : A => p.2.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hf : Primrec (fun p : A => p.2.2.2) := Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have ha : Primrec (fun p : A =>
      renameCode p.1 (p.1 * (p.2.1 + 1)) (fun k => (p.2.1 + 1) * k) p.2.2.2) :=
    renameCode_primrec _ _ _ _ hn hN
      (Primrec.nat_mul.comp (hm.comp Primrec.fst) Primrec.snd) hf
  have hb : Primrec (fun p : A × ℕ =>
      renameCode (p.1.2.1 + 1) (p.1.1 * (p.1.2.1 + 1))
        (fun k => k + (p.1.2.1 + 1) * p.2) p.1.2.2.1) :=
    renameCode_primrec _ _ _ _ (hm.comp Primrec.fst) (hN.comp Primrec.fst)
      (Primrec.nat_add.comp Primrec.snd
        (Primrec.nat_mul.comp (hm.comp (Primrec.fst.comp Primrec.fst))
          (Primrec.snd.comp Primrec.fst))) (hP.comp Primrec.fst)
  exact hN.pair (Primrec.list_append.comp
    (multiplyCode_primrec.comp ha ha)
    (Primrec.list_flatMap (Primrec.list_range.comp hn)
      (multiplyCode_primrec.comp hb hb)))

/- Raw natural codes use Mathlib's canonical `Encodable` numbering of the
finite list code. A malformed numeral decodes to `[]`, hence to zero. -/
def decodeCode (k : ℕ) : PolynomialCode :=
  (Encodable.decode (α := PolynomialCode) k).getD []

def compileCodeNat (n m p f : ℕ) : ℕ × ℕ :=
  let q := compileCode n m (decodeCode p) (decodeCode f)
  (n * (m + 1), Encodable.encode q)

theorem compileCodeNat_primrec :
    Primrec (fun q : ℕ × ℕ × ℕ × ℕ =>
      compileCodeNat q.1 q.2.1 q.2.2.1 q.2.2.2) := by
  have hdP : Primrec (fun q : ℕ × ℕ × ℕ × ℕ => decodeCode q.2.2.1) :=
    Primrec.option_getD.comp
      (Primrec.decode.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.snd)))
      (Primrec.const [])
  have hdf : Primrec (fun q : ℕ × ℕ × ℕ × ℕ => decodeCode q.2.2.2) :=
    Primrec.option_getD.comp
      (Primrec.decode.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
      (Primrec.const [])
  have hq : Primrec (fun q : ℕ × ℕ × ℕ × ℕ =>
      (q.1, q.2.1, decodeCode q.2.2.1, decodeCode q.2.2.2)) :=
    (Primrec.fst.pair ((Primrec.fst.comp Primrec.snd).pair (hdP.pair hdf)))
  have hc := compileCode_primrec.comp hq
  exact (Primrec.fst.pair (Primrec.encode.comp Primrec.snd)).comp hc

private theorem compileCodeNat_computable :
    Computable (fun q : ℕ × ℕ × ℕ × ℕ =>
      compileCodeNat q.1 q.2.1 q.2.2.1 q.2.2.2) :=
  compileCodeNat_primrec.to_comp

private theorem decodeCode_encode (c : PolynomialCode) : decodeCode (Encodable.encode c) = c := by
  simp [decodeCode]

private theorem code_complete_raw {n : ℕ} (f : MvPolynomial (Fin n) ℤ) :
    ∃ k : ℕ, decodePolynomial n (decodeCode k) = f := by
  obtain ⟨c, hc⟩ := code_complete f
  exact ⟨Encodable.encode c, by rw [decodeCode_encode, hc]⟩

/-- The distributed-code transformation decodes to the original semantic compiler. -/
theorem decode_compileCode (n m : ℕ) (P f : PolynomialCode) :
    decodePolynomial (n * (m + 1)) (compileCode n m P f) =
      compile (decodePolynomial (m + 1) P) (decodePolynomial n f) := by
  classical
  have ho : decodePolynomial (n * (m + 1))
      (renameCode n (n * (m + 1)) (fun k => (m + 1) * k) f) =
      rename original (decodePolynomial n f) := by
    apply decode_rename original
    intro k
    simp [original, coordinate, finProdFinEquiv]
  have hr (i : Fin n) : decodePolynomial (n * (m + 1)) (rowCode n m i.val P) =
      (rename (coordinate i) (decodePolynomial (m + 1) P)) ^ 2 := by
    have h := decode_rename (coordinate i) (fun k => k + (m + 1) * i.val)
      (fun _ => rfl) P
    simpa only [rowCode, decode_multiply, pow_two] using congrArg (fun a => a * a) h
  rw [compileCode, decode_append, decode_multiply, ho, decode_flatMap]
  rw [compile, Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ, pow_two]
  congr 1
  rw [Fin.sum_univ_def]
  rw [show List.range n = (List.finRange n).map Fin.val by simp]
  simp only [List.map_map]
  apply congrArg List.sum
  exact List.map_congr_left fun i _ => by
    simpa only [Function.comp_apply, pow_two] using hr i

/-- The effective code compiler consumes the original semantic solvability
theorem; all rational constraints use one joint assignment. -/
theorem code_solvability (n m : ℕ) (P f : PolynomialCode)
    (hP : DefinesIntegers (decodePolynomial (m + 1) P)) :
    (∃ x : Fin (n * (m + 1)) → ℚ,
      eval₂ (Int.castRingHom ℚ) x
        (decodePolynomial (n * (m + 1)) (compileCode n m P f)) = 0) ↔
      ∃ z : Fin n → ℤ, eval z (decodePolynomial n f) = 0 := by
  rw [decode_compileCode]
  exact solvability _ hP _

/-- The complete uniform effective interface: a computable map on raw finite
codes, a code for every finite integer polynomial, and solvability preservation
for every raw input satisfying the entire integer-definition premise. -/
theorem effective_compiler :
    Computable (fun q : ℕ × ℕ × ℕ × ℕ =>
      compileCodeNat q.1 q.2.1 q.2.2.1 q.2.2.2) ∧
    (∀ (n : ℕ) (f : MvPolynomial (Fin n) ℤ),
      ∃ k : ℕ, decodePolynomial n (decodeCode k) = f) ∧
    (∀ (n m p f : ℕ), DefinesIntegers (decodePolynomial (m + 1) (decodeCode p)) →
      ((∃ x : Fin (n * (m + 1)) → ℚ,
        eval₂ (Int.castRingHom ℚ) x (decodePolynomial (n * (m + 1))
          (decodeCode (compileCodeNat n m p f).2)) = 0) ↔
        ∃ z : Fin n → ℤ, eval z (decodePolynomial n (decodeCode f)) = 0)) := by
  refine ⟨compileCodeNat_computable, fun _ f => code_complete_raw f, ?_⟩
  intro n m p f hP
  simpa only [compileCodeNat, decodeCode_encode] using
    code_solvability n m (decodeCode p) (decodeCode f) hP

end D5.S0.Computability.Diophantine.IntegerToRational
