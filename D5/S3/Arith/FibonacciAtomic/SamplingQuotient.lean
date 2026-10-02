/- GID: D5/S3/Arith/FibonacciAtomic/SamplingQuotient
   generality: I
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/SamplingQuotient
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Sampling preserves coarse fibers; a nonzero kernel blocks one-step updates. -/

import D5.S1.Recurrence.FiniteSamplingSmithDefect
import D5.S3.Arith.FibonacciAtomic.TimeSampling

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Matrix
open D5.S3.Arith.FibonacciAtomic.TimeSampling
open D5.S1.Recurrence.FiniteSamplingSmithDefect

namespace D5.S3.Arith.FibonacciAtomic.SamplingQuotient

/-- Fibonacci readout is the second coordinate of the iterated step. -/
theorem readout_iterate (N k : ℕ) (x : ZMod N × ZMod N) :
    readout N k x = ((fun z : ZMod N × ZMod N => (z.2, z.1 + z.2))^[k] x).2 := by
  let T : ℕ × ℕ → ℕ × ℕ := fun z => (z.2, z.1 + z.2)
  let C : ℕ × ℕ → ZMod N × ZMod N := fun z =>
    (((z.2 : ZMod N) - z.1) * x.1 + z.1 * x.2,
      z.1 * x.1 + z.2 * x.2)
  have hC : Function.Semiconj C T (fun z : ZMod N × ZMod N => (z.2, z.1 + z.2)) := by
    intro z
    apply Prod.ext <;> dsimp [C, T] <;> push_cast <;> ring
  have hbase : C (0, 1) = x := by ext <;> simp [C]
  have hfst : (T^[k] (0, 1)).1 = Nat.fib k := rfl
  have hsnd : (T^[k] (0, 1)).2 = Nat.fib (k + 1) := by
    change (T^[k] (0, 1)).2 = (T^[k + 1] (0, 1)).1
    rw [Function.iterate_succ_apply']
  have h := congrArg Prod.snd (hC.iterate_right k (0, 1))
  rw [hbase] at h
  change (T^[k] (0, 1)).1 * x.1 + (T^[k] (0, 1)).2 * x.2 = _ at h
  simpa only [hfst, hsnd, readout] using h

/-- The finite sample fibers are exactly the full coarse-clock fibers. A nonzero
sample kernel prevents any autonomous one-step update, as the four-step example
modulo three illustrates. All moduli, including one, are retained. -/
theorem sampling_quotient (n m : ℕ) (hn : 0 < n) (hm : 2 ≤ m)
    (t : Fin m → ℕ) (ht : StrictMono t) :
    let M (N : ℕ) : Matrix (Fin 2) (Fin 2) (ZMod N) := !![0, 1; 1, 1]
    let S (N : ℕ) : ZMod N × ZMod N → ZMod N × ZMod N :=
      fun x => (x.2, x.1 + x.2)
    let i0 : Fin m := ⟨0, by omega⟩
    let s := t i0
    let g := (Finset.univ.erase i0).gcd (fun i => t i - s)
    let O := fun x : ZMod n × ZMod n => fun i => readout n (t i) x
    (∀ x j, readout n (s + (j + 2) * g) x =
      (M n ^ g).trace * readout n (s + (j + 1) * g) x -
        (-1 : ZMod n) ^ g * readout n (s + j * g) x) ∧
    (∀ z, (O z = 0 ↔ readout n s z = 0 ∧ readout n (s + g) z = 0) ∧
      (O z = 0 ↔ ((S n)^[s] z).2 = 0 ∧
        (Nat.fib g : ZMod n) * ((S n)^[s] z).1 = 0)) ∧
    (∀ x y, O x = O y ↔
      ∀ j : ℕ, readout n (s + j * g) x = readout n (s + j * g) y) ∧
    (∀ Φ : (Fin m → ZMod n) → (Fin m → ZMod n),
      (∀ x, O (S n x) = Φ (O x)) → ∀ z, O z = 0 → O (S n z) = 0) ∧
    Function.Injective (fun x => (readout n s x, readout n (s + 1) x)) ∧
    (!![(Nat.fib s : ZMod n), Nat.fib (s + 1);
      Nat.fib (s + 1), Nat.fib (s + 2)] : Matrix (Fin 2) (Fin 2) (ZMod n)).det =
        (-1 : ZMod n) ^ (s + 1) ∧
    ((∃ z, z ≠ 0 ∧ O z = 0) →
      ¬ ∃ Φ : (Fin m → ZMod n) → (Fin m → ZMod n),
        ∀ x, O (S n x) = Φ (O x)) ∧
    (M 3 ^ 4 = (2 : ZMod 3) • (1 : Matrix (Fin 2) (Fin 2) (ZMod 3))) ∧
    (∀ (j : ℕ) (x : ZMod 3 × ZMod 3), readout 3 (4 * j) x = 2 ^ j * x.2) ∧
    (∀ (j : ℕ) (x : ZMod 3 × ZMod 3),
      readout 3 (8 * j) x = x.2 ∧ readout 3 (8 * j + 4) x = 2 * x.2) ∧
    (∀ j : ℕ, readout 3 (4 * j) (0, 0) = readout 3 (4 * j) (1, 0)) ∧
    readout 3 1 (0, 0) = 0 ∧ readout 3 1 (1, 0) = 1 ∧
    (0 : ZMod 3) ≠ 1 ∧
    (let O4 := fun x : ZMod 3 × ZMod 3 => ![readout 3 0 x, readout 3 4 x]
     (∃ Ψ : (Fin 2 → ZMod 3) → (Fin 2 → ZMod 3),
       ∀ x, O4 ((S 3)^[4] x) = Ψ (O4 x)) ∧
     (¬ ∃ Φ : (Fin 2 → ZMod 3) → (Fin 2 → ZMod 3),
       ∀ x, O4 (S 3 x) = Φ (O4 x)) ∧
     ¬ ((∃ Ψ : (Fin 2 → ZMod 3) → (Fin 2 → ZMod 3),
          ∀ x, O4 ((S 3)^[4] x) = Ψ (O4 x)) →
        ∃ Φ : (Fin 2 → ZMod 3) → (Fin 2 → ZMod 3),
          ∀ x, O4 (S 3 x) = Φ (O4 x))) := by
  classical
  intro M S i0 s g O
  let : NeZero n := ⟨hn.ne'⟩
  have hstep (N k : ℕ) (x : ZMod N × ZMod N) :
      readout N (k + 1) x = readout N k (S N x) := by
    simp only [readout, S, Nat.fib_add_two, Nat.cast_add]
    ring
  have hiter (N k : ℕ) (x : ZMod N × ZMod N) :
      readout N k x = ((S N)^[k] x).2 := readout_iterate N k x
  have hshift (N a b : ℕ) (x : ZMod N × ZMod N) :
      readout N (a + b) x = readout N b ((S N)^[a] x) := by
    rw [hiter, hiter, Nat.add_comm a b, Function.iterate_add_apply]
  have hmat (N k : ℕ) (x : ZMod N × ZMod N) :
      M N ^ k *ᵥ ![x.1, x.2] = ![((S N)^[k] x).1, ((S N)^[k] x).2] := by
    let E : ZMod N × ZMod N → Fin 2 → ZMod N := fun z => ![z.1, z.2]
    have hE : Function.Semiconj E (S N) (M N).toLin' := by
      intro z
      ext i
      fin_cases i <;> simp [E, S, M, Matrix.toLin'_apply,
        Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    have h := hE.iterate_right k x
    rw [← Module.End.pow_apply, ← Matrix.toLin'_pow, Matrix.toLin'_apply] at h
    exact h.symm
  have hreadmat (N k : ℕ) (x : ZMod N × ZMod N) :
      readout N k x = (M N ^ k *ᵥ ![x.1, x.2]) 1 := by
    rw [hmat, hiter]
    rfl
  have hrec (x : ZMod n × ZMod n) (j : ℕ) :
      readout n (s + (j + 2) * g) x =
        (M n ^ g).trace * readout n (s + (j + 1) * g) x -
          (-1 : ZMod n) ^ g * readout n (s + j * g) x := by
    have hd : (M n ^ g).det = (-1 : ZMod n) ^ g := by
      rw [Matrix.det_pow]
      simp [M, Matrix.det_fin_two_of]
    have hc : (M n ^ g) ^ 2 = (M n ^ g).trace • M n ^ g -
        (-1 : ZMod n) ^ g • (1 : Matrix (Fin 2) (Fin 2) (ZMod n)) := by
      nontriviality ZMod n
      have h := Matrix.aeval_self_charpoly (M n ^ g)
      rw [Matrix.charpoly_fin_two] at h
      simp only [map_add, map_sub, map_mul, map_pow, Polynomial.aeval_X, Polynomial.aeval_C,
        Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, hd, smul_pow, one_pow] at h
      have h' := sub_eq_iff_eq_add.mp (eq_neg_of_add_eq_zero_left h)
      simpa only [sub_eq_add_neg, add_comm] using h'
    have hp : M n ^ (s + (j + 2) * g) =
        (M n ^ g).trace • M n ^ (s + (j + 1) * g) -
          (-1 : ZMod n) ^ g • M n ^ (s + j * g) := by
      calc
        M n ^ (s + (j + 2) * g) = M n ^ (s + j * g) * (M n ^ g) ^ 2 := by
          rw [← pow_mul, ← pow_add]
          congr 1
          ring
        _ = _ := by
          rw [hc, mul_sub, mul_smul_comm, mul_smul_comm, mul_one, ← pow_add]
          congr 2; congr 1; ring
    simp only [hreadmat, hp, Matrix.sub_mulVec, Matrix.smul_mulVec,
      Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  have hzero (N k : ℕ) : readout N k 0 = 0 := by simp [readout]
  have hsub (k : ℕ) (x y : ZMod n × ZMod n) :
      readout n k (x - y) = readout n k x - readout n k y := by
    simp only [readout, Prod.fst_sub, Prod.snd_sub]
    ring
  have hcoarse (z : ZMod n × ZMod n)
      (hz : readout n s z = 0 ∧ readout n (s + g) z = 0) :
      ∀ j : ℕ, readout n (s + j * g) z = 0 := by
    have hb : ((S n)^[s] z).2 = 0 := by rw [← hiter]; exact hz.1
    have ha : (Nat.fib g : ZMod n) * ((S n)^[s] z).1 = 0 := by
      have h := hz.2
      rw [hshift] at h
      simpa only [readout, hb, mul_zero, add_zero] using h
    intro j
    obtain ⟨q, hq⟩ := Nat.fib_dvd g (j * g) (dvd_mul_left g j)
    rw [hshift, readout, hb, mul_zero, add_zero, hq, Nat.cast_mul]
    calc
      (Nat.fib g : ZMod n) * q * ((S n)^[s] z).1 =
          q * ((Nat.fib g : ZMod n) * ((S n)^[s] z).1) := by ring
      _ = 0 := by rw [ha, mul_zero]
  obtain ⟨hfg, U, V, hUV, hsmith⟩ := finite_sampling_smith_defect m hm t ht
  have hg : 0 < g := Nat.fib_pos.mp hfg
  have hgrid (i : Fin m) : ∃ j : ℕ, t i = s + j * g := by
    have hle : s ≤ t i := ht.monotone (show i0 ≤ i from Nat.zero_le _)
    have hd : g ∣ t i - s := by
      by_cases hi : i = i0
      · subst i; simp [s]
      · exact Finset.gcd_dvd (Finset.mem_erase.mpr ⟨hi, Finset.mem_univ _⟩)
    obtain ⟨j, hj⟩ := hd
    rw [Nat.mul_comm] at hj
    exact ⟨j, by omega⟩
  have hinc (z : ZMod n × ZMod n)
      (hz : readout n s z = 0 ∧ readout n (s + g) z = 0) : O z = 0 := by
    funext i
    obtain ⟨j, hj⟩ := hgrid i
    change readout n (t i) z = 0
    rw [hj]
    exact hcoarse z hz j
  have hcard (k : ℕ) (hk : 2 ≤ k) (v : Fin k → ℕ) (hv : StrictMono v) :
      Nat.card {z : ZMod n × ZMod n // (fun i => readout n (v i) z) = 0} =
        Nat.gcd n (Nat.fib ((Finset.univ.erase (⟨0, by omega⟩ : Fin k)).gcd
          (fun i => v i - v ⟨0, by omega⟩))) := by
    obtain ⟨_, A, B, _, h⟩ := finite_sampling_smith_defect k hk v hv
    let H : Matrix (Fin k) (Fin 2) ℤ := fun i =>
      ![(Nat.fib (v i) : ℤ), (Nat.fib (v i + 1) : ℤ)]
    let C := H.map (Int.castRingHom (ZMod n))
    have heq (z : ZMod n × ZMod n) : C *ᵥ ![z.1, z.2] =
        fun i => readout n (v i) z := by
      funext i
      simp [C, H, Matrix.mulVec, Matrix.map, dotProduct, Fin.sum_univ_two, readout]
    let e : {z : ZMod n × ZMod n // (fun i => readout n (v i) z) = 0} ≃
        C.mulVecLin.ker :=
      { toFun := fun z => ⟨![z.val.1, z.val.2], by
          change C *ᵥ ![z.val.1, z.val.2] = 0
          rw [heq]; exact z.property⟩
        invFun := fun z => ⟨(z.val 0, z.val 1), by
          rw [← heq]
          have hv : ![z.val 0, z.val 1] = z.val := by ext i; fin_cases i <;> rfl
          rw [hv]; exact z.property⟩
        left_inv := by intro z; rfl
        right_inv := by intro z; apply Subtype.ext; ext i; fin_cases i <;> rfl }
    exact (Nat.card_congr e).trans (h n hn).1
  let v : Fin 2 → ℕ := ![s, s + g]
  have hv : StrictMono v := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all [v]
  have hvG : (Finset.univ.erase (0 : Fin 2)).gcd (fun i => v i - v 0) = g := by
    have he : Finset.univ.erase (0 : Fin 2) = {1} := by decide
    simp [he, v]
  let K := {z : ZMod n × ZMod n // O z = 0}
  let P := {z : ZMod n × ZMod n // readout n s z = 0 ∧ readout n (s + g) z = 0}
  have hPc : Nat.card P = Nat.gcd n (Nat.fib g) := by
    have hvker (z : ZMod n × ZMod n) :
        (fun i => readout n (v i) z) = 0 ↔
          readout n s z = 0 ∧ readout n (s + g) z = 0 := by
      constructor
      · intro h; exact ⟨congrFun h 0, congrFun h 1⟩
      · rintro ⟨h0, h1⟩; funext i; fin_cases i <;> assumption
    let e : P ≃ {z : ZMod n × ZMod n // (fun i => readout n (v i) z) = 0} :=
      Equiv.subtypeEquivRight (fun z => (hvker z).symm)
    have hc := hcard 2 (by omega) v hv
    change Nat.card {z : ZMod n × ZMod n // (fun i => readout n (v i) z) = 0} =
      Nat.gcd n (Nat.fib ((Finset.univ.erase (0 : Fin 2)).gcd (fun i => v i - v 0))) at hc
    rw [hvG] at hc
    exact (Nat.card_congr e).trans hc
  let f : P → K := fun z => ⟨z.val, hinc z.val z.property⟩
  have hf : Function.Injective f := by
    intro x y h
    exact Subtype.ext (congrArg (fun z : K => z.val) h)
  have hsurj : Function.Surjective f :=
    ((Nat.bijective_iff_injective_and_card f).mpr
      ⟨hf, hPc.trans (hcard m hm t ht).symm⟩).2
  have hker (z : ZMod n × ZMod n) :
      O z = 0 ↔ readout n s z = 0 ∧ readout n (s + g) z = 0 := by
    constructor
    · intro hz
      obtain ⟨w, hw⟩ := hsurj ⟨z, hz⟩
      have hwz : w.val = z := congrArg Subtype.val hw
      exact hwz ▸ w.property
    · exact hinc z
  have hstable (Φ : (Fin m → ZMod n) → (Fin m → ZMod n))
      (hΦ : ∀ x, O (S n x) = Φ (O x)) (z : ZMod n × ZMod n)
      (hz : O z = 0) : O (S n z) = 0 := by
    have hO0 : O 0 = 0 := by funext i; exact hzero n (t i)
    have hS0 : S n 0 = 0 := by simp [S]
    rw [hΦ, hz, ← hO0, ← hΦ, hS0, hO0]
  have hadj : Function.Injective (fun x => (readout n s x, readout n (s + 1) x)) := by
    have hS : Function.Injective (S n) := by
      intro x y h
      have h1 := congrArg Prod.fst h
      have h2 := congrArg Prod.snd h
      dsimp [S] at h1 h2
      exact Prod.ext (add_right_cancel (h1 ▸ h2)) h1
    intro x y h
    apply hS.iterate s
    have h0 := congrArg Prod.fst h
    have h1 := congrArg Prod.snd h
    dsimp only at h0 h1
    rw [hshift n s 1, hshift n s 1] at h1
    rw [hiter, hiter] at h0
    simp only [readout, Nat.fib_one, Nat.cast_one, one_mul] at h1
    exact Prod.ext (add_right_cancel (h0 ▸ h1)) h0
  have h4 : M 3 ^ 4 = (2 : ZMod 3) • (1 : Matrix (Fin 2) (Fin 2) (ZMod 3)) := by
    decide
  have hfour (j : ℕ) (x : ZMod 3 × ZMod 3) : readout 3 (4 * j) x = 2 ^ j * x.2 := by
    rw [hreadmat, pow_mul, h4, smul_pow, one_pow, Matrix.smul_mulVec, Matrix.one_mulVec]
    rfl
  have hdet :
      (!![(Nat.fib s : ZMod n), Nat.fib (s + 1);
        Nat.fib (s + 1), Nat.fib (s + 2)] : Matrix (Fin 2) (Fin 2) (ZMod n)).det =
          (-1 : ZMod n) ^ (s + 1) := by
    rw [Matrix.det_fin_two_of, ← pow_two]
    have h := congrArg (Int.castRingHom (ZMod n))
      (D5.S1.Scale.fib_cassini_from_golden_norm s)
    simpa using h
  refine ⟨hrec, ?_, ?_, hstable, hadj, hdet, ?_, h4, hfour, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro z
    refine ⟨hker z, ?_⟩
    rw [hker, hiter, hshift]
    simp only [readout]
    constructor
    · rintro ⟨hb, h⟩
      exact ⟨hb, by simpa [hb] using h⟩
    · rintro ⟨hb, ha⟩
      exact ⟨hb, by simp [hb, ha]⟩
  · intro x y
    have he (k : ℕ) : readout n k x = readout n k y ↔ readout n k (x-y) = 0 := by
      rw [hsub, sub_eq_zero]
    constructor
    · intro h j
      apply (he _).mpr
      apply hcoarse (x-y) ((hker _).mp ?_) j
      funext i
      change readout n (t i) (x-y) = 0
      have hi : readout n (t i) x = readout n (t i) y := congrFun h i
      rw [hsub, hi, sub_self]
    · intro h
      funext i
      obtain ⟨j, hj⟩ := hgrid i
      change readout n (t i) x = readout n (t i) y
      rw [hj]
      exact h j
  · rintro ⟨z, hz, hzO⟩ ⟨Φ, hΦ⟩
    apply hz
    apply hadj
    have h0 : readout n s z = 0 := (hker z).mp hzO |>.1
    have h1 : readout n (s + 1) z = 0 := by
      rw [hstep]
      exact (hker _).mp (hstable Φ hΦ z hzO) |>.1
    simp [h0, h1, hzero]
  · intro j x
    have hp : (2 : ZMod 3) ^ (2 * j) = 1 := by
      rw [pow_mul, show (2 : ZMod 3) ^ 2 = 1 by decide, one_pow]
    constructor
    · have he : 8*j = 4*(2*j) := by ring
      rw [he, hfour, hp, one_mul]
    · have he : 8*j+4 = 4*(2*j+1) := by ring
      rw [he, hfour, pow_succ, hp, one_mul]
  · intro j
    rw [hfour, hfour]
  · norm_num [readout]
  · norm_num [readout]
  · decide
  · dsimp only
    let O4 := fun x : ZMod 3 × ZMod 3 => ![readout 3 0 x, readout 3 4 x]
    have hcoarse4 : ∃ Ψ : (Fin 2 → ZMod 3) → (Fin 2 → ZMod 3),
        ∀ x, O4 ((S 3)^[4] x) = Ψ (O4 x) := by
      exact ⟨fun y => (2 : ZMod 3) • y, by decide⟩
    have hfine4 : ¬ ∃ Φ : (Fin 2 → ZMod 3) → (Fin 2 → ZMod 3),
        ∀ x, O4 (S 3 x) = Φ (O4 x) := by
      rintro ⟨Φ, hΦ⟩
      have heq : O4 (0, 0) = O4 (1, 0) := by decide
      have h := (hΦ (0, 0)).trans ((congrArg Φ heq).trans (hΦ (1, 0)).symm)
      have h0 := congrFun h 0
      norm_num [O4, S, readout] at h0
    exact ⟨hcoarse4, hfine4, fun h => hfine4 (h hcoarse4)⟩

#print axioms sampling_quotient

end D5.S3.Arith.FibonacciAtomic.SamplingQuotient
