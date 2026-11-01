/- GID: D5/S3/Quantum/Entanglement/SectorChannels/WordScaleTower
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/SectorChannels/WordScaleTower
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Common digit words construct a strictly composable compact physical CPTP tower. -/

import D5.S3.Quantum.Foundation.FiniteKrausChannel
import D5.S3.Quantum.Entanglement.SectorSchmidtEncoding
import D5.S3.Quantum.Entanglement.FiniteSectorChannelModel
import Mathlib.Algebra.BigOperators.Fin

/-! A common digit alphabet on the original compact sector carriers. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators CStarAlgebra ComplexOrder MatrixOrder Matrix
open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Foundation.FiniteKrausChannel
open D5.S3.Quantum.Entanglement.SectorSchmidtEncoding
open D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality

noncomputable section

namespace D5.S3.Quantum.Entanglement.SectorChannels.WordScaleTower

variable {Sector : Type*} [Fintype Sector] [DecidableEq Sector]

abbrev Level (b : Sector → ℕ) (n : ℕ) := TargetLocal (fun s => b s ^ n)

def alphabet (b : Sector → ℕ) : ℕ := Finset.univ.sup b

abbrev Word (b : Sector → ℕ) (n : ℕ) := Fin n → Fin (alphabet b)

/-- The explicit least-significant-first base expansion, on the compact carrier. -/
def digits (b : Sector → ℕ) (n : ℕ) (s : Sector) :
    Fin (b s ^ n) ≃ (Fin n → Fin (b s)) := finFunctionFinEquiv.symm

def commonWord (b : Sector → ℕ) {n : ℕ} (x : Level b n) : Word b n :=
  fun q => ⟨digits b n x.1 x.2 q, lt_of_lt_of_le (digits b n x.1 x.2 q).isLt
    (Finset.le_sup (Finset.mem_univ x.1))⟩

def keep (b : Sector → ℕ) {n j : ℕ} (h : j ≤ n) (x : Level b n) : Level b j :=
  ⟨x.1, (digits b j x.1).symm (fun q => digits b n x.1 x.2 (q.castLE h))⟩

def tail (b : Sector → ℕ) {n j : ℕ} (h : j ≤ n) (x : Level b n) : Word b (n - j) :=
  fun q => commonWord b x ⟨j + q.val, by omega⟩

omit [DecidableEq Sector] in
private theorem commonWord_keep (b : Sector → ℕ) {n j : ℕ} (h : j ≤ n)
    (x : Level b n) (q : Fin j) :
    commonWord b (keep b h x) q = commonWord b x (q.castLE h) := by
  apply Fin.ext
  change ((digits b j x.1) ((digits b j x.1).symm _) q).val = _
  exact congrArg (fun w : Fin j → Fin (b x.1) => (w q).val)
    ((digits b j x.1).apply_symm_apply _)

omit [Fintype Sector] [DecidableEq Sector] in
private theorem keep_comp (b : Sector → ℕ) {n j h : ℕ}
    (hjn : j ≤ n) (hhj : h ≤ j) (x : Level b n) :
    keep b hhj (keep b hjn x) = keep b (hhj.trans hjn) x := by
  rcases x with ⟨s, i⟩
  apply congrArg (Sigma.mk s)
  change (digits b h s).symm (fun q =>
      digits b j s ((digits b j s).symm (fun r => digits b n s i (r.castLE hjn)))
        (q.castLE hhj)) =
    (digits b h s).symm (fun q => digits b n s i (q.castLE (hhj.trans hjn)))
  apply congrArg (digits b h s).symm
  funext q
  rw [(digits b j s).apply_symm_apply]
  apply congrArg ((digits b n s) i)
  exact Fin.ext rfl

omit [DecidableEq Sector] in
private theorem tail_eq_iff (b : Sector → ℕ) {n j : ℕ} (h : j ≤ n)
    (x y : Level b n) :
    tail b h x = tail b h y ↔
      ∀ q : Fin n, j ≤ q.val → commonWord b x q = commonWord b y q := by
  constructor
  · intro he q hq
    have hh := congrFun he (⟨q.val - j, by omega⟩ : Fin (n - j))
    simpa only [tail, Nat.add_sub_of_le hq] using hh
  · intro he
    funext q
    exact he ⟨j + q.val, by omega⟩ (Nat.le_add_right _ _)

omit [DecidableEq Sector] in
private theorem tail_comp_iff (b : Sector → ℕ) {n j h : ℕ}
    (hjn : j ≤ n) (hhj : h ≤ j) (x y : Level b n) :
    tail b (hhj.trans hjn) x = tail b (hhj.trans hjn) y ↔
      tail b hjn x = tail b hjn y ∧
      tail b hhj (keep b hjn x) = tail b hhj (keep b hjn y) := by
  simp only [tail_eq_iff]
  constructor
  · intro he
    constructor
    · intro q hq
      exact he q (hhj.trans hq)
    · intro q hq
      simpa only [commonWord_keep] using he (q.castLE hjn) hq
  · rintro ⟨he, hf⟩ q hq
    by_cases hqj : q.val < j
    · have hh := hf (⟨q.val, hqj⟩ : Fin j) hq
      have hi : Fin.castLE hjn (⟨q.val,hqj⟩ : Fin j) = q := Fin.ext rfl
      simpa only [commonWord_keep, hi] using hh
    · exact he q (by omega)

omit [DecidableEq Sector] in
private theorem keep_tail_injective (b : Sector → ℕ) {n j : ℕ} (h : j ≤ n) :
    Function.Injective (fun x : Level b n => (keep b h x, tail b h x)) := by
  rintro ⟨s,i⟩ ⟨t,k⟩ he
  have hk := congrArg Prod.fst he
  have hs : s = t := congrArg Sigma.fst hk
  subst t
  apply congrArg (Sigma.mk s)
  apply (digits b n s).injective
  funext q
  by_cases hq : q.val < j
  · have hv := congrArg (fun x : Level b j => commonWord b x ⟨q.val,hq⟩) hk
    simp only [commonWord_keep] at hv
    have hi : Fin.castLE h (⟨q.val,hq⟩ : Fin j) = q := Fin.ext rfl
    rw [hi] at hv
    exact Fin.ext (congrArg (fun v : Fin (alphabet b) => v.val) hv)
  · have ht := (tail_eq_iff b h ⟨s,i⟩ ⟨s,k⟩).mp (congrArg Prod.snd he)
    exact Fin.ext (congrArg (fun v : Fin (alphabet b) => v.val) (ht q (by omega)))

section Discard

variable {A C E : Type*} [Fintype A] [DecidableEq A]
  [Fintype C] [DecidableEq C] [Fintype E] [DecidableEq E]

private def discardKraus (g : A → C × E) (e : E) : Matrix C A ℂ :=
  fun y x => if g x = (y,e) then 1 else 0

omit [Fintype A] in
private theorem discard_complete (g : A → C × E) (hg : Function.Injective g) :
    (∑ e, (discardKraus g e)ᴴ * discardKraus g e) = 1 := by
  ext x z
  by_cases hxz : x = z
  · subst z
    simp [Matrix.sum_apply, discardKraus, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Prod.ext_iff, eq_comm, ite_and, ite_mul, mul_ite]
  · have he : ∀ e y, (starRingEnd ℂ) (discardKraus g e y x) * discardKraus g e y z = 0 := by
      intro e y
      simp only [discardKraus]
      split_ifs with hx hz
      · exact False.elim (hxz (hg (hx.trans hz.symm)))
      · simp
      · simp
      · simp
    simp [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, he, Matrix.one_apply, hxz]

private noncomputable def discardChannel (g : A → C × E) (hg : Function.Injective g) :
    QuantumChannel A C :=
  Classical.choose (finite_kraus_quantum_channel (discardKraus g) (discard_complete g hg))

private abbrev raw (channel : QuantumChannel A C) : Matrix A A ℂ →ₗ[ℂ] Matrix C C ℂ :=
  { CStarMatrix.ofMatrixₗ.symm.toLinearMap.comp
      (channel.toCompletelyPositiveMap.toLinearMap.comp CStarMatrix.ofMatrixₗ.toLinearMap) with
    toFun := fun X => CStarMatrix.ofMatrix.symm
      (channel.toCompletelyPositiveMap (CStarMatrix.ofMatrix X)) }

private theorem discard_action (g : A → C × E) (hg : Function.Injective g)
    (X : Matrix A A ℂ) :
    raw (discardChannel g hg) X = ∑ e, discardKraus g e * X * (discardKraus g e)ᴴ :=
  Classical.choose_spec (finite_kraus_quantum_channel (discardKraus g) (discard_complete g hg)) X

private theorem discard_single (g : A → C × E) (hg : Function.Injective g)
    (x z : A) (c : ℂ) :
    raw (discardChannel g hg) (Matrix.single x z c) =
      if (g x).2 = (g z).2 then Matrix.single (g x).1 (g z).1 c else 0 := by
  rw [discard_action]
  ext y w
  have hprod (e : E) :
      (discardKraus g e * Matrix.single x z c * (discardKraus g e)ᴴ) y w =
        discardKraus g e y x * c * star (discardKraus g e w z) := by
    simp [Matrix.mul_apply, Matrix.single_apply, Matrix.conjTranspose_apply,
      ite_and, ite_mul, mul_ite]
  simp only [Matrix.sum_apply, hprod]
  by_cases ht : (g x).2 = (g z).2
  · simp [discardKraus, Prod.ext_iff, ht, eq_comm, ite_and, ite_mul, mul_ite,
      Matrix.single_apply]
  · simp [discardKraus, Prod.ext_iff, ht, eq_comm, ite_and, ite_mul, mul_ite,
      Matrix.single_apply]

end Discard

private theorem raw_comp {A C D : Type*} [Fintype A] [DecidableEq A]
    [Fintype C] [DecidableEq C] [Fintype D] [DecidableEq D]
    (second : QuantumChannel C D) (first : QuantumChannel A C) (X : Matrix A A ℂ) :
    raw (second.comp first) X = raw second (raw first X) := by
  change CStarMatrix.ofMatrix.symm
    ((second.comp first).toCompletelyPositiveMap (CStarMatrix.ofMatrix X)) = _
  rw [QuantumChannel.comp_apply]
  change CStarMatrix.ofMatrix.symm
    (second.toCompletelyPositiveMap (first.toCompletelyPositiveMap (CStarMatrix.ofMatrix X))) =
      CStarMatrix.ofMatrix.symm (second.toCompletelyPositiveMap
        (CStarMatrix.ofMatrix (CStarMatrix.ofMatrix.symm
          (first.toCompletelyPositiveMap (CStarMatrix.ofMatrix X)))))
  rw [Equiv.apply_symm_apply]

private theorem channel_ext_single {A C : Type*} [Fintype A] [DecidableEq A]
    [Fintype C] [DecidableEq C] (first second : QuantumChannel A C)
    (h : ∀ x z, raw first (Matrix.single x z 1) = raw second (Matrix.single x z 1)) :
    first = second := by
  have hall (X : Matrix A A ℂ) : raw first X = raw second X := by
    have he : X = ∑ i, ∑ j, X i j • Matrix.single i j (1 : ℂ) := by
      simpa only [Matrix.smul_single, smul_eq_mul, mul_one] using Matrix.matrix_eq_sum_single X
    conv_lhs => rw [he]
    conv_rhs => rw [he]
    simp only [map_sum, map_smul]
    simp only [h]
  have hcp : first.toCompletelyPositiveMap = second.toCompletelyPositiveMap := by
    apply DFunLike.ext
    intro X
    apply CStarMatrix.ofMatrix.symm.injective
    have he := hall (CStarMatrix.ofMatrix.symm X)
    change CStarMatrix.ofMatrix.symm
      (first.toCompletelyPositiveMap (CStarMatrix.ofMatrix (CStarMatrix.ofMatrix.symm X))) =
        CStarMatrix.ofMatrix.symm
          (second.toCompletelyPositiveMap
            (CStarMatrix.ofMatrix (CStarMatrix.ofMatrix.symm X))) at he
    simpa only [Equiv.apply_symm_apply] using he
  cases first
  cases second
  cases hcp
  rfl

/-- Word Kraus matrices on the original compact physical carriers. -/
def localKraus (b : Sector → ℕ) {n j : ℕ} (h : j ≤ n) (e : Word b (n - j)) :
    Matrix (Level b j) (Level b n) ℂ :=
  discardKraus (fun x => (keep b h x, tail b h x)) e

private theorem local_complete (b : Sector → ℕ) {n j : ℕ} (h : j ≤ n) :
    (∑ e, (localKraus b h e)ᴴ * localKraus b h e) = 1 :=
  discard_complete _ (keep_tail_injective b h)

/-- Actual local CPTP discard with one common residual word alphabet. -/
noncomputable def localChannel (b : Sector → ℕ) {n j : ℕ} (h : j ≤ n) :
    QuantumChannel (Level b n) (Level b j) :=
  Classical.choose (finite_kraus_quantum_channel (localKraus b h) (local_complete b h))

private theorem local_single (b : Sector → ℕ) {n j : ℕ} (h : j ≤ n)
    (x z : Level b n) (c : ℂ) :
    raw (localChannel b h) (Matrix.single x z c) =
      if tail b h x = tail b h z then Matrix.single (keep b h x) (keep b h z) c else 0 :=
  discard_single _ (keep_tail_injective b h) x z c

private theorem local_comp (b : Sector → ℕ) {n j h : ℕ}
    (hjn : j ≤ n) (hhj : h ≤ j) :
    (localChannel b hhj).comp (localChannel b hjn) = localChannel b (hhj.trans hjn) := by
  apply channel_ext_single
  intro x z
  rw [raw_comp, local_single]
  by_cases he : tail b hjn x = tail b hjn z
  · rw [ite_eq_left he, local_single, local_single]
    by_cases hf : tail b hhj (keep b hjn x) = tail b hhj (keep b hjn z)
    · have hd := (tail_comp_iff b hjn hhj x z).mpr ⟨he,hf⟩
      simp only [ite_eq_left hf, ite_eq_left hd, keep_comp]
    · have hd : tail b (hhj.trans hjn) x ≠ tail b (hhj.trans hjn) z :=
        fun h => hf ((tail_comp_iff b hjn hhj x z).mp h).2
      simp only [ite_eq_right hf, ite_eq_right hd]
  · rw [ite_eq_right he, map_zero, local_single]
    have hd : tail b (hhj.trans hjn) x ≠ tail b (hhj.trans hjn) z :=
      fun h => he ((tail_comp_iff b hjn hhj x z).mp h).1
    rw [ite_eq_right hd]

private def pairKeep (b : Sector → ℕ) {n j : ℕ} (h : j ≤ n)
    (x : Level b n × Level b n) : Level b j × Level b j :=
  (keep b h x.1, keep b h x.2)

private def pairTail (b : Sector → ℕ) {n j : ℕ} (h : j ≤ n)
    (x : Level b n × Level b n) : Word b (n - j) × Word b (n - j) :=
  (tail b h x.1, tail b h x.2)

omit [DecidableEq Sector] in
private theorem pair_injective (b : Sector → ℕ) {n j : ℕ} (h : j ≤ n) :
    Function.Injective (fun x : Level b n × Level b n => (pairKeep b h x, pairTail b h x)) := by
  intro x z he
  have hk := congrArg Prod.fst he
  have ht := congrArg Prod.snd he
  have hkl : keep b h x.1 = keep b h z.1 := congrArg Prod.fst hk
  have hkr : keep b h x.2 = keep b h z.2 := congrArg Prod.snd hk
  have htl : tail b h x.1 = tail b h z.1 := congrArg Prod.fst ht
  have htr : tail b h x.2 = tail b h z.2 := congrArg Prod.snd ht
  apply Prod.ext
  · exact keep_tail_injective b h (Prod.ext hkl htl)
  · exact keep_tail_injective b h (Prod.ext hkr htr)

/-- The product of the two local physical discards, with independent word labels. -/
noncomputable def jointChannel (b : Sector → ℕ) {n j : ℕ} (h : j ≤ n) :
    QuantumChannel (Level b n × Level b n) (Level b j × Level b j) :=
  discardChannel (fun x => (pairKeep b h x, pairTail b h x)) (pair_injective b h)

private theorem joint_single (b : Sector → ℕ) {n j : ℕ} (h : j ≤ n)
    (x z : Level b n × Level b n) (c : ℂ) :
    raw (jointChannel b h) (Matrix.single x z c) =
      if pairTail b h x = pairTail b h z then
        Matrix.single (pairKeep b h x) (pairKeep b h z) c else 0 :=
  discard_single _ (pair_injective b h) x z c

omit [Fintype Sector] [DecidableEq Sector] in
private theorem pairKeep_comp (b : Sector → ℕ) {n j h : ℕ}
    (hjn : j ≤ n) (hhj : h ≤ j) (x : Level b n × Level b n) :
    pairKeep b hhj (pairKeep b hjn x) = pairKeep b (hhj.trans hjn) x := by
  simp only [pairKeep, keep_comp]

omit [DecidableEq Sector] in
private theorem pairTail_comp_iff (b : Sector → ℕ) {n j h : ℕ}
    (hjn : j ≤ n) (hhj : h ≤ j) (x z : Level b n × Level b n) :
    pairTail b (hhj.trans hjn) x = pairTail b (hhj.trans hjn) z ↔
      pairTail b hjn x = pairTail b hjn z ∧
      pairTail b hhj (pairKeep b hjn x) = pairTail b hhj (pairKeep b hjn z) := by
  simp only [pairTail, pairKeep, Prod.mk.injEq]
  rw [tail_comp_iff b hjn hhj x.1 z.1, tail_comp_iff b hjn hhj x.2 z.2]
  tauto

private theorem joint_comp (b : Sector → ℕ) {n j h : ℕ}
    (hjn : j ≤ n) (hhj : h ≤ j) :
    (jointChannel b hhj).comp (jointChannel b hjn) = jointChannel b (hhj.trans hjn) := by
  apply channel_ext_single
  intro x z
  rw [raw_comp, joint_single]
  by_cases he : pairTail b hjn x = pairTail b hjn z
  · rw [ite_eq_left he, joint_single, joint_single]
    by_cases hf : pairTail b hhj (pairKeep b hjn x) = pairTail b hhj (pairKeep b hjn z)
    · have hd := (pairTail_comp_iff b hjn hhj x z).mpr ⟨he,hf⟩
      simp only [ite_eq_left hf, ite_eq_left hd, pairKeep_comp]
    · have hd : pairTail b (hhj.trans hjn) x ≠ pairTail b (hhj.trans hjn) z :=
        fun h => hf ((pairTail_comp_iff b hjn hhj x z).mp h).2
      simp only [ite_eq_right hf, ite_eq_right hd]
  · rw [ite_eq_right he, map_zero, joint_single]
    have hd : pairTail b (hhj.trans hjn) x ≠ pairTail b (hhj.trans hjn) z :=
      fun h => he ((pairTail_comp_iff b hjn hhj x z).mp h).1
    rw [ite_eq_right hd]

private theorem raw_expand {A C : Type*} [Fintype A] [DecidableEq A]
    [Fintype C] [DecidableEq C] (channel : QuantumChannel A C) (X : Matrix A A ℂ) :
    raw channel X = ∑ x, ∑ z, X x z • raw channel (Matrix.single x z 1) := by
  have hX : X = ∑ x, ∑ z, X x z • Matrix.single x z (1 : ℂ) := by
    simpa only [Matrix.smul_single, smul_eq_mul, mul_one] using Matrix.matrix_eq_sum_single X
  conv_lhs => rw [hX]
  simp only [map_sum, map_smul]

private theorem joint_tensor (b : Sector → ℕ) {n j : ℕ} (h : j ≤ n) :
    TensorRealization (localChannel b h) (localChannel b h) (jointChannel b h) := by
  intro X
  change raw (jointChannel b h) X = _
  rw [raw_expand]
  ext y w
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Fintype.sum_prod_type]
  unfold tensorRawAction
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro v _
  change X (i,u) (k,v) * raw (jointChannel b h) (Matrix.single (i,u) (k,v) 1) y w =
    X (i,u) (k,v) * raw (localChannel b h) (Matrix.single i k 1) y.1 w.1 *
      raw (localChannel b h) (Matrix.single u v 1) y.2 w.2
  rw [joint_single, local_single, local_single]
  by_cases hl : tail b h i = tail b h k <;>
    by_cases hr : tail b h u = tail b h v <;>
    simp [pairTail, pairKeep, Prod.ext_iff, hl, hr, Matrix.single_apply,
      ite_and, ite_mul, mul_ite] <;> split_ifs <;> simp_all

omit [Fintype Sector] [DecidableEq Sector] in
private theorem keep_refl (b : Sector → ℕ) (n : ℕ) (x : Level b n) :
    keep b (le_refl n) x = x := by
  rcases x with ⟨s,i⟩
  simp [keep]

private theorem local_zero (b : Sector → ℕ) (n : ℕ) (X : Matrix (Level b n) (Level b n) ℂ) :
    raw (localChannel b (le_refl n)) X = X := by
  rw [raw_expand]
  have ht (x z : Level b n) : tail b (le_refl n) x = tail b (le_refl n) z := by
    funext q
    have hq := q.isLt
    omega
  simp only [local_single, ite_eq_left (ht _ _), keep_refl]
  simpa only [Matrix.smul_single, smul_eq_mul, mul_one] using (Matrix.matrix_eq_sum_single X).symm

private theorem joint_zero (b : Sector → ℕ) (n : ℕ)
    (X : Matrix (Level b n × Level b n) (Level b n × Level b n) ℂ) :
    raw (jointChannel b (le_refl n)) X = X := by
  rw [raw_expand]
  have ht (x z : Level b n × Level b n) : pairTail b (le_refl n) x = pairTail b (le_refl n) z := by
    apply Prod.ext
    all_goals
      funext q
      have hq := q.isLt
      omega
  simp only [joint_single, ite_eq_left (ht _ _), pairKeep, keep_refl]
  simpa only [Matrix.smul_single, smul_eq_mul, mul_one] using (Matrix.matrix_eq_sum_single X).symm

/-- The common-word construction gives actual compact local/product CPTP maps,
with strict composition on their entire physical matrix algebras. -/
theorem result (b : Sector → ℕ) :
    (∀ (n j : ℕ) (h : j ≤ n),
      TensorRealization (localChannel b h) (localChannel b h) (jointChannel b h)) ∧
    (∀ (n j h : ℕ) (hjn : j ≤ n) (hhj : h ≤ j),
      (localChannel b hhj).comp (localChannel b hjn) = localChannel b (hhj.trans hjn)) ∧
    (∀ (n j h : ℕ) (hjn : j ≤ n) (hhj : h ≤ j),
      (jointChannel b hhj).comp (jointChannel b hjn) = jointChannel b (hhj.trans hjn)) ∧
    (∀ (n j : ℕ) (h : j ≤ n) (x z : Level b n) (c : ℂ),
      CStarMatrix.ofMatrix.symm
        ((localChannel b h).toCompletelyPositiveMap (CStarMatrix.ofMatrix (Matrix.single x z c))) =
      if tail b h x = tail b h z then Matrix.single (keep b h x) (keep b h z) c else 0) ∧
    (∀ (n : ℕ) (X : Matrix (Level b n) (Level b n) ℂ),
      CStarMatrix.ofMatrix.symm
        ((localChannel b (le_refl n)).toCompletelyPositiveMap (CStarMatrix.ofMatrix X)) = X) ∧
    (∀ (n : ℕ) (X : Matrix (Level b n × Level b n) (Level b n × Level b n) ℂ),
      CStarMatrix.ofMatrix.symm
        ((jointChannel b (le_refl n)).toCompletelyPositiveMap (CStarMatrix.ofMatrix X)) = X) := by
  exact ⟨fun _ _ h => joint_tensor b h, fun _ _ _ hjn hhj => local_comp b hjn hhj,
    fun _ _ _ hjn hhj => joint_comp b hjn hhj, fun _ _ h x z c => local_single b h x z c,
    local_zero b, joint_zero b⟩

#print axioms result

end D5.S3.Quantum.Entanglement.SectorChannels.WordScaleTower
