/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPSUniformHardCoreMarginalWitness
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPSUniformHardCoreMarginalWitness
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: [lake/module/D5.S3.Quantum.TensorNetworks.PeriodicMPSUniformHardCoreEnergy, lake/module/D5.S3.Quantum.TensorNetworks.PeriodicMPSUniformHardCoreWitnessAmplitude, lake/module/D5.S3.Quantum.TensorNetworks.PeriodicMPSTwoSiteAmbiguity]
   utility: none
   digest: One adjacent marginal determines the fixed equal-weight independent-set amplitude up to phase among cyclic amplitudes for every length at least seven. -/
import D5.S3.Quantum.TensorNetworks.PeriodicMPSUniformHardCoreEnergy
import D5.S3.Quantum.TensorNetworks.PeriodicMPSUniformHardCoreWitnessAmplitude
import D5.S3.Quantum.TensorNetworks.PeriodicMPSTwoSiteAmbiguity

/-! The adjacent Gram matrix determines the shifted hard-core energy at fugacity one. -/

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.PeriodicMPSUniformHardCoreMarginalWitness

open PeriodicMPSParentIntersection (Bond Word)
open PeriodicMPSUniformHardCoreCounts
open PeriodicMPSUniformHardCoreEnergy
open UniformMPSExpectedDimensionRefutation (traceWord)
open scoped BigOperators Matrix

noncomputable section

variable {m : ℕ}

abbrev Pair := Fin 2 × Fin 2
abbrev Amplitudes (m : ℕ) := Word (2 + m) → ℂ

private def join (p : Pair) (b : Word m) : Word (2 + m) :=
  Fin.append ![p.1, p.2] b

private def wordEquiv (m : ℕ) : Pair × Word m ≃ Word (2 + m) :=
  (Equiv.prodCongr (finTwoArrowEquiv (Fin 2)).symm (Equiv.refl _)).trans (Fin.appendEquiv 2 m)

private theorem wordEquiv_apply (p : Pair) (b : Word m) :
    wordEquiv m (p, b) = join p b := rfl

@[simp] private theorem join_zero (p : Pair) (b : Word m) : join p b 0 = p.1 := by
  change Fin.append ![p.1, p.2] b (Fin.castAdd m (0 : Fin 2)) = _
  simp

@[simp] private theorem join_one (p : Pair) (b : Word m) : join p b 1 = p.2 := by
  have h : (1 : Fin (2 + m)) = Fin.castAdd m (1 : Fin 2) := by
    ext
    simp [Nat.mod_eq_of_lt (show 1 < 2 + m by omega)]
  rw [h]
  simp [join]

private theorem sum_words {R : Type*} [AddCommMonoid R] (f : Word (2 + m) → R) :
    (∑ w, f w) = ∑ p : Pair, ∑ b : Word m, f (join p b) := by
  calc
    _ = ∑ x : Pair × Word m, f (wordEquiv m x) := (Equiv.sum_comp (wordEquiv m) f).symm
    _ = _ := Fintype.sum_prod_type (fun x : Pair × Word m => f (wordEquiv m x))

/-- The Gram matrix of the actual first two bits with the remaining bits traced out. -/
def pairGram (ψ : Amplitudes m) : Matrix Pair Pair ℂ :=
  fun p q => ∑ b, ψ (join p b) * star (ψ (join q b))

theorem pairGram_traceWord (A : Fin 2 → Bond) (r : ℕ) :
    pairGram (traceWord 2 2 (2 + (r + 2)) A) = PeriodicMPSTwoSiteAmbiguity.rawTwo A r := by
  ext p q
  simp [pairGram, PeriodicMPSTwoSiteAmbiguity.rawTwo,
    PeriodicMPSParentIntersection.twoFlattening, join, Matrix.mul_apply]

/-- Translation moving the designated edge to the first two sites. -/
def rotateWord (i : Fin (2 + m)) (w : Word (2 + m)) : Word (2 + m) :=
  fun j => w (i + j)

private def rotateWordEquiv (i : Fin (2 + m)) : Word (2 + m) ≃ Word (2 + m) where
  toFun := rotateWord i
  invFun w j := w (j - i)
  left_inv w := by ext j; simp [rotateWord]
  right_inv w := by ext j; simp [rotateWord, add_comm i j]

/-- Invariance under every cyclic translation. -/
def Cyclic (ψ : Amplitudes m) : Prop :=
  ∀ i w, ψ (rotateWord i w) = ψ w

/-- Occupied sites in the binary word. -/
def occupied {n : ℕ} (w : Word n) : Finset (Fin n) :=
  Finset.univ.filter fun i => w i = 1

@[simp] theorem mem_occupied {n : ℕ} (w : Word n) (i : Fin n) :
    i ∈ occupied w ↔ w i = 1 := by simp [occupied]

/-- The binary word with exactly the specified occupied sites. -/
def configWord {n : ℕ} (S : Finset (Fin n)) : Word n :=
  fun i => if i ∈ S then 1 else 0

@[simp] theorem occupied_configWord {n : ℕ} (S : Finset (Fin n)) :
    occupied (configWord S) = S := by
  ext i
  by_cases h : i ∈ S <;> simp [configWord, h]

@[simp] theorem configWord_occupied {n : ℕ} (w : Word n) :
    configWord (occupied w) = w := by
  ext i
  by_cases h : w i = 0
  · simp [configWord, h]
  · simp [configWord, Fin.eq_one_of_ne_zero _ h]

/-- Vanishing of the observed 11 corner forces hard-core support on the whole cycle. -/
theorem support_of_pairGram_corner_zero (hn : 7 ≤ 2 + m) {ψ : Amplitudes m}
    (hcyc : Cyclic ψ) (hGram : pairGram ψ (1, 1) (1, 1) = 0)
    (w : Word (2 + m)) (hw : ¬ Independent (occupied w)) : ψ w = 0 := by
  have hmass : (∑ b : Word m, Complex.normSq (ψ (join (1, 1) b))) = 0 := by
    simpa [pairGram, Complex.re_sum, Complex.star_def, Complex.mul_conj] using
      congrArg Complex.re hGram
  have hfront (b : Word m) : ψ (join (1, 1) b) = 0 :=
    Complex.normSq_eq_zero.mp ((Finset.sum_eq_zero_iff_of_nonneg
      (fun b _ => Complex.normSq_nonneg (ψ (join (1, 1) b)))).mp hmass b (Finset.mem_univ b))
  rw [occupied, occupied_independent_iff hn] at hw
  push Not at hw
  obtain ⟨i, hi, hj⟩ := hw
  obtain ⟨⟨p, b⟩, he⟩ := (wordEquiv m).surjective (rotateWord i w)
  rw [wordEquiv_apply] at he
  have hp : p = (1, 1) := by
    apply Prod.ext
    · simpa [rotateWord] using (congrFun he 0).trans (by simpa [rotateWord] using hi)
    · simpa using (congrFun he 1).trans (by simpa [rotateWord, finRotate_apply] using hj)
  rw [← hcyc i w, ← he, hp]
  exact hfront b

/-- Total squared mass of the word amplitudes. -/
def mass (ψ : Amplitudes m) : ℝ := ∑ w, Complex.normSq (ψ w)

/-- The expectation of the negative single flip, half hop, and first-site number. -/
def edgeExpectation (ρ : Matrix Pair Pair ℂ) : ℝ :=
  -2 * ((ρ (0, 0) (1, 0)).re + (ρ (0, 1) (1, 1)).re) -
    (ρ (0, 1) (1, 0)).re - ((ρ (1, 0) (1, 0)).re + (ρ (1, 1) (1, 1)).re)

private def overlap (ψ : Amplitudes m) (u v : Word (2 + m)) : ℝ :=
  (ψ u * star (ψ v)).re

private theorem overlap_comm (ψ : Amplitudes m) (u v : Word (2 + m)) :
    overlap ψ u v = overlap ψ v u := by
  simp only [overlap, Complex.star_def, Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

private theorem overlap_self (ψ : Amplitudes m) (u : Word (2 + m)) :
    overlap ψ u u = Complex.normSq (ψ u) := by
  simp [overlap, Complex.mul_conj]

private def changed {n : ℕ} (u v : Word n) : Finset (Fin n) :=
  Finset.univ.filter fun k => u k ≠ v k

@[simp] private theorem mem_changed {n : ℕ} (u v : Word n) (k : Fin n) :
    k ∈ changed u v ↔ u k ≠ v k := by simp [changed]

private def localWeight (i : Fin (2 + m)) (u v : Word (2 + m)) : ℝ :=
  (if changed u v = {i} then 1 else 0) +
  (if changed u v = {i, finRotate (2 + m) i} ∧ u i ≠ u (finRotate (2 + m) i)
    then 1 / 2 else 0) +
  (if u = v ∧ u i = 1 then 1 else 0)

private def pairWeight (p q : Pair) : ℝ :=
  (if p.1 ≠ q.1 ∧ p.2 = q.2 then 1 else 0) +
  (if p.1 ≠ q.1 ∧ p.2 ≠ q.2 ∧ p.1 ≠ p.2 then 1 / 2 else 0) +
  (if p = q ∧ p.1 = 1 then 1 else 0)

private theorem castAdd_one (m : ℕ) : Fin.castAdd m (1 : Fin 2) = 1 := by
  ext
  simp [Nat.mod_eq_of_lt (show 1 < 2 + m by omega)]

private theorem natAdd_ne_zero (k : Fin m) : Fin.natAdd 2 k ≠ 0 := by
  intro h
  have hv := congrArg Fin.val h
  simp at hv

private theorem natAdd_ne_one (k : Fin m) : Fin.natAdd 2 k ≠ 1 := by
  intro h
  have hv := congrArg Fin.val h
  rw [← castAdd_one m] at hv
  change 2 + k.val = 1 at hv
  omega

private theorem changed_join (p q : Pair) (b c : Word m)
    (D : Finset (Fin (2 + m))) (hD : ∀ k ∈ D, k = 0 ∨ k = 1) :
    changed (join p b) (join q c) = D ↔
      (p.1 ≠ q.1 ↔ 0 ∈ D) ∧ (p.2 ≠ q.2 ↔ 1 ∈ D) ∧ b = c := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · rw [← h, mem_changed, join_zero, join_zero]
    · rw [← h, mem_changed, join_one, join_one]
    · funext k
      by_contra hne
      have hk : Fin.natAdd 2 k ∈ changed (join p b) (join q c) := by
        simpa [join] using hne
      exact (hD _ (h ▸ hk)).elim (natAdd_ne_zero k) (natAdd_ne_one k)
  · rintro ⟨h₀, h₁, rfl⟩
    ext k
    refine Fin.addCases (fun j => ?_) (fun j => ?_) k
    · fin_cases j
      · change (0 : Fin (2 + m)) ∈ changed (join p b) (join q b) ↔ 0 ∈ D
        simpa only [mem_changed, join_zero] using h₀
      · change Fin.castAdd m (1 : Fin 2) ∈ changed (join p b) (join q b) ↔
          Fin.castAdd m (1 : Fin 2) ∈ D
        rw [castAdd_one, mem_changed, join_one, join_one]
        exact h₁
    · have h : Fin.natAdd 2 j ∉ D := fun hj =>
        (hD _ hj).elim (natAdd_ne_zero j) (natAdd_ne_one j)
      simp [join, h]

private theorem localWeight_join (p q : Pair) (b c : Word m) :
    localWeight 0 (join p b) (join q c) = if b = c then pairWeight p q else 0 := by
  have h01 : (0 : Fin (2 + m)) ≠ 1 := by
    rw [← castAdd_one m]
    intro h
    have hv := congrArg Fin.val h
    change 0 = 1 at hv
    omega
  have hflip := changed_join p q b c {0} (by simp)
  have hhop := changed_join p q b c {0, 1} (by simp)
  simp [h01, Ne.symm h01] at hflip hhop
  have heq : join p b = join q c ↔ p = q ∧ b = c := by
    rw [← wordEquiv_apply, ← wordEquiv_apply, (wordEquiv m).injective.eq_iff, Prod.mk.injEq]
  simp only [localWeight, finRotate_apply, zero_add, hflip, hhop, heq, join_zero, join_one]
  by_cases h : b = c <;> simp [h, pairWeight, and_assoc]

private theorem localWeight_rotate (i : Fin (2 + m)) (u v : Word (2 + m)) :
    localWeight 0 (rotateWord i u) (rotateWord i v) = localWeight i u v := by
  have hchanged (D : Finset (Fin (2 + m))) :
      changed (rotateWord i u) (rotateWord i v) = D ↔
        changed u v = D.map (Equiv.addLeft i).toEmbedding := by
    have hmap : (changed (rotateWord i u) (rotateWord i v)).map
        (Equiv.addLeft i).toEmbedding = changed u v := by
      ext k
      obtain ⟨j, rfl⟩ := (Equiv.addLeft i).surjective k
      simp [rotateWord]
    constructor
    · intro h
      rw [← hmap, h]
    · intro h
      exact (Finset.map_injective _) (hmap.trans h)
  have heq : rotateWord i u = rotateWord i v ↔ u = v :=
    (rotateWordEquiv i).injective.eq_iff
  have ha (j : Fin (2 + m)) : Equiv.addLeft i j = i + j := rfl
  simp [localWeight, hchanged, ha, heq, rotateWord]

private theorem pairGram_re (ψ : Amplitudes m) (p q : Pair) :
    (pairGram ψ p q).re = ∑ b, overlap ψ (join p b) (join q b) := by
  simp [pairGram, overlap, Complex.re_sum]

private theorem pairGram_re_comm (ψ : Amplitudes m) (p q : Pair) :
    (pairGram ψ p q).re = (pairGram ψ q p).re := by
  simp only [pairGram_re, overlap_comm ψ (join p _) (join q _)]

private theorem edgeExpectation_eq_pair_sum (ψ : Amplitudes m) :
    -edgeExpectation (pairGram ψ) =
      ∑ p : Pair, ∑ q : Pair, pairWeight p q * (pairGram ψ p q).re := by
  rw [edgeExpectation]
  simp only [Fintype.sum_prod_type, Fin.sum_univ_two]
  norm_num [pairWeight, Prod.mk.injEq]
  rw [pairGram_re_comm ψ (1, 0) (0, 0), pairGram_re_comm ψ (1, 1) (0, 1),
    pairGram_re_comm ψ (1, 0) (0, 1)]
  ring

private theorem localWeight_expectation (ψ : Amplitudes m) (hcyc : Cyclic ψ)
    (i : Fin (2 + m)) :
    (∑ u, ∑ v, localWeight i u v * overlap ψ u v) = -edgeExpectation (pairGram ψ) := by
  calc
    _ = ∑ u, ∑ v, localWeight 0 u v * overlap ψ u v := by
      rw [← (Equiv.sum_comp (rotateWordEquiv i) (fun u =>
        ∑ v, localWeight 0 u v * overlap ψ u v))]
      refine Finset.sum_congr rfl fun u _ => ?_
      rw [← (Equiv.sum_comp (rotateWordEquiv i) (fun v =>
        localWeight 0 (rotateWordEquiv i u) v * overlap ψ (rotateWordEquiv i u) v))]
      exact Finset.sum_congr rfl fun v _ => by
        change _ = localWeight 0 (rotateWord i u) (rotateWord i v) *
          overlap ψ (rotateWord i u) (rotateWord i v)
        simp only [localWeight_rotate, overlap, hcyc i u, hcyc i v]
    _ = ∑ p : Pair, ∑ q : Pair, pairWeight p q * (pairGram ψ p q).re := by
      rw [sum_words]
      refine Finset.sum_congr rfl fun p _ => ?_
      simp only [sum_words (fun v => localWeight 0 (join p _) v * overlap ψ (join p _) v),
        localWeight_join, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true,
        pairGram_re, Finset.mul_sum]
      exact Finset.sum_comm
    _ = _ := (edgeExpectation_eq_pair_sum ψ).symm

@[simp] private theorem mem_changed_config {n : ℕ} (S T : Finset (Fin n)) (k : Fin n) :
    k ∈ changed (configWord S) (configWord T) ↔ ¬ (k ∈ S ↔ k ∈ T) := by
  by_cases hS : k ∈ S <;> by_cases hT : k ∈ T <;> simp [configWord, hS, hT]

private theorem changed_comm {n : ℕ} (u v : Word n) : changed u v = changed v u := by
  ext k
  simp [ne_comm]

private theorem erase_iff_changed {n : ℕ} {S T : Finset (Fin n)} {i : Fin n} (hi : i ∈ S) :
    T = S.erase i ↔ changed (configWord S) (configWord T) = {i} := by
  constructor
  · rintro rfl
    apply Finset.ext
    intro k
    rw [mem_changed_config]
    by_cases hk : k = i
    · subst k
      simp [hi]
    · simp [hk]
  · intro h
    ext k
    have hd : (¬ (k ∈ S ↔ k ∈ T)) ↔ k = i := by
      rw [← mem_changed_config, h, Finset.mem_singleton]
    by_cases hk : k = i
    · subst k
      simpa [hi] using hd
    · simpa [hk, iff_comm] using hd

private theorem replace_iff_changed {n : ℕ} {S T : Finset (Fin n)} {src dst : Fin n}
    (hs : src ∈ S) (hd : dst ∉ S) :
    T = insert dst (S.erase src) ↔ changed (configWord S) (configWord T) = {src, dst} := by
  have hne : src ≠ dst := fun h => hd (h ▸ hs)
  constructor
  · rintro rfl
    apply Finset.ext
    intro k
    rw [mem_changed_config]
    by_cases hks : k = src
    · subst k
      simp [hs, hne]
    · by_cases hkd : k = dst
      · subst k
        simp [hd]
      · simp [hks, hkd]
  · intro h
    ext k
    have hmem : (¬ (k ∈ S ↔ k ∈ T)) ↔ k = src ∨ k = dst := by
      rw [← mem_changed_config, h]
      simp
    by_cases hks : k = src
    · subst k
      simpa [hs, hne] using hmem
    · by_cases hkd : k = dst
      · subst k
        simpa [hd] using hmem
      · simpa [hks, hkd, iff_comm] using hmem

private theorem flipGraph_iff (S T : Configuration (2 + m)) :
    (flipGraph (2 + m)).Adj S T ↔
      ∃ i, changed (configWord S.val) (configWord T.val) = {i} := by
  constructor
  · rintro (⟨i, hi, ht⟩ | ⟨i, hi, ht⟩)
    · exact ⟨i, (erase_iff_changed hi).mp ht⟩
    · exact ⟨i, (changed_comm _ _).trans ((erase_iff_changed hi).mp ht)⟩
  · rintro ⟨i, hi⟩
    have hd : ¬ (i ∈ S.val ↔ i ∈ T.val) := by
      rw [← mem_changed_config, hi]
      simp
    change DeletionStep S T ∨ DeletionStep T S
    by_cases hs : i ∈ S.val
    · exact Or.inl ⟨i, hs, (erase_iff_changed hs).mpr hi⟩
    · have ht : i ∈ T.val := by simpa [hs] using hd
      exact Or.inr ⟨i, ht, (erase_iff_changed ht).mpr ((changed_comm _ _).trans hi)⟩

private theorem hopGraph_iff (hn : 7 ≤ 2 + m) (S T : Configuration (2 + m)) :
    (hopGraph (2 + m)).Adj S T ↔
      ∃ i, changed (configWord S.val) (configWord T.val) = {i, finRotate (2 + m) i} ∧
        configWord S.val i ≠ configWord S.val (finRotate (2 + m) i) := by
  constructor
  · rintro ⟨src, dst, ⟨ha, hs, hd, _⟩, he⟩
    have hc := (replace_iff_changed hs hd).mp he
    rcases (cycle_adj_iff hn src dst).mp ha with hb | hf
    · refine ⟨dst, ?_, ?_⟩
      · rw [hc, ← hb, Finset.pair_comm]
      · simp [← hb, configWord, hs, hd]
    · refine ⟨src, ?_, ?_⟩
      · rwa [← hf]
      · simp [← hf, configWord, hs, hd]
  · rintro ⟨i, hc, hne⟩
    let j := finRotate (2 + m) i
    change changed (configWord S.val) (configWord T.val) = {i, j} at hc
    change configWord S.val i ≠ configWord S.val j at hne
    have ha : (SimpleGraph.cycleGraph (2 + m)).Adj i j :=
      (cycle_adj_iff hn i j).mpr (Or.inr rfl)
    change HopStep S T
    by_cases hi : i ∈ S.val <;> by_cases hj : j ∈ S.val
    · simp [configWord, hi, hj] at hne
    · have he := (replace_iff_changed hi hj).mpr hc
      exact ⟨i, j, ⟨ha, hi, hj, he ▸ T.property⟩, he⟩
    · have he := (replace_iff_changed hj hi).mpr (hc.trans (Finset.pair_comm i j))
      exact ⟨j, i, ⟨ha.symm, hj, hi, he ▸ T.property⟩, he⟩
    · simp [configWord, hi, hj] at hne

private theorem rotatePair_injective (hn : 7 ≤ 2 + m) :
    Function.Injective (fun i : Fin (2 + m) => ({i, finRotate (2 + m) i} : Finset _)) := by
  intro i j he
  change ({i, finRotate (2 + m) i} : Finset _) = {j, finRotate (2 + m) j} at he
  have hmem : i ∈ ({j, finRotate (2 + m) j} : Finset _) := he ▸ Finset.mem_insert_self _ _
  rcases (Finset.mem_insert.mp hmem).elim Or.inl (fun h => Or.inr (Finset.mem_singleton.mp h))
    with hij | hij
  · exact hij
  · exfalso
    have hh : finRotate (2 + m) i ∈ ({j, finRotate (2 + m) j} : Finset _) :=
      he ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    have hn1 : finRotate (2 + m) i ≠ i :=
      ((cycle_adj_iff hn i (finRotate (2 + m) i)).mpr (Or.inr rfl)).symm.ne
    rw [← hij] at hh
    have hj : finRotate (2 + m) i = j :=
      (Finset.mem_insert.mp hh).resolve_right (by simpa using hn1)
    have h2 : (1 : Fin (2 + m)) + 1 = 0 := by
      apply add_left_cancel (a := j)
      rw [← add_assoc, ← finRotate_apply, ← finRotate_apply, ← hij, hj, add_zero]
    have hv := congrArg Fin.val h2
    simp [Fin.val_add, Nat.mod_eq_of_lt (show 1 < 2 + m by omega),
      Nat.mod_eq_of_lt (show 1 + 1 < 2 + m by omega)] at hv

private theorem sum_indicator {ι : Type*} [Fintype ι] (p : ι → Prop) [DecidablePred p]
    (c : ℝ) (hunique : ∀ a b, p a → p b → a = b) :
    (∑ i, if p i then c else 0) = if ∃ i, p i then c else 0 := by
  classical
  by_cases h : ∃ i, p i
  · rw [ite_eq_left h]
    obtain ⟨i, hi⟩ := h
    rw [Finset.sum_eq_single i, ite_eq_left hi]
    · exact fun j _ hji => ite_eq_right fun hj => hji (hunique j i hj hi)
    · simp
  · rw [ite_eq_right h]
    exact Finset.sum_eq_zero fun i _ => ite_eq_right fun hi => h ⟨i, hi⟩

private theorem sum_localWeight (hn : 7 ≤ 2 + m) (S T : Configuration (2 + m)) :
    (∑ i, localWeight i (configWord S.val) (configWord T.val)) =
      transitionWeight S T + if S = T then (S.val.card : ℝ) else 0 := by
  classical
  simp only [localWeight, Finset.sum_add_distrib]
  rw [sum_indicator, sum_indicator]
  · simp only [← flipGraph_iff, ← hopGraph_iff hn, transitionWeight]
    congr 1
    have heq : configWord S.val = configWord T.val ↔ S = T := by
      constructor
      · intro h
        exact Subtype.ext (by simpa using congrArg occupied h)
      · rintro rfl
        rfl
    by_cases h : S = T
    · simp only [h, true_and, ite_true]
      simp [configWord, apply_ite (fun x : Fin 2 => x = 1)]
    · simp [heq, h]
  · intro i j hi hj
    exact rotatePair_injective hn (hi.1.symm.trans hj.1)
  · intro i j hi hj
    simpa using hi.symm.trans hj

private def independentWordEquiv (m : ℕ) :
    Configuration (2 + m) ≃ {w : Word (2 + m) // Independent (occupied w)} where
  toFun S := ⟨configWord S.val, by simpa using S.property⟩
  invFun w := ⟨occupied w.val, w.property⟩
  left_inv S := Subtype.ext (occupied_configWord S.val)
  right_inv w := Subtype.ext (configWord_occupied w.val)

private theorem sum_restrict (f : Word (2 + m) → ℝ)
    (hf : ∀ w, ¬ Independent (occupied w) → f w = 0) :
    (∑ w, f w) = ∑ S : Configuration (2 + m), f (configWord S.val) := by
  classical
  calc
    _ = ∑ w ∈ Finset.univ.filter (fun w => Independent (occupied w)), f w := by
      symm
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro w _ hw
      exact hf w (by simpa using hw)
    _ = ∑ w : {w : Word (2 + m) // Independent (occupied w)}, f w.val :=
      Finset.sum_subtype _ (by simp) f
    _ = _ := (Equiv.sum_comp (independentWordEquiv m) (fun w => f w.val)).symm

private theorem shiftedEnergy_eq_sum (hn : 7 ≤ 2 + m) (ψ : Amplitudes m) :
    shiftedEnergy (fun S : Configuration (2 + m) => ψ (configWord S.val)) =
      ((2 + m : ℕ) : ℝ) * (∑ S : Configuration (2 + m), Complex.normSq (ψ (configWord S.val))) -
        ∑ S : Configuration (2 + m), ∑ T : Configuration (2 + m),
          (∑ i, localWeight i (configWord S.val) (configWord T.val)) *
            overlap ψ (configWord S.val) (configWord T.val) := by
  classical
  simp only [shiftedEnergy, dotProduct, Matrix.mulVec, Finset.mul_sum, Pi.star_apply,
    Complex.re_sum, Matrix.map_apply, shiftedHamiltonian, Matrix.sub_apply, Matrix.of_apply,
    Matrix.diagonal_apply, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun S _ => ?_
  have hdiag :
      (((2 + m : ℕ) : ℝ) * Complex.normSq (ψ (configWord S.val))) =
        ∑ T : Configuration (2 + m), (if S = T then ((2 + m : ℕ) : ℝ) else 0) *
          overlap ψ (configWord S.val) (configWord T.val) := by
    simp [ite_mul, Finset.sum_ite_eq, overlap_self]
  rw [hdiag, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun T _ => ?_
  rw [sum_localWeight hn]
  simp only [overlap, Complex.star_def, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re, Complex.conj_im]
  by_cases h : S = T <;> simp [h] <;> ring

/-- One adjacent Gram matrix and the mass give the shifted energy of the supported vector. -/
theorem shiftedEnergy_eq_observed (hn : 7 ≤ 2 + m) {ψ : Amplitudes m}
    (hcyc : Cyclic ψ) (hsupp : ∀ w, ¬ Independent (occupied w) → ψ w = 0) :
    shiftedEnergy (fun S : Configuration (2 + m) => ψ (configWord S.val)) =
      ((2 + m : ℕ) : ℝ) * mass ψ + ((2 + m : ℕ) : ℝ) * edgeExpectation (pairGram ψ) := by
  rw [shiftedEnergy_eq_sum hn, mass, sum_restrict _ (fun w hw => by simp [hsupp w hw])]
  have hsum :
      (∑ u, ∑ v, (∑ i, localWeight i u v) * overlap ψ u v) =
        ∑ S : Configuration (2 + m), ∑ T : Configuration (2 + m),
          (∑ i, localWeight i (configWord S.val) (configWord T.val)) *
            overlap ψ (configWord S.val) (configWord T.val) := by
    rw [sum_restrict _ (fun w hw => by simp [overlap, hsupp w hw])]
    refine Finset.sum_congr rfl fun S _ => ?_
    exact sum_restrict _ (fun w hw => by simp [overlap, hsupp w hw])
  rw [← hsum]
  have hswap :
      (∑ u, ∑ v, (∑ i, localWeight i u v) * overlap ψ u v) =
        ∑ i, ∑ u, ∑ v, localWeight i u v * overlap ψ u v := by
    simp only [Finset.sum_mul]
    calc
      _ = ∑ u, ∑ i, ∑ v, localWeight i u v * overlap ψ u v :=
        Finset.sum_congr rfl fun u _ => Finset.sum_comm
      _ = _ := Finset.sum_comm
  rw [hswap]
  simp [localWeight_expectation ψ hcyc, nsmul_eq_mul]

theorem mass_eq_trace (ψ : Amplitudes m) : mass ψ = (pairGram ψ).trace.re := by
  rw [mass, sum_words]
  simp [Matrix.trace, Complex.re_sum, pairGram_re, overlap_self]

/-- The unnormalized equal-amplitude hard-core vector. -/
def independentIndicator (m : ℕ) : Amplitudes m :=
  fun w => if Independent (occupied w) then 1 else 0

private theorem independent_rotateWord (hn : 7 ≤ 2 + m) (i : Fin (2 + m)) (w : Word (2 + m)) :
    Independent (occupied (rotateWord i w)) ↔ Independent (occupied w) := by
  unfold occupied
  rw [occupied_independent_iff hn (rotateWord i w), occupied_independent_iff hn w]
  simp only [rotateWord, finRotate_apply, ← add_assoc]
  constructor
  · intro h j
    obtain ⟨k, hk⟩ := (Equiv.addLeft i).surjective j
    change i + k = j at hk
    rw [← hk]
    exact h k
  · intro h j
    exact h (i + j)

/-- The indicator is invariant under translation. -/
theorem cyclic_independentIndicator (hn : 7 ≤ 2 + m) : Cyclic (independentIndicator m) := by
  intro i w
  simp [independentIndicator, independent_rotateWord hn]

/-- A cyclic vector with the same Gram as a scaled hard-core indicator is constant on
the independent words and vanishes on all other words. -/
theorem eq_constant_of_pairGram_eq_indicator (hn : 7 ≤ 2 + m) {ψ : Amplitudes m}
    (hcyc : Cyclic ψ) (a : ℂ) (hGram : pairGram ψ = pairGram (fun w => a * independentIndicator m w)) :
    ∃ c : ℂ, ∀ w, ψ w = c * independentIndicator m w := by
  let χ : Amplitudes m := fun w => a * independentIndicator m w
  have hχcyc : Cyclic χ := fun i w => congrArg (a * ·) (cyclic_independentIndicator hn i w)
  have hχsupp (w : Word (2 + m)) (hw : ¬ Independent (occupied w)) : χ w = 0 := by
    simp [χ, independentIndicator, hw]
  have hχfront (b : Word m) : χ (join (1, 1) b) = 0 := by
    apply hχsupp
    simp only [occupied, occupied_independent_iff hn]
    intro h
    have := h 0 (join_zero (1, 1) b)
    simp at this
  have hcorner : pairGram ψ (1, 1) (1, 1) = 0 := by
    rw [hGram]
    change pairGram χ (1, 1) (1, 1) = 0
    simp [pairGram, hχfront]
  have hsupp := support_of_pairGram_corner_zero hn hcyc hcorner
  have hzero : shiftedEnergy (fun S : Configuration (2 + m) => χ (configWord S.val)) = 0 := by
    apply (shiftedEnergy_eq_zero_iff hn _).mpr
    intro S
    simp [χ, independentIndicator, S.property, (emptyConfiguration (2 + m)).property]
  have hm : mass ψ = mass χ := by rw [mass_eq_trace, mass_eq_trace, hGram]
  have hψzero : shiftedEnergy (fun S : Configuration (2 + m) => ψ (configWord S.val)) = 0 := by
    rw [shiftedEnergy_eq_observed hn hcyc hsupp, hm, hGram]
    exact (shiftedEnergy_eq_observed hn hχcyc hχsupp).symm.trans hzero
  let e := configWord (emptyConfiguration (2 + m)).val
  refine ⟨ψ e, fun w => ?_⟩
  by_cases hw : Independent (occupied w)
  · have hconst := (shiftedEnergy_eq_zero_iff hn _).mp hψzero ⟨occupied w, hw⟩
    simpa [e, independentIndicator, hw] using hconst
  · simp [independentIndicator, hw, hsupp w hw]

private theorem mass_scaled_indicator (a : ℂ) :
    mass (fun w => a * independentIndicator m w) =
      Complex.normSq a * mass (independentIndicator m) := by
  simp only [mass, Complex.normSq_mul, Finset.mul_sum]

/-- The same observed Gram also fixes the modulus of the constant amplitude. -/
theorem eq_constant_same_norm_of_pairGram_eq_indicator (hn : 7 ≤ 2 + m) {ψ : Amplitudes m}
    (hcyc : Cyclic ψ) (a : ℂ) (hGram : pairGram ψ = pairGram (fun w => a * independentIndicator m w)) :
    ∃ c : ℂ, Complex.normSq c = Complex.normSq a ∧ ∀ w, ψ w = c * independentIndicator m w := by
  obtain ⟨c, hc⟩ := eq_constant_of_pairGram_eq_indicator hn hcyc a hGram
  have hmass : mass ψ = mass (fun w => a * independentIndicator m w) :=
    (mass_eq_trace ψ).trans (by rw [hGram, ← mass_eq_trace])
  rw [funext hc, mass_scaled_indicator, mass_scaled_indicator] at hmass
  have hpos : 0 < mass (independentIndicator m) := by
    let e := emptyConfiguration (2 + m)
    have he : Complex.normSq (independentIndicator m (configWord e.val)) = 1 := by
      simp [independentIndicator, e.property]
    have hle := Finset.single_le_sum
      (f := fun w => Complex.normSq (independentIndicator m w))
      (fun w _ => Complex.normSq_nonneg (independentIndicator m w))
      (Finset.mem_univ (configWord e.val))
    rw [he] at hle
    exact lt_of_lt_of_le zero_lt_one hle
  exact ⟨c, mul_right_cancel₀ hpos.ne' hmass, hc⟩

/-- Periodic trace amplitudes are cyclic by the trace identity for two factors. -/
theorem cyclic_traceWord (A : Fin 2 → Bond) : Cyclic (traceWord 2 2 (2 + m) A) := by
  let ψ := traceWord 2 2 (2 + m) A
  have hstep (n : ℕ) (w : Word n) :
      traceWord 2 2 n A (w ∘ finRotate n) = traceWord 2 2 n A w := by
    cases n with
    | zero => rfl
    | succ n =>
      have hw : w ∘ finRotate (n + 1) = Fin.snoc (Fin.tail w) (w 0) := by
        have he := (Fin.snoc_eq_cons_rotate (Fin.tail w) (w 0)).symm
        rw [Fin.cons_self_tail] at he
        exact he
      rw [hw]
      change (PeriodicMPSParentIntersection.wordMatrix A (Fin.snoc (Fin.tail w) (w 0))).trace =
        (PeriodicMPSParentIntersection.wordMatrix A w).trace
      conv_rhs => rw [← Fin.cons_self_tail w, PeriodicMPSParentIntersection.wordMatrix_cons]
      rw [PeriodicMPSParentIntersection.wordMatrix_snoc, Matrix.trace_mul_comm]
  intro i w
  have hiter (k : ℕ) (v : Word (2 + m)) :
      ψ (v ∘ (finRotate (2 + m))^[k]) = ψ v := by
    induction k generalizing v with
    | zero => rfl
    | succ k ih =>
      rw [Function.iterate_succ', ← Function.comp_assoc, ih]
      exact hstep (2 + m) v
  have he : rotateWord i w = w ∘ finCycle i := by
    ext j
    simp [rotateWord, finCycle, add_comm]
  rw [he, finCycle_eq_finRotate_iterate]
  exact hiter i.val w

/-- Literal equality of the observed two-site Gram at the hard-core core determines all
periodic amplitudes up to a unit scalar. -/
theorem traceWord_eq_unit_of_rawTwo_eq_witness (A : Fin 2 → Bond) (r : ℕ)
    (hn : 7 ≤ 2 + (r + 2))
    (hGram : PeriodicMPSTwoSiteAmbiguity.rawTwo A r =
      PeriodicMPSTwoSiteAmbiguity.rawTwo PeriodicMPSUniformDeterminantPencil.witnessCore r) :
    ∃ c : ℂ, Complex.normSq c = 1 ∧
      ∀ w, traceWord 2 2 (2 + (r + 2)) A w =
        c * traceWord 2 2 (2 + (r + 2)) PeriodicMPSUniformDeterminantPencil.witnessCore w := by
  have hw (w : Word (2 + (r + 2))) :
      traceWord 2 2 (2 + (r + 2)) PeriodicMPSUniformDeterminantPencil.witnessCore w =
        independentIndicator (r + 2) w :=
    PeriodicMPSUniformHardCoreWitnessAmplitude.traceWord_witnessCore_eq_indicator hn w
  have hg : pairGram (traceWord 2 2 (2 + (r + 2)) A) =
      pairGram (fun w => (1 : ℂ) * independentIndicator (r + 2) w) := by
    simp only [one_mul, ← funext hw, pairGram_traceWord, hGram]
  obtain ⟨c, hc, he⟩ :=
    eq_constant_same_norm_of_pairGram_eq_indicator hn (cyclic_traceWord A) 1 hg
  refine ⟨c, by simpa using hc, fun w => ?_⟩
  rw [he, hw]

end

end D5.S3.Quantum.TensorNetworks.PeriodicMPSUniformHardCoreMarginalWitness
