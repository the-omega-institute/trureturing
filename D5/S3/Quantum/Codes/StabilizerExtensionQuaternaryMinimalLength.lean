/- GID: D5/S3/Quantum/Codes/StabilizerExtensionQuaternaryMinimalLength
   generality: I
   mirror-B: D5/B/S3/Quantum/Codes/StabilizerExtensionQuaternaryMinimalLength
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Codes/StabilizerExtensionQuaternaryMinimalLength.claim; result=D5/S3/Quantum/Codes/StabilizerExtensionQuaternaryMinimalLength.result; claim=D5/S3/Quantum/Codes/StabilizerExtensionQuaternaryMinimalLength.claim
   digest: Explicit quaternary additive-code counterexamples refute the length-five expectation. -/

import D5.S1.Recurrence.Residue.ExponentialSquareWeightCatalanParity
import D5.S3.Observer.HilbertGeometry.GoldenAntiIsometry
import D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.FirstWindowBoundaryAttainment
import D5.S3.Quantum.Information.SingerQuadricQubitDistanceCeiling

noncomputable section

namespace D5.S3.Quantum.Codes.StabilizerExtensionQuaternaryMinimalLength

set_option autoImplicit false
set_option relaxedAutoImplicit false

open D5.S3.Quantum.Information.SingerQuadricQubitDistanceCeiling (K)
open D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.FirstWindowBoundaryAttainment (Pair)
open D5.S1.Recurrence.Residue.ExponentialSquareWeightCatalanParity (binary)
open D5.S3.Observer.HilbertGeometry.GoldenAntiIsometry (HilbertPhase)

attribute [local instance]
  D5.S3.Quantum.Information.SingerQuadricQubitDistanceCeiling.instFintypeK
  D5.S3.Quantum.Information.SingerQuadricQubitDistanceCeiling.instDecidableEqK

private lemma card_F4 : Fintype.card (K 1) = 4 := by
  simpa [Nat.card_eq_fintype_card] using
    (GaloisField.card 2 2 (by decide : (2 : ℕ) ≠ 0))

private lemma exists_nonbase : ∃ x : K 1, x ≠ 0 ∧ x ≠ 1 := by
  exact ENat.exists_ne_ne_of_three_le
    (by norm_num [ENat.card_eq_coe_fintype_card, card_F4]) 0 1

private noncomputable def omega : K 1 := Classical.choose exists_nonbase

private lemma omega_ne_zero : omega ≠ 0 := (Classical.choose_spec exists_nonbase).1
private lemma omega_ne_one : omega ≠ 1 := (Classical.choose_spec exists_nonbase).2

private lemma omega_add_one_ne_zero : omega + 1 ≠ 0 :=
  mt CharTwo.add_eq_zero.mp omega_ne_one

private lemma one_add_omega_ne_zero : 1 + omega ≠ 0 := by
  simpa [add_comm] using omega_add_one_ne_zero

def tr (x : K 1) : K 1 := x + x ^ 2

def symp {n : ℕ} (u v : Fin n → HilbertPhase (K 1)) : K 1 :=
  tr (∑ i, ((u i).1 * (v i).2 - (v i).1 * (u i).2))

private lemma wt3_two_01 {u : Fin 3 → HilbertPhase (K 1)} (h0 : u 0 ≠ 0) (h1 : u 1 ≠ 0)
    (h2 : u 2 = 0) : hammingNorm u = 2 := by
  have hp (i : Fin 3) : (u i ≠ 0) ↔ (i = 0 ∨ i = 1) := by
    fin_cases i <;> simp [h0, h1, h2]
  rw [hammingNorm, Finset.filter_congr (by intro i hi; exact hp i)]
  decide

private lemma wt3_two_02 {u : Fin 3 → HilbertPhase (K 1)} (h0 : u 0 ≠ 0) (h1 : u 1 = 0)
    (h2 : u 2 ≠ 0) : hammingNorm u = 2 := by
  have hp (i : Fin 3) : (u i ≠ 0) ↔ (i = 0 ∨ i = 2) := by
    fin_cases i <;> simp [h0, h1, h2]
  rw [hammingNorm, Finset.filter_congr (by intro i hi; exact hp i)]
  decide

private lemma wt3_two_12 {u : Fin 3 → HilbertPhase (K 1)} (h0 : u 0 = 0) (h1 : u 1 ≠ 0)
    (h2 : u 2 ≠ 0) : hammingNorm u = 2 := by
  have hp (i : Fin 3) : (u i ≠ 0) ↔ (i = 1 ∨ i = 2) := by
    fin_cases i <;> simp [h0, h1, h2]
  rw [hammingNorm, Finset.filter_congr (by intro i hi; exact hp i)]
  decide

def selfOrthogonal {n : ℕ} (C : AddSubgroup (Fin n → HilbertPhase (K 1))) : Prop :=
  ∀ u ∈ C, ∀ v ∈ C, symp u v = 0

private noncomputable def rangeEquiv {V W : Type*} [AddCommGroup V] [AddCommGroup W]
    (g : Pair →+ V) (h : Pair →+ W) (hg : Function.Injective g) (hh : Function.Injective h) :
    g.range ≃+ h.range :=
  (g.ofInjective hg).symm.trans (h.ofInjective hh)

private lemma rangeEquiv_apply {V W : Type*} [AddCommGroup V] [AddCommGroup W]
    (g : Pair →+ V) (h : Pair →+ W) (hg : Function.Injective g) (hh : Function.Injective h)
    (p : Pair) : rangeEquiv g h hg hh
      ⟨g p, AddMonoidHom.mem_range.mpr ⟨p, rfl⟩⟩ =
      ⟨h p, AddMonoidHom.mem_range.mpr ⟨p, rfl⟩⟩ := by
  apply Subtype.ext
  change h ((g.ofInjective hg).symm
      ⟨g p, AddMonoidHom.mem_range.mpr ⟨p, rfl⟩⟩) = h p
  exact congrArg h ((g.ofInjective hg).symm_apply_apply p)

private def c1Hom : Pair →+ (Fin 1 → HilbertPhase (K 1)) :=
  { toFun := fun p => fun _ =>
      (algebraMap (ZMod 2) (K 1) p.1 + algebraMap (ZMod 2) (K 1) p.2 * omega, 0)
    map_zero' := by ext i <;> simp
    map_add' := by
      intro p q
      funext i
      simp [add_mul, add_assoc, add_left_comm, add_comm] }

private def d1Hom : Pair →+ (Fin 1 → HilbertPhase (K 1)) :=
  { toFun := fun p => fun _ => (algebraMap (ZMod 2) (K 1) p.1, algebraMap (ZMod 2) (K 1) p.2)
    map_zero' := by ext i <;> simp
    map_add' := by intro p q; funext i; simp }

private lemma c1Hom_injective : Function.Injective c1Hom := by
  intro p q h
  rcases p with ⟨a, b⟩
  rcases q with ⟨c, d⟩
  have h0 := congrFun h 0
  change (algebraMap (ZMod 2) (K 1) a + algebraMap (ZMod 2) (K 1) b * omega, 0) =
    (algebraMap (ZMod 2) (K 1) c + algebraMap (ZMod 2) (K 1) d * omega, 0) at h0
  rcases binary a with rfl | rfl <;>
    rcases binary b with rfl | rfl <;>
        rcases binary c with rfl | rfl <;>
        rcases binary d with rfl | rfl <;>
          simp_all [omega_ne_zero, omega_ne_one,
            omega_add_one_ne_zero] <;>
            first
            | exact omega_ne_zero h0.symm
            | exact one_add_omega_ne_zero h0.symm
            | exact omega_ne_one h0.symm
            | exact one_add_omega_ne_zero h0

private lemma d1Hom_injective : Function.Injective d1Hom := by
  exact (Function.const_injective (α := Fin 1)).comp
    ((algebraMap (ZMod 2) (K 1)).injective.prodMap
      (algebraMap (ZMod 2) (K 1)).injective)

private def c3Hom : Pair →+ (Fin 3 → HilbertPhase (K 1)) :=
  { toFun := fun p => ![
      (algebraMap (ZMod 2) (K 1) p.1, algebraMap (ZMod 2) (K 1) p.2 * omega),
      (algebraMap (ZMod 2) (K 1) p.1, algebraMap (ZMod 2) (K 1) p.2 * omega),
      (0, 0)]
    map_zero' := by funext i; fin_cases i <;> simp
    map_add' := by
      intro p q
      funext i
      fin_cases i <;> simp [add_mul, add_assoc, add_left_comm, add_comm] }

private def d3Hom : Pair →+ (Fin 3 → HilbertPhase (K 1)) :=
  { toFun := fun p => ![
      (algebraMap (ZMod 2) (K 1) (p.1 + p.2), 0),
      (algebraMap (ZMod 2) (K 1) p.1, 0),
      (algebraMap (ZMod 2) (K 1) p.2, 0)]
    map_zero' := by funext i; fin_cases i <;> simp
    map_add' := by
      intro p q
      funext i
      fin_cases i <;> simp [add_assoc, add_left_comm, add_comm] }

private lemma c3Hom_injective : Function.Injective c3Hom := by
  exact Function.Injective.of_comp (f := fun u : Fin 3 → HilbertPhase (K 1) => u 0) (g := c3Hom)
    ((algebraMap (ZMod 2) (K 1)).injective.prodMap
      ((mul_left_injective₀ omega_ne_zero).comp (algebraMap (ZMod 2) (K 1)).injective))

private lemma d3Hom_injective : Function.Injective d3Hom := by
  exact Function.Injective.of_comp (f := fun u : Fin 3 → HilbertPhase (K 1) => ((u 1).1, (u 2).1))
    (g := d3Hom) ((algebraMap (ZMod 2) (K 1)).injective.prodMap
      (algebraMap (ZMod 2) (K 1)).injective)

private abbrev C1 : AddSubgroup (Fin 1 → HilbertPhase (K 1)) := c1Hom.range
private abbrev D1 : AddSubgroup (Fin 1 → HilbertPhase (K 1)) := d1Hom.range
private abbrev C3 : AddSubgroup (Fin 3 → HilbertPhase (K 1)) := c3Hom.range
private abbrev D3 : AddSubgroup (Fin 3 → HilbertPhase (K 1)) := d3Hom.range

private noncomputable def f1 : C1 ≃+ D1 :=
  rangeEquiv c1Hom d1Hom c1Hom_injective d1Hom_injective

private noncomputable def f3 : C3 ≃+ D3 :=
  rangeEquiv c3Hom d3Hom c3Hom_injective d3Hom_injective

private lemma selfOrthogonal_C1 : selfOrthogonal C1 := by
  intro u hu v hv
  obtain ⟨p, hp⟩ := hu
  obtain ⟨q, hq⟩ := hv
  subst u
  subst v
  simp [symp, tr, c1Hom, Fin.sum_univ_succ, CharTwo.add_self_eq_zero]

private lemma selfOrthogonal_D1 : selfOrthogonal D1 := by
  intro u hu v hv
  obtain ⟨p, hp⟩ := hu
  obtain ⟨q, hq⟩ := hv
  subst u
  subst v
  rcases p with ⟨a, b⟩
  rcases q with ⟨c, d⟩
  rcases binary a with rfl | rfl <;>
    rcases binary b with rfl | rfl <;>
      rcases binary c with rfl | rfl <;>
        rcases binary d with rfl | rfl <;>
          simp [symp, tr, d1Hom, Fin.sum_univ_succ, CharTwo.add_self_eq_zero]

private lemma f1_on (p : Pair) :
    f1 ⟨c1Hom p, AddMonoidHom.mem_range.mpr ⟨p, rfl⟩⟩ =
      ⟨d1Hom p, AddMonoidHom.mem_range.mpr ⟨p, rfl⟩⟩ := by
  exact rangeEquiv_apply c1Hom d1Hom c1Hom_injective d1Hom_injective p

private lemma f1_weight : ∀ u : C1,
    hammingNorm (f1 u : Fin 1 → HilbertPhase (K 1)) =
      hammingNorm (u : Fin 1 → HilbertPhase (K 1)) := by
  intro u
  obtain ⟨p, hp⟩ := u.property
  have hu : u = ⟨c1Hom p, AddMonoidHom.mem_range.mpr ⟨p, rfl⟩⟩ := by
    exact Subtype.ext hp.symm
  subst u
  rw [f1_on]
  rcases p with ⟨a, b⟩
  rcases binary a with rfl | rfl <;>
    rcases binary b with rfl | rfl <;>
      simp [hammingNorm, c1Hom, d1Hom, omega_ne_zero, omega_ne_one,
        omega_add_one_ne_zero, one_add_omega_ne_zero]

private lemma selfOrthogonal_C3 : selfOrthogonal C3 := by
  intro u hu v hv
  obtain ⟨p, hp⟩ := hu
  obtain ⟨q, hq⟩ := hv
  subst u
  subst v
  simp [symp, tr, c3Hom, Fin.sum_univ_succ, sub_eq_add_neg, CharTwo.add_self_eq_zero]

private lemma selfOrthogonal_D3 : selfOrthogonal D3 := by
  intro u hu v hv
  obtain ⟨p, hp⟩ := hu
  obtain ⟨q, hq⟩ := hv
  subst u
  subst v
  simp [symp, tr, d3Hom, Fin.sum_univ_succ]

private lemma f3_on (p : Pair) :
    f3 ⟨c3Hom p, AddMonoidHom.mem_range.mpr ⟨p, rfl⟩⟩ =
      ⟨d3Hom p, AddMonoidHom.mem_range.mpr ⟨p, rfl⟩⟩ := by
  exact rangeEquiv_apply c3Hom d3Hom c3Hom_injective d3Hom_injective p

private lemma f3_weight : ∀ u : C3,
    hammingNorm (f3 u : Fin 3 → HilbertPhase (K 1)) =
      hammingNorm (u : Fin 3 → HilbertPhase (K 1)) := by
  intro u
  obtain ⟨p, hp⟩ := u.property
  have hu : u = ⟨c3Hom p, AddMonoidHom.mem_range.mpr ⟨p, rfl⟩⟩ := by
    exact Subtype.ext hp.symm
  subst u
  rw [f3_on]
  rcases p with ⟨a, b⟩
  rcases binary a with rfl | rfl
  · rcases binary b with rfl | rfl
    · simp [hammingNorm, c3Hom, d3Hom, CharTwo.add_self_eq_zero]
    · have hc : hammingNorm (c3Hom (0, 1)) = 2 := by
        apply wt3_two_01
        · simp [c3Hom, omega_ne_zero]
        · simp [c3Hom, omega_ne_zero]
        · simp [c3Hom]
      have hd : hammingNorm (d3Hom (0, 1)) = 2 := by
        apply wt3_two_02
        · simp [d3Hom]
        · simp [d3Hom]
        · simp [d3Hom]
      exact hd.trans hc.symm
  · rcases binary b with rfl | rfl
    · have hc : hammingNorm (c3Hom (1, 0)) = 2 := by
        apply wt3_two_01
        · simp [c3Hom]
        · simp [c3Hom]
        · simp [c3Hom]
      have hd : hammingNorm (d3Hom (1, 0)) = 2 := by
        apply wt3_two_01
        · simp [d3Hom]
        · simp [d3Hom]
        · simp [d3Hom]
      exact hd.trans hc.symm
    · have hc : hammingNorm (c3Hom (1, 1)) = 2 := by
        apply wt3_two_01
        · simp [c3Hom]
        · simp [c3Hom]
        · simp [c3Hom]
      have hd : hammingNorm (d3Hom (1, 1)) = 2 := by
        apply wt3_two_12
        · simp [d3Hom, CharTwo.add_self_eq_zero]
        · simp [d3Hom]
        · simp [d3Hom]
      exact hd.trans hc.symm

def qepWitness {n : ℕ} {C D : AddSubgroup (Fin n → HilbertPhase (K 1))} (f : C ≃+ D)
    (π : Equiv.Perm (Fin n)) (τ : Fin n → Matrix (Fin 2) (Fin 2) (K 1)) : Prop :=
  (∀ i, (τ i).det = 1) ∧ ∀ u : C, ∀ i,
    (f u : Fin n → HilbertPhase (K 1)) i = (τ i) • ((u : Fin n → HilbertPhase (K 1)) (π.symm i))

def QEP (n : ℕ) : Prop :=
  ∀ (C D : AddSubgroup (Fin n → HilbertPhase (K 1))), selfOrthogonal C → selfOrthogonal D →
    ∀ f : C ≃+ D,
      (∀ u : C, hammingNorm (f u : Fin n → HilbertPhase (K 1)) =
        hammingNorm (u : Fin n → HilbertPhase (K 1))) →
      ∃ π : Equiv.Perm (Fin n), ∃ τ : Fin n → Matrix (Fin 2) (Fin 2) (K 1),
        qepWitness f π τ

def QEPAdd (n : ℕ) : Prop :=
  ∀ (C D : AddSubgroup (Fin n → HilbertPhase (K 1))), selfOrthogonal C → selfOrthogonal D →
    ∀ f : C ≃+ D,
      (∀ u : C, hammingNorm (f u : Fin n → HilbertPhase (K 1)) =
        hammingNorm (u : Fin n → HilbertPhase (K 1))) →
      ∃ π : Equiv.Perm (Fin n), ∃ τ : Fin n → (HilbertPhase (K 1) ≃+ HilbertPhase (K 1)),
        (∀ u : C, ∀ i,
          (f u : Fin n → HilbertPhase (K 1)) i = τ i ((u : Fin n → HilbertPhase (K 1)) (π.symm i)))

def claim : Prop :=
  IsLeast {n : ℕ | 1 ≤ n ∧ ¬ QEP n} 5 ∨
    IsLeast {n : ℕ | 1 ≤ n ∧ ¬ QEPAdd n} 5

private lemma not_qep_one : ¬ QEP 1 := by
  intro h
  obtain ⟨π, τ, hτ, hact⟩ :=
    h C1 D1 selfOrthogonal_C1 selfOrthogonal_D1 f1 f1_weight
  have hπ : π.symm 0 = 0 := Subsingleton.elim _ _
  let p0 : Pair := (1, 0)
  let pω : Pair := (0, 1)
  have h0 := hact
    (⟨c1Hom p0, AddMonoidHom.mem_range.mpr ⟨p0, rfl⟩⟩ : C1) 0
  have hω := hact
    (⟨c1Hom pω, AddMonoidHom.mem_range.mpr ⟨pω, rfl⟩⟩ : C1) 0
  simp only [f1_on] at h0 hω
  have h0' : (d1Hom p0 : Fin 1 → HilbertPhase (K 1)) 0 = (τ 0) • ((c1Hom p0 : Fin 1 → HilbertPhase (K 1)) 0) := by
    simpa [hπ] using h0
  have hω' : (d1Hom pω : Fin 1 → HilbertPhase (K 1)) 0 = (τ 0) • ((c1Hom pω : Fin 1 → HilbertPhase (K 1)) 0) := by
    simpa [hπ] using hω
  have hτ10 : τ 0 1 0 = 0 := by
    have hs := congrArg Prod.snd h0'
    have hs' := hs
    simp [Matrix.fin_two_smul_prod, c1Hom, d1Hom, p0] at hs'
    change (0 : K 1) = τ 0 1 0 at hs'
    exact hs'.symm
  have hsω := congrArg Prod.snd hω'
  simp [Matrix.fin_two_smul_prod, c1Hom, d1Hom, pω] at hsω
  change (1 : K 1) = τ 0 1 0 * omega at hsω
  rw [hτ10] at hsω
  simp at hsω

private lemma not_qepAdd_three : ¬ QEPAdd 3 := by
  intro h
  obtain ⟨π, τ, hact⟩ :=
    h C3 D3 selfOrthogonal_C3 selfOrthogonal_D3 f3 f3_weight
  let j : Fin 3 := π 2
  have hj : π.symm j = 2 := by
    exact π.symm_apply_apply 2
  have hzero : ∀ u : C3, (f3 u : Fin 3 → HilbertPhase (K 1)) j = 0 := by
    intro u
    obtain ⟨p, hp⟩ := u.property
    have hu : u = ⟨c3Hom p, AddMonoidHom.mem_range.mpr ⟨p, rfl⟩⟩ := by
      exact Subtype.ext hp.symm
    subst u
    have hh := hact
      (⟨c3Hom p, AddMonoidHom.mem_range.mpr ⟨p, rfl⟩⟩ : C3) j
    rw [hj] at hh
    change (f3 ⟨c3Hom p, AddMonoidHom.mem_range.mpr ⟨p, rfl⟩⟩ : Fin 3 → HilbertPhase (K 1)) j =
      (τ j) (c3Hom p 2) at hh
    have hcp : c3Hom p 2 = (0, 0) := by simp [c3Hom]
    rw [hcp] at hh
    have hτzero : τ j (0, 0) = 0 := by
      simpa using (map_zero (τ j))
    rw [hτzero] at hh
    exact hh
  have hD : ∀ k : Fin 3, ∃ y : D3, (y : Fin 3 → HilbertPhase (K 1)) k ≠ 0 := by
    intro k
    fin_cases k
    · refine ⟨⟨d3Hom (1, 0), AddMonoidHom.mem_range.mpr ⟨(1, 0), rfl⟩⟩, ?_⟩
      simp [d3Hom]
    · refine ⟨⟨d3Hom (1, 0), AddMonoidHom.mem_range.mpr ⟨(1, 0), rfl⟩⟩, ?_⟩
      simp [d3Hom]
    · refine ⟨⟨d3Hom (0, 1), AddMonoidHom.mem_range.mpr ⟨(0, 1), rfl⟩⟩, ?_⟩
      simp [d3Hom]
  obtain ⟨y, hy⟩ := hD j
  obtain ⟨u, hu⟩ := f3.surjective y
  apply hy
  rw [← hu]
  exact hzero u

theorem result : ¬ claim := by
  intro h
  rcases h with h | h
  · have hmem : 1 ∈ {n : ℕ | 1 ≤ n ∧ ¬ QEP n} := by simp [not_qep_one]
    have hle := h.2 hmem
    omega
  · have hmem : 3 ∈ {n : ℕ | 1 ≤ n ∧ ¬ QEPAdd n} := by simp [not_qepAdd_three]
    have hle := h.2 hmem
    omega

end D5.S3.Quantum.Codes.StabilizerExtensionQuaternaryMinimalLength
