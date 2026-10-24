/- GID: D5/S3/Quantum/Codes/StabilizerExtensionQuaternaryMinimalLength
   generality: I
   mirror-B: D5/B/S3/Quantum/Codes/StabilizerExtensionQuaternaryMinimalLength
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Codes/StabilizerExtensionQuaternaryMinimalLength.claim; result=D5/S3/Quantum/Codes/StabilizerExtensionQuaternaryMinimalLength.result; claim=D5/S3/Quantum/Codes/StabilizerExtensionQuaternaryMinimalLength.claim
   digest: Explicit quaternary additive-code counterexamples refute the length-five expectation. -/

import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Tactic

noncomputable section

namespace D5.S3.Quantum.Codes.StabilizerExtensionQuaternaryMinimalLength

set_option autoImplicit false
set_option relaxedAutoImplicit false

abbrev F4 := GaloisField 2 2
abbrev A := F4 × F4

noncomputable instance : Fintype F4 := Fintype.ofFinite F4
noncomputable instance : DecidableEq F4 := Classical.decEq F4

private lemma card_F4 : Fintype.card F4 = 4 := by
  simpa [Nat.card_eq_fintype_card] using
    (GaloisField.card 2 2 (by decide : (2 : ℕ) ≠ 0))

private lemma exists_nonbase : ∃ x : F4, x ≠ 0 ∧ x ≠ 1 := by
  by_contra hn
  have hall : ∀ x : F4, x = 0 ∨ x = 1 := by
    intro x
    by_contra hx
    push_neg at hx
    exact hn ⟨x, hx.1, hx.2⟩
  let g : F4 → Bool := fun x => if x = 0 then false else true
  have hg : Function.Injective g := by
    intro x y hxy
    by_cases hx : x = 0
    · subst x
      by_cases hy : y = 0
      · exact hy.symm
      · exfalso
        have hne : g (0 : F4) ≠ g y := by simp [g, hy]
        exact hne hxy
    · by_cases hy : y = 0
      · subst y
        exfalso
        have hne : g x ≠ g (0 : F4) := by simp [g, hx]
        exact hne hxy
      · exact (hall x).resolve_left hx |>.trans ((hall y).resolve_left hy).symm
  have hc : Fintype.card F4 ≤ Fintype.card Bool :=
    Fintype.card_le_of_injective g hg
  rw [card_F4] at hc
  norm_num at hc

private noncomputable def omega : F4 := Classical.choose exists_nonbase

private lemma omega_ne_zero : omega ≠ 0 := (Classical.choose_spec exists_nonbase).1
private lemma omega_ne_one : omega ≠ 1 := (Classical.choose_spec exists_nonbase).2

private lemma root_four (x : F4) : x ^ 4 = x := by
  simpa [card_F4] using (FiniteField.pow_card x)

private lemma omega_sq : omega ^ 2 = omega + 1 := by
  have h4 : omega ^ 4 = omega := root_four omega
  have h3 : omega ^ 3 = 1 := by
    apply (mul_right_cancel₀ omega_ne_zero)
    simpa [pow_succ, pow_two, mul_assoc] using h4
  have h2 : (2 : F4) = 0 := by exact CharP.cast_eq_zero F4 2
  have hadd (x : F4) : x + x = 0 := by
    have hh := congrArg (fun z : F4 => x * z) h2
    simpa [mul_two] using hh
  have hmul2 (x : F4) : x * 2 = 0 := by
    have hh := congrArg (fun z : F4 => x * z) h2
    simpa using hh
  have hfactor : (omega + 1) * (omega ^ 2 + omega + 1) = 0 := by
    calc
      (omega + 1) * (omega ^ 2 + omega + 1) = omega ^ 3 + 1 := by
        ring_nf
        rw [hmul2 omega, hmul2 (omega ^ 2)]
        simp
      _ = 0 := by rw [h3]; simpa [← two_mul] using h2
  have hplus : omega + 1 ≠ 0 := by
    intro h
    apply omega_ne_one
    have hnegone : (-1 : F4) = 1 := by
      have hh : (1 : F4) + 1 = 0 := by simpa [← two_mul] using h2
      exact (add_eq_zero_iff_eq_neg.mp hh).symm
    simpa [hnegone] using (add_eq_zero_iff_eq_neg.mp h)
  have hquad : omega ^ 2 + omega + 1 = 0 :=
    (mul_eq_zero.mp hfactor).resolve_left hplus
  have hself (x : F4) : -x = x := by
    apply neg_eq_iff_add_eq_zero.mpr
    have hh := congrArg (fun z : F4 => x * z) h2
    simpa [mul_two] using hh
  have hquad' : omega ^ 2 - (omega + 1) = 0 := by
    simpa [sub_eq_add_neg, hself, add_assoc] using hquad
  exact sub_eq_zero.mp hquad'

private lemma omega_add_one_ne_zero : omega + 1 ≠ 0 := by
  intro h
  apply omega_ne_one
  have h2 : (2 : F4) = 0 := by exact CharP.cast_eq_zero F4 2
  have hnegone : (-1 : F4) = 1 := by
    have hh : (1 : F4) + 1 = 0 := by simpa [← two_mul] using h2
    exact (add_eq_zero_iff_eq_neg.mp hh).symm
  simpa [hnegone] using (add_eq_zero_iff_eq_neg.mp h)

private lemma add_self_F4 (x : F4) : x + x = 0 := by
  have h2 : (2 : F4) = 0 := CharP.cast_eq_zero F4 2
  simpa [← two_mul] using congrArg (fun z : F4 => z * x) h2

private lemma one_add_omega_ne_zero : 1 + omega ≠ 0 := by
  simpa [add_comm] using omega_add_one_ne_zero

def tr (x : F4) : F4 := x + x ^ 2

def symp {n : ℕ} (u v : Fin n → A) : F4 :=
  tr (∑ i, ((u i).1 * (v i).2 - (v i).1 * (u i).2))

def wt {n : ℕ} (u : Fin n → A) : ℕ :=
  (Finset.univ.filter (fun i => u i ≠ 0)).card

private lemma wt3_two_01 {u : Fin 3 → A} (h0 : u 0 ≠ 0) (h1 : u 1 ≠ 0)
    (h2 : u 2 = 0) : wt u = 2 := by
  have hp (i : Fin 3) : (u i ≠ 0) ↔ (i = 0 ∨ i = 1) := by
    fin_cases i <;> simp [h0, h1, h2]
  rw [wt, Finset.filter_congr (by intro i hi; exact hp i)]
  decide

private lemma wt3_two_02 {u : Fin 3 → A} (h0 : u 0 ≠ 0) (h1 : u 1 = 0)
    (h2 : u 2 ≠ 0) : wt u = 2 := by
  have hp (i : Fin 3) : (u i ≠ 0) ↔ (i = 0 ∨ i = 2) := by
    fin_cases i <;> simp [h0, h1, h2]
  rw [wt, Finset.filter_congr (by intro i hi; exact hp i)]
  decide

private lemma wt3_two_12 {u : Fin 3 → A} (h0 : u 0 = 0) (h1 : u 1 ≠ 0)
    (h2 : u 2 ≠ 0) : wt u = 2 := by
  have hp (i : Fin 3) : (u i ≠ 0) ↔ (i = 1 ∨ i = 2) := by
    fin_cases i <;> simp [h0, h1, h2]
  rw [wt, Finset.filter_congr (by intro i hi; exact hp i)]
  decide

def selfOrthogonal {n : ℕ} (C : AddSubgroup (Fin n → A)) : Prop :=
  ∀ u ∈ C, ∀ v ∈ C, symp u v = 0

private def labelVec (x : A) : Fin 2 → F4 := ![x.1, x.2]

def act (τ : Matrix (Fin 2) (Fin 2) F4) (x : A) : A :=
  ((Matrix.mulVec τ (labelVec x)) 0, (Matrix.mulVec τ (labelVec x)) 1)

private abbrev P := ZMod 2 × ZMod 2

private def f2 (a : ZMod 2) : F4 := algebraMap (ZMod 2) F4 a

@[simp] private lemma f2_zero : f2 0 = 0 := by simp [f2]
@[simp] private lemma f2_one : f2 1 = 1 := by simp [f2]

private lemma zmod2_cases (x : ZMod 2) : x = 0 ∨ x = 1 := by
  cases x with
  | mk v hv =>
    interval_cases v
    · left
      rfl
    · right
      rfl

private noncomputable def rangeEquiv {V W : Type*} [AddCommGroup V] [AddCommGroup W]
    (g : P →+ V) (h : P →+ W) (hg : Function.Injective g) (hh : Function.Injective h) :
    g.range ≃+ h.range :=
  (g.ofInjective hg).symm.trans (h.ofInjective hh)

private lemma rangeEquiv_apply {V W : Type*} [AddCommGroup V] [AddCommGroup W]
    (g : P →+ V) (h : P →+ W) (hg : Function.Injective g) (hh : Function.Injective h)
    (p : P) : rangeEquiv g h hg hh
      ⟨g p, AddMonoidHom.mem_range.mpr ⟨p, rfl⟩⟩ =
      ⟨h p, AddMonoidHom.mem_range.mpr ⟨p, rfl⟩⟩ := by
  apply Subtype.ext
  change h ((g.ofInjective hg).symm
      ⟨g p, AddMonoidHom.mem_range.mpr ⟨p, rfl⟩⟩) = h p
  exact congrArg h ((g.ofInjective hg).symm_apply_apply p)

private def c1Hom : P →+ (Fin 1 → A) :=
  { toFun := fun p => fun _ => (f2 p.1 + f2 p.2 * omega, 0)
    map_zero' := by ext i <;> simp [f2]
    map_add' := by
      intro p q
      funext i
      simp [f2, add_mul, add_assoc, add_left_comm, add_comm] }

private def d1Hom : P →+ (Fin 1 → A) :=
  { toFun := fun p => fun _ => (f2 p.1, f2 p.2)
    map_zero' := by ext i <;> simp [f2]
    map_add' := by intro p q; funext i; simp [f2] }

private lemma c1Hom_injective : Function.Injective c1Hom := by
  intro p q h
  rcases p with ⟨a, b⟩
  rcases q with ⟨c, d⟩
  have h0 := congrFun h 0
  change (f2 a + f2 b * omega, 0) = (f2 c + f2 d * omega, 0) at h0
  rcases zmod2_cases a with rfl | rfl <;>
    rcases zmod2_cases b with rfl | rfl <;>
        rcases zmod2_cases c with rfl | rfl <;>
        rcases zmod2_cases d with rfl | rfl <;>
          simp_all [f2, omega_ne_zero, omega_ne_one,
            omega_add_one_ne_zero] <;>
            first
            | exact omega_ne_zero h0.symm
            | exact one_add_omega_ne_zero h0.symm
            | exact omega_ne_one h0.symm
            | exact one_add_omega_ne_zero h0

private lemma d1Hom_injective : Function.Injective d1Hom := by
  intro p q h
  rcases p with ⟨a, b⟩
  rcases q with ⟨c, d⟩
  have h0 := congrFun h 0
  exact Prod.ext (by simpa [d1Hom, f2] using congrArg Prod.fst h0)
    (by simpa [d1Hom, f2] using congrArg Prod.snd h0)

private def c3Hom : P →+ (Fin 3 → A) :=
  { toFun := fun p => ![
      (f2 p.1, f2 p.2 * omega),
      (f2 p.1, f2 p.2 * omega),
      (0, 0)]
    map_zero' := by funext i; fin_cases i <;> simp [f2]
    map_add' := by
      intro p q
      funext i
      fin_cases i <;> simp [f2, add_mul, add_assoc, add_left_comm, add_comm] }

private def d3Hom : P →+ (Fin 3 → A) :=
  { toFun := fun p => ![
      (f2 (p.1 + p.2), 0),
      (f2 p.1, 0),
      (f2 p.2, 0)]
    map_zero' := by funext i; fin_cases i <;> simp [f2]
    map_add' := by
      intro p q
      funext i
      fin_cases i <;> simp [f2, add_assoc, add_left_comm, add_comm] }

private lemma c3Hom_injective : Function.Injective c3Hom := by
  intro p q h
  rcases p with ⟨a, b⟩
  rcases q with ⟨c, d⟩
  have h0 := congrFun h 0
  change (f2 a, f2 b * omega) = (f2 c, f2 d * omega) at h0
  rcases zmod2_cases a with rfl | rfl <;>
    rcases zmod2_cases b with rfl | rfl <;>
      rcases zmod2_cases c with rfl | rfl <;>
        rcases zmod2_cases d with rfl | rfl <;>
          simp_all [f2, omega_ne_zero]
          <;> exact omega_ne_zero h0.symm

private lemma d3Hom_injective : Function.Injective d3Hom := by
  intro p q h
  rcases p with ⟨a, b⟩
  rcases q with ⟨c, d⟩
  have h1 := congrFun h 1
  have h2 := congrFun h 2
  exact Prod.ext (by simpa [d3Hom, f2] using congrArg Prod.fst h1)
    (by simpa [d3Hom, f2] using congrArg Prod.fst h2)

private abbrev C1 : AddSubgroup (Fin 1 → A) := c1Hom.range
private abbrev D1 : AddSubgroup (Fin 1 → A) := d1Hom.range
private abbrev C3 : AddSubgroup (Fin 3 → A) := c3Hom.range
private abbrev D3 : AddSubgroup (Fin 3 → A) := d3Hom.range

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
  simp [symp, tr, c1Hom, Fin.sum_univ_succ, add_self_F4]

private lemma selfOrthogonal_D1 : selfOrthogonal D1 := by
  intro u hu v hv
  obtain ⟨p, hp⟩ := hu
  obtain ⟨q, hq⟩ := hv
  subst u
  subst v
  rcases p with ⟨a, b⟩
  rcases q with ⟨c, d⟩
  rcases zmod2_cases a with rfl | rfl <;>
    rcases zmod2_cases b with rfl | rfl <;>
      rcases zmod2_cases c with rfl | rfl <;>
        rcases zmod2_cases d with rfl | rfl <;>
          simp [symp, tr, d1Hom, f2, Fin.sum_univ_succ, add_self_F4]

private lemma f1_on (p : P) :
    f1 ⟨c1Hom p, AddMonoidHom.mem_range.mpr ⟨p, rfl⟩⟩ =
      ⟨d1Hom p, AddMonoidHom.mem_range.mpr ⟨p, rfl⟩⟩ := by
  exact rangeEquiv_apply c1Hom d1Hom c1Hom_injective d1Hom_injective p

private lemma f1_weight : ∀ u : C1,
    wt (f1 u : Fin 1 → A) = wt (u : Fin 1 → A) := by
  intro u
  obtain ⟨p, hp⟩ := u.property
  have hu : u = ⟨c1Hom p, AddMonoidHom.mem_range.mpr ⟨p, rfl⟩⟩ := by
    exact Subtype.ext hp.symm
  subst u
  rw [f1_on]
  rcases p with ⟨a, b⟩
  rcases zmod2_cases a with rfl | rfl <;>
    rcases zmod2_cases b with rfl | rfl <;>
      simp [wt, c1Hom, d1Hom, f2, omega_ne_zero, omega_ne_one,
        omega_add_one_ne_zero, one_add_omega_ne_zero]

private lemma selfOrthogonal_C3 : selfOrthogonal C3 := by
  intro u hu v hv
  obtain ⟨p, hp⟩ := hu
  obtain ⟨q, hq⟩ := hv
  subst u
  subst v
  simp [symp, tr, c3Hom, Fin.sum_univ_succ, sub_eq_add_neg, add_self_F4]

private lemma selfOrthogonal_D3 : selfOrthogonal D3 := by
  intro u hu v hv
  obtain ⟨p, hp⟩ := hu
  obtain ⟨q, hq⟩ := hv
  subst u
  subst v
  simp [symp, tr, d3Hom, Fin.sum_univ_succ]

private lemma f3_on (p : P) :
    f3 ⟨c3Hom p, AddMonoidHom.mem_range.mpr ⟨p, rfl⟩⟩ =
      ⟨d3Hom p, AddMonoidHom.mem_range.mpr ⟨p, rfl⟩⟩ := by
  exact rangeEquiv_apply c3Hom d3Hom c3Hom_injective d3Hom_injective p

private lemma f3_weight : ∀ u : C3,
    wt (f3 u : Fin 3 → A) = wt (u : Fin 3 → A) := by
  intro u
  obtain ⟨p, hp⟩ := u.property
  have hu : u = ⟨c3Hom p, AddMonoidHom.mem_range.mpr ⟨p, rfl⟩⟩ := by
    exact Subtype.ext hp.symm
  subst u
  rw [f3_on]
  rcases p with ⟨a, b⟩
  rcases zmod2_cases a with rfl | rfl
  · rcases zmod2_cases b with rfl | rfl
    · simp [wt, c3Hom, d3Hom, f2, add_self_F4]
    · have hc : wt (c3Hom (0, 1)) = 2 := by
        apply wt3_two_01
        · simp [c3Hom, f2, omega_ne_zero]
        · simp [c3Hom, f2, omega_ne_zero]
        · simp [c3Hom]
      have hd : wt (d3Hom (0, 1)) = 2 := by
        apply wt3_two_02
        · simp [d3Hom, f2]
        · simp [d3Hom]
        · simp [d3Hom, f2]
      exact hd.trans hc.symm
  · rcases zmod2_cases b with rfl | rfl
    · have hc : wt (c3Hom (1, 0)) = 2 := by
        apply wt3_two_01
        · simp [c3Hom, f2]
        · simp [c3Hom, f2]
        · simp [c3Hom]
      have hd : wt (d3Hom (1, 0)) = 2 := by
        apply wt3_two_01
        · simp [d3Hom, f2]
        · simp [d3Hom]
        · simp [d3Hom, f2]
      exact hd.trans hc.symm
    · have hc : wt (c3Hom (1, 1)) = 2 := by
        apply wt3_two_01
        · simp [c3Hom, f2]
        · simp [c3Hom, f2]
        · simp [c3Hom]
      have hd : wt (d3Hom (1, 1)) = 2 := by
        apply wt3_two_12
        · simp [d3Hom, f2, add_self_F4]
        · simp [d3Hom, f2]
        · simp [d3Hom, f2]
      exact hd.trans hc.symm

def qepWitness {n : ℕ} {C D : AddSubgroup (Fin n → A)} (f : C ≃+ D)
    (π : Equiv.Perm (Fin n)) (τ : Fin n → Matrix (Fin 2) (Fin 2) F4) : Prop :=
  (∀ i, (τ i).det = 1) ∧ ∀ u : C, ∀ i,
    (f u : Fin n → A) i = act (τ i) ((u : Fin n → A) (π.symm i))

def QEP (n : ℕ) : Prop :=
  ∀ (C D : AddSubgroup (Fin n → A)), selfOrthogonal C → selfOrthogonal D →
    ∀ f : C ≃+ D, (∀ u : C, wt (f u : Fin n → A) = wt (u : Fin n → A)) →
      ∃ π : Equiv.Perm (Fin n), ∃ τ : Fin n → Matrix (Fin 2) (Fin 2) F4,
        qepWitness f π τ

def QEPAdd (n : ℕ) : Prop :=
  ∀ (C D : AddSubgroup (Fin n → A)), selfOrthogonal C → selfOrthogonal D →
    ∀ f : C ≃+ D, (∀ u : C, wt (f u : Fin n → A) = wt (u : Fin n → A)) →
      ∃ π : Equiv.Perm (Fin n), ∃ τ : Fin n → (A ≃+ A),
        (∀ u : C, ∀ i,
          (f u : Fin n → A) i = τ i ((u : Fin n → A) (π.symm i)))

def claim : Prop :=
  IsLeast {n : ℕ | 1 ≤ n ∧ ¬ QEP n} 5 ∨
    IsLeast {n : ℕ | 1 ≤ n ∧ ¬ QEPAdd n} 5

private lemma not_qep_one : ¬ QEP 1 := by
  intro h
  obtain ⟨π, τ, hτ, hact⟩ :=
    h C1 D1 selfOrthogonal_C1 selfOrthogonal_D1 f1 f1_weight
  have hπ : π.symm 0 = 0 := Subsingleton.elim _ _
  let p0 : P := (1, 0)
  let pω : P := (0, 1)
  have h0 := hact
    (⟨c1Hom p0, AddMonoidHom.mem_range.mpr ⟨p0, rfl⟩⟩ : C1) 0
  have hω := hact
    (⟨c1Hom pω, AddMonoidHom.mem_range.mpr ⟨pω, rfl⟩⟩ : C1) 0
  simp only [f1_on] at h0 hω
  have h0' : (d1Hom p0 : Fin 1 → A) 0 = act (τ 0) ((c1Hom p0 : Fin 1 → A) 0) := by
    simpa [hπ] using h0
  have hω' : (d1Hom pω : Fin 1 → A) 0 = act (τ 0) ((c1Hom pω : Fin 1 → A) 0) := by
    simpa [hπ] using hω
  have hτ10 : τ 0 1 0 = 0 := by
    have hs := congrArg Prod.snd h0'
    have hs' := hs
    simp [act, labelVec, c1Hom, d1Hom, p0, Matrix.mulVec,
      Fin.sum_univ_two] at hs'
    change (0 : F4) = τ 0 1 0 at hs'
    exact hs'.symm
  have hsω := congrArg Prod.snd hω'
  simp [act, labelVec, c1Hom, d1Hom, pω, Matrix.mulVec,
    Fin.sum_univ_two] at hsω
  change (1 : F4) = τ 0 1 0 * omega at hsω
  rw [hτ10] at hsω
  simp at hsω

private lemma not_qepAdd_three : ¬ QEPAdd 3 := by
  intro h
  obtain ⟨π, τ, hact⟩ :=
    h C3 D3 selfOrthogonal_C3 selfOrthogonal_D3 f3 f3_weight
  let j : Fin 3 := π 2
  have hj : π.symm j = 2 := by
    exact π.symm_apply_apply 2
  have hzero : ∀ u : C3, (f3 u : Fin 3 → A) j = 0 := by
    intro u
    obtain ⟨p, hp⟩ := u.property
    have hu : u = ⟨c3Hom p, AddMonoidHom.mem_range.mpr ⟨p, rfl⟩⟩ := by
      exact Subtype.ext hp.symm
    subst u
    have hh := hact
      (⟨c3Hom p, AddMonoidHom.mem_range.mpr ⟨p, rfl⟩⟩ : C3) j
    rw [hj] at hh
    change (f3 ⟨c3Hom p, AddMonoidHom.mem_range.mpr ⟨p, rfl⟩⟩ : Fin 3 → A) j =
      (τ j) (c3Hom p 2) at hh
    have hcp : c3Hom p 2 = (0, 0) := by simp [c3Hom]
    rw [hcp] at hh
    have hτzero : τ j (0, 0) = 0 := by
      simpa using (map_zero (τ j))
    rw [hτzero] at hh
    exact hh
  have hD : ∀ k : Fin 3, ∃ y : D3, (y : Fin 3 → A) k ≠ 0 := by
    intro k
    fin_cases k
    · refine ⟨⟨d3Hom (1, 0), AddMonoidHom.mem_range.mpr ⟨(1, 0), rfl⟩⟩, ?_⟩
      simp [d3Hom, f2]
    · refine ⟨⟨d3Hom (1, 0), AddMonoidHom.mem_range.mpr ⟨(1, 0), rfl⟩⟩, ?_⟩
      simp [d3Hom, f2]
    · refine ⟨⟨d3Hom (0, 1), AddMonoidHom.mem_range.mpr ⟨(0, 1), rfl⟩⟩, ?_⟩
      simp [d3Hom, f2]
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
