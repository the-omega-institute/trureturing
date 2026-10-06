/- GID: D5/S3/FiniteGroups/NikolovSegal/TransitiveCoordinates
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/TransitiveCoordinates
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual minimal-period coordinates and simultaneous scalar corrections. -/

import D5.S3.FiniteGroups.NikolovSegal.TransitiveHall
import Mathlib.Combinatorics.Hall.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Sort
import Mathlib.Combinatorics.SimpleGraph.Acyclic

set_option autoImplicit false
namespace NikolovSegal
universe u

def qPowerGraph {I : Type u} [DecidableEq I] {m : ℕ}
    (σ : Fin m → Equiv.Perm I) (q : ℕ) : SimpleGraph I where
  Adj i k := i ≠ k ∧ ∃ j : Fin m,
    (σ j ^ q) i = k ∨ (σ j ^ q) k = i
  symm := ⟨fun i k h =>
    ⟨Ne.symm h.1, by
      obtain ⟨j, hj | hj⟩ := h.2
      · exact ⟨j, Or.inr hj⟩
      · exact ⟨j, Or.inl hj⟩⟩⟩
  loopless := ⟨fun i h => h.1 rfl⟩

theorem qPowerGraph_spanningForest
    {I : Type u} [Fintype I] [DecidableEq I] {m q : ℕ}
    (σ : Fin m → Equiv.Perm I) :
    ∃ F : SimpleGraph I, F ≤ qPowerGraph σ q ∧ F.IsAcyclic ∧
      F.Reachable = (qPowerGraph σ q).Reachable := by
  exact (qPowerGraph σ q).exists_isAcyclic_reachable_eq_le

theorem qPowerForestEdgeLabel
    {I : Type u} [DecidableEq I] {m q : ℕ}
    (σ : Fin m → Equiv.Perm I) {F : SimpleGraph I}
    (hF : F ≤ qPowerGraph σ q) {i k : I} (h : F.Adj i k) :
    ∃ j : Fin m, (σ j ^ q) i = k ∨ (σ j ^ q) k = i := by
  exact (hF h).2

def PartIIScalarProductInput {S : Type u} [Group S]
    (q M : ℕ) (β : Fin M → MulAut S) (e : Fin M → ℕ) : Prop :=
  (∀ j, 0 < e j ∧ e j ∣ q) →
    ∃ x : Fin M → S, ∀ t : S, ∃ c : Fin M → S,
      orderedProduct (fun j => (c j)⁻¹ *
        ((β j * MulAut.conj (x j)⁻¹) ^ (q / e j)) (c j)) = t

private theorem step_formula {S I : Type u} [Group S]
    {m : ℕ} (k : Fin m → MulAut (I → S)) (σ : Fin m → Equiv.Perm I)
    (β : Fin m → I → MulAut S)
    (hcoord : ∀ j z o, k j z (σ j o) = β j o (z o))
    (j : Fin m) (y z : I → S) (o : I) :
    (k j * MulAut.conj y⁻¹) z (σ j o) =
      β j o (y o)⁻¹ * β j o (z o) * β j o (y o) := by
  simp only [MulAut.mul_apply]
  rw [hcoord]
  simp [map_inv, map_mul, Pi.mul_apply]

private theorem path_same {S I : Type u} [Group S] [DecidableEq I]
    {m : ℕ} (k : Fin m → MulAut (I → S)) (σ : Fin m → Equiv.Perm I)
    (β : Fin m → I → MulAut S)
    (hcoord : ∀ j z o, k j z (σ j o) = β j o (z o))
    (j : Fin m) (y : I → S) (n : ℕ) (a : I)
    (hy : ∀ r < n, y ((σ j)^[r] a) = 1)
    (u v : I → S) (huv : u a = v a) :
    ((k j * MulAut.conj y⁻¹) ^ n) u ((σ j)^[n] a) =
      (k j ^ n) v ((σ j)^[n] a) := by
  induction n generalizing a u v with
  | zero => simpa using huv
  | succ n ih =>
    rw [pow_succ, pow_succ]
    change ((k j * MulAut.conj y⁻¹) ^ n)
      ((k j * MulAut.conj y⁻¹) u) ((σ j)^[n] ((σ j) a)) =
      (k j ^ n) (k j v) ((σ j)^[n] ((σ j) a))
    apply ih (a := (σ j) a)
    · intro r hr
      rw [← Function.iterate_succ_apply]
      exact hy (r + 1) (by omega)
    · simp only [step_formula k σ β hcoord]
      rw [huv]
      have hya : y a = 1 := by simpa using hy 0 (by omega)
      simp [hya]
      exact (hcoord j v a).symm

private noncomputable def factorCorrection {S R I : Type u} [Group S]
    [Fintype R] [DecidableEq R] [DecidableEq I]
    {m : ℕ} (rep : R → I) (sel : R → Finset (Fin m))
    (x : R → Fin m → S) (j : Fin m) (i : I) : S :=
  if h : ∃ r, j ∈ sel r ∧ i = rep r then x (Classical.choose h) j else 1

private theorem factorCorrection_at {S R I : Type u} [Group S]
    [Fintype R] [DecidableEq R] [DecidableEq I]
    {m : ℕ} (rep : R → I) (hinj : Function.Injective rep)
    (sel : R → Finset (Fin m)) (x : R → Fin m → S)
    (j : Fin m) (r : R) (hsel : j ∈ sel r) :
    factorCorrection rep sel x j (rep r) = x r j := by
  classical
  by_cases h : ∃ r', j ∈ sel r' ∧ rep r = rep r'
  · simp [factorCorrection, h]
    have hc := Classical.choose_spec h
    have heq : Classical.choose h = r := (hinj hc.2).symm
    rw [heq]
  · simp [factorCorrection, h]
    exact (h ⟨r, hsel, rfl⟩).elim

private theorem factorCorrection_eq_one {S R I : Type u} [Group S]
    [Fintype R] [DecidableEq R] [DecidableEq I]
    {m : ℕ} (rep : R → I) (sel : R → Finset (Fin m)) (x : R → Fin m → S)
    (j : Fin m) (i : I)
    (hnone : ∀ r, j ∈ sel r → rep r ≠ i) :
    factorCorrection rep sel x j i = 1 := by
  classical
  by_cases h : ∃ r, j ∈ sel r ∧ i = rep r
  · simp [factorCorrection, h]
    obtain ⟨r, hr, hir⟩ := h
    exact (hnone r hr hir.symm).elim
  · simp [factorCorrection, h]

private theorem periodicity_of_pow_fix {I : Type u}
    (σ : Equiv.Perm I) (e : ℕ) (i : I) (h : (σ ^ e) i = i) :
    Function.IsPeriodicPt σ e i := by
  have hp : ∀ n : ℕ, ∀ x : I, (σ ^ n) x = (σ^[n]) x := by
    intro n
    induction n with
    | zero => intro x; simp
    | succ n ih =>
      intro x
      rw [pow_succ]
      change (σ ^ n) (σ x) = _
      rw [ih]
      exact (Function.iterate_succ_apply σ n x).symm
  change (σ^[e]) i = i
  exact (hp e i).symm.trans h

def cycleComponent {S I : Type u} [Group S]
    {m : ℕ} (β : Fin m → I → MulAut S) (σ : Fin m → Equiv.Perm I)
    (j : Fin m) (i : I) : ℕ → MulAut S
  | 0 => 1
  | n + 1 => β j ((σ j)^[n] i) * cycleComponent β σ j i n

theorem actual_cycle_component_action
    {S I : Type u} [Group S] {m : ℕ}
    (k : Fin m → MulAut (I → S)) (σ : Fin m → Equiv.Perm I)
    (β : Fin m → I → MulAut S)
    (hcoord : ∀ j z i, k j z (σ j i) = β j i (z i))
    (j : Fin m) (i : I) (n : ℕ) (z : I → S) :
    (k j ^ n) z ((σ j)^[n] i) =
      (cycleComponent β σ j i n) (z i) := by
  induction n with
  | zero => simp [cycleComponent]
  | succ n ih =>
    rw [pow_succ']
    simp only [MulAut.mul_apply]
    rw [Function.iterate_succ_apply']
    change k j ((k j ^ n) z) ((σ j) ((σ j)^[n] i)) =
      (cycleComponent β σ j i (n + 1)) (z i)
    rw [hcoord]
    rw [ih]
    rfl

def correctedCycleComponent {S I : Type u} [Group S]
    {m : ℕ} (β : Fin m → I → MulAut S) (σ : Fin m → Equiv.Perm I)
    (y : Fin m → I → S) (j : Fin m) (i : I) : ℕ → MulAut S
  | 0 => 1
  | n + 1 =>
      (β j ((σ j)^[n] i) *
        MulAut.conj (y j ((σ j)^[n] i))⁻¹) *
        correctedCycleComponent β σ y j i n

theorem actual_corrected_cycle_component_action
    {S I : Type u} [Group S] {m : ℕ}
    (k : Fin m → MulAut (I → S)) (σ : Fin m → Equiv.Perm I)
    (β : Fin m → I → MulAut S)
    (hcoord : ∀ j z i, k j z (σ j i) = β j i (z i))
    (y : Fin m → I → S) (j : Fin m) (i : I) (n : ℕ) (z : I → S) :
    ((k j * MulAut.conj (y j)⁻¹) ^ n) z ((σ j)^[n] i) =
      (correctedCycleComponent β σ y j i n) (z i) := by
  induction n with
  | zero => simp [correctedCycleComponent]
  | succ n ih =>
    rw [pow_succ']
    simp only [MulAut.mul_apply]
    rw [Function.iterate_succ_apply']
    change (k j * MulAut.conj (y j)⁻¹)
        (((k j * MulAut.conj (y j)⁻¹) ^ n) z)
        ((σ j) ((σ j)^[n] i)) =
      (correctedCycleComponent β σ y j i (n + 1)) (z i)
    rw [step_formula k σ β hcoord j (y j)
      (((k j * MulAut.conj (y j)⁻¹) ^ n) z) ((σ j)^[n] i)]
    rw [ih]
    simp [correctedCycleComponent, MulAut.mul_apply, map_inv, map_mul,
      mul_assoc]

theorem actual_corrected_q_power_coordinate
    {S I : Type u} [Group S] {m : ℕ}
    (k : Fin m → MulAut (I → S)) (σ : Fin m → Equiv.Perm I)
    (β : Fin m → I → MulAut S)
    (hcoord : ∀ j z i, k j z (σ j i) = β j i (z i))
    (y : Fin m → I → S) (j : Fin m) (i : I) (q : ℕ) (z : I → S) :
    ((k j * MulAut.conj (y j)⁻¹) ^ q) z ((σ j ^ q) i) =
      (correctedCycleComponent β σ y j i q) (z i) := by
  have hpow : (σ j ^ q) i = (σ j)^[q] i := by
    simpa only [Equiv.Perm.coe_pow]
  rw [hpow]
  exact actual_corrected_cycle_component_action k σ β hcoord y j i q z

theorem actual_cycle_component_at_return
    {S I : Type u} [Group S] {m : ℕ}
    (k : Fin m → MulAut (I → S)) (σ : Fin m → Equiv.Perm I)
    (β : Fin m → I → MulAut S)
    (hcoord : ∀ j z i, k j z (σ j i) = β j i (z i))
    (j : Fin m) (i : I) (e : ℕ) (hreturn : (σ j ^ e) i = i) :
    ∀ z, (k j ^ e) z i = (cycleComponent β σ j i e) (z i) := by
  intro z
  have hp : ∀ n : ℕ, ∀ x : I, ((σ j) ^ n) x = ((σ j)^[n]) x := by
    intro n
    induction n with
    | zero => intro x; simp
    | succ n ih =>
      intro x
      rw [pow_succ]
      change ((σ j) ^ n) ((σ j) x) = _
      rw [ih]
      exact (Function.iterate_succ_apply (σ j) n x).symm
  have hret : (σ j)^[e] i = i := (hp e i).symm.trans hreturn
  have h := actual_cycle_component_action k σ β hcoord j i e z
  rw [hret] at h
  exact h

theorem actual_factor_tuple_corrections
    {S R I : Type u} [Group S] [Fintype R] [Fintype I]
    [DecidableEq R] [DecidableEq I]
    {m : ℕ}
    (k : Fin m → MulAut (I → S)) (σ : Fin m → Equiv.Perm I)
    (β : Fin m → I → MulAut S)
    (hcoord : ∀ j z i, k j z (σ j i) = β j i (z i))
    (rep : R → I) (hinjrep : Function.Injective rep)
    (sel : R → Finset (Fin m)) (x : R → Fin m → S)
    (e : R → Fin m → ℕ) (γ : R → Fin m → MulAut S)
    (hsel : ∀ r j, j ∈ sel r → 0 < e r j)
    (hreturn : ∀ r j, j ∈ sel r → (σ j ^ e r j) (rep r) = rep r)
    (hcomponent : ∀ r j, j ∈ sel r → ∀ z,
      (k j ^ e r j) z (rep r) = γ r j (z (rep r)))
    (hminimal : ∀ r j, j ∈ sel r → ∀ n, 0 < n → n < e r j →
      (σ j)^[n] (rep r) ≠ rep r)
    (hind : ∀ r r' j, r ≠ r' → j ∈ sel r → j ∈ sel r' →
      (Function.periodicOrbit (σ j) (rep r)).toFinset ≠
        (Function.periodicOrbit (σ j) (rep r')).toFinset) :
    ∃ y : Fin m → (I → S), ∀ r j, j ∈ sel r → ∀ z,
      ((k j * MulAut.conj (y j)⁻¹) ^ (e r j)) z (rep r) =
        ((γ r j * MulAut.conj (x r j)⁻¹) (z (rep r))) := by
  classical
  let y : Fin m → (I → S) := fun j i => factorCorrection rep sel x j i
  refine ⟨y, ?_⟩
  intro r j hsj z
  let w : I → S := fun i =>
    if i = rep r then (x r j)⁻¹ * z i * x r j else z i
  let g : MulAut (I → S) := k j * MulAut.conj (y j)⁻¹
  let n := e r j - 1
  have hepos := hsel r j hsj
  have hn : n + 1 = e r j := by
    dsimp [n]
    omega
  have hper : Function.IsPeriodicPt (σ j) (e r j) (rep r) :=
    periodicity_of_pow_fix (σ j) (e r j) (rep r) (hreturn r j hsj)
  have hbase : g z ((σ j) (rep r)) = k j w ((σ j) (rep r)) := by
    change (k j * MulAut.conj (y j)⁻¹) z ((σ j) (rep r)) =
      k j w ((σ j) (rep r))
    rw [step_formula k σ β hcoord]
    have hy := factorCorrection_at rep hinjrep sel x j r hsj
    have hw : w (rep r) = (x r j)⁻¹ * z (rep r) * x r j := by simp [w]
    rw [hcoord j w (rep r)]
    change (β j (rep r)) (y j (rep r))⁻¹ * (β j (rep r)) (z (rep r)) *
      (β j (rep r)) (y j (rep r)) = (β j (rep r)) (w (rep r))
    rw [show y j (rep r) = x r j by exact hy, hw]
    simp only [map_inv, map_mul]
  have hpath :
      ∀ a : I, (∀ r' < n, y j ((σ j)^[r'] a) = 1) →
        ∀ u v : I → S, u a = v a →
        (g ^ n) u ((σ j)^[n] a) = (k j ^ n) v ((σ j)^[n] a) := by
    intro a ha u v huv
    exact path_same k σ β hcoord j (y j) n a ha u v huv
  have hzero : ∀ r' < n, y j ((σ j)^[r'] ((σ j) (rep r))) = 1 := by
    intro r' hr'
    apply factorCorrection_eq_one rep sel x j
    intro r'' hrsel heq
    by_cases heqr : r'' = r
    · subst r''
      have hlt : r' + 1 < e r j := by omega
      have hne : (σ j)^[r' + 1] (rep r) ≠ rep r := by
        intro hfix
        exact hminimal r j hsj (r' + 1) (by omega) hlt hfix
      apply hne
      rw [Function.iterate_succ_apply]
      exact heq.symm
    · have hperpt : (rep r) ∈ Function.periodicPts (σ j) :=
          Function.mk_mem_periodicPts (f := σ j) (x := rep r) (by omega) hper
      have horb :
          (Function.periodicOrbit (σ j) ((σ j)^[r' + 1] (rep r))).toFinset =
            (Function.periodicOrbit (σ j) (rep r)).toFinset := by
        rw [Function.periodicOrbit_apply_iterate_eq hperpt (r' + 1)]
      have hcyc :
          (Function.periodicOrbit (σ j) (rep r'')).toFinset =
            (Function.periodicOrbit (σ j) (rep r)).toFinset := by
        calc
          (Function.periodicOrbit (σ j) (rep r'')).toFinset =
              (Function.periodicOrbit (σ j) ((σ j)^[r'] ((σ j) (rep r)))).toFinset := by rw [heq]
          _ = (Function.periodicOrbit (σ j) ((σ j)^[r' + 1] (rep r))).toFinset := by
            rw [Function.iterate_succ_apply]
          _ = (Function.periodicOrbit (σ j) (rep r)).toFinset := horb
      exact (hind r r'' j (Ne.symm heqr) hsj hrsel hcyc.symm).elim
  have hiter : (σ j)^[n] ((σ j) (rep r)) = rep r := by
    rw [← Function.iterate_succ_apply]
    have heqfix : (σ j)^[n + 1] (rep r) = rep r := by
      simpa [hn] using hper.isFixedPt.eq
    exact heqfix
  have hpow : (g ^ (n + 1)) z (rep r) = (k j ^ (n + 1)) w (rep r) := by
    rw [pow_succ, pow_succ]
    simp only [MulAut.mul_apply]
    rw [← hiter]
    exact hpath ((σ j) (rep r)) hzero (g z) (k j w) hbase
  have hpowE : (g ^ e r j) z (rep r) = (k j ^ e r j) w (rep r) := by
    simpa [hn] using hpow
  rw [hcomponent r j hsj w] at hpowE
  have hw : w (rep r) = (x r j)⁻¹ * z (rep r) * x r j := by simp [w]
  rw [hw] at hpowE
  refine hpowE.trans ?_
  simp [MulAut.mul_apply, MulAut.conj_inv_apply, map_inv, map_mul]

theorem actual_factor_tuple_q_power_corrections
    {S R I : Type u} [Group S] [Fintype R] [Fintype I]
    [DecidableEq R] [DecidableEq I]
    {m : ℕ} (q : ℕ)
    (k : Fin m → MulAut (I → S)) (σ : Fin m → Equiv.Perm I)
    (β : Fin m → I → MulAut S)
    (hcoord : ∀ j z i, k j z (σ j i) = β j i (z i))
    (rep : R → I) (hinjrep : Function.Injective rep)
    (sel : R → Finset (Fin m)) (x : R → Fin m → S)
    (e : R → Fin m → ℕ) (γ : R → Fin m → MulAut S)
    (hdiv : ∀ r j, j ∈ sel r → 0 < e r j ∧ e r j ∣ q)
    (hreturn : ∀ r j, j ∈ sel r → (σ j ^ e r j) (rep r) = rep r)
    (hcomponent : ∀ r j, j ∈ sel r → ∀ z,
      (k j ^ e r j) z (rep r) = γ r j (z (rep r)))
    (hminimal : ∀ r j, j ∈ sel r → ∀ n, 0 < n → n < e r j →
      (σ j)^[n] (rep r) ≠ rep r)
    (hind : ∀ r r' j, r ≠ r' → j ∈ sel r → j ∈ sel r' →
      (Function.periodicOrbit (σ j) (rep r)).toFinset ≠
        (Function.periodicOrbit (σ j) (rep r')).toFinset) :
    ∃ y : Fin m → (I → S), ∀ r j, j ∈ sel r → ∀ z,
      ((k j * MulAut.conj (y j)⁻¹) ^ q) z (rep r) =
        (((γ r j * MulAut.conj (x r j)⁻¹) ^ (q / e r j))
          (z (rep r))) := by
  obtain ⟨y, hstep⟩ := actual_factor_tuple_corrections k σ β hcoord rep
    hinjrep sel x e γ (fun r j h => (hdiv r j h).1) hreturn hcomponent
    hminimal hind
  refine ⟨y, ?_⟩
  intro r j hsj z
  let g : MulAut (I → S) := k j * MulAut.conj (y j)⁻¹
  let δ : MulAut S := γ r j * MulAut.conj (x r j)⁻¹
  have hpow : ∀ n : ℕ, ∀ w : I → S,
      ((g ^ e r j) ^ n) w (rep r) = (δ ^ n) (w (rep r)) := by
    intro n
    induction n with
    | zero => intro w; simp
    | succ n ih =>
      intro w
      rw [pow_succ]
      change ((g ^ e r j) ^ n) ((g ^ e r j) w) (rep r) =
        (δ ^ n.succ) (w (rep r))
      rw [ih ((g ^ e r j) w)]
      rw [hstep r j hsj w]
      rw [pow_succ]
      rfl
  have hq : e r j * (q / e r j) = q :=
    Nat.mul_div_cancel' (hdiv r j hsj).2
  calc
    (g ^ q) z (rep r) = (g ^ (e r j * (q / e r j))) z (rep r) := by rw [hq]
    _ = ((g ^ e r j) ^ (q / e r j)) z (rep r) := by rw [pow_mul]
    _ = (δ ^ (q / e r j)) (z (rep r)) := hpow (q / e r j) z
    _ = ((γ r j * MulAut.conj (x r j)⁻¹) ^ (q / e r j))
          (z (rep r)) := by rfl

theorem actual_factor_tuple_q_power_from_coordinate
    {S R I : Type u} [Group S] [Fintype R] [Fintype I]
    [DecidableEq R] [DecidableEq I]
    {m : ℕ} (q : ℕ)
    (k : Fin m → MulAut (I → S)) (σ : Fin m → Equiv.Perm I)
    (β : Fin m → I → MulAut S)
    (hcoord : ∀ j z i, k j z (σ j i) = β j i (z i))
    (rep : R → I) (hinjrep : Function.Injective rep)
    (sel : R → Finset (Fin m)) (x : R → Fin m → S)
    (e : R → Fin m → ℕ)
    (hdiv : ∀ r j, j ∈ sel r → 0 < e r j ∧ e r j ∣ q)
    (hreturn : ∀ r j, j ∈ sel r → (σ j ^ e r j) (rep r) = rep r)
    (hminimal : ∀ r j, j ∈ sel r → ∀ n, 0 < n → n < e r j →
      (σ j)^[n] (rep r) ≠ rep r)
    (hind : ∀ r r' j, r ≠ r' → j ∈ sel r → j ∈ sel r' →
      (Function.periodicOrbit (σ j) (rep r)).toFinset ≠
        (Function.periodicOrbit (σ j) (rep r')).toFinset) :
    ∃ y : Fin m → (I → S), ∀ r j, j ∈ sel r → ∀ z,
      ((k j * MulAut.conj (y j)⁻¹) ^ q) z (rep r) =
        (((cycleComponent β σ j (rep r) (e r j) *
          MulAut.conj (x r j)⁻¹) ^ (q / e r j)) (z (rep r))) := by
  let γ : R → Fin m → MulAut S := fun r j =>
    cycleComponent β σ j (rep r) (e r j)
  have hcomponent : ∀ r j, j ∈ sel r → ∀ z,
      (k j ^ e r j) z (rep r) = γ r j (z (rep r)) := by
    intro r j hsj z
    exact actual_cycle_component_at_return k σ β hcoord j (rep r) (e r j)
      (hreturn r j hsj) z
  obtain ⟨y, hy⟩ := actual_factor_tuple_q_power_corrections q k σ β hcoord
    rep hinjrep sel x e γ hdiv hreturn hcomponent hminimal hind
  refine ⟨y, ?_⟩
  intro r j hsj z
  exact hy r j hsj z

private theorem orderedProduct_restrict_finset
    {G : Type u} [Group G] {m M : ℕ}
    (s : Finset (Fin m)) (hs : s.card = M)
    (f : Fin m → G) (hf : ∀ j, j ∉ s → f j = 1) :
    orderedProduct f =
      orderedProduct (fun t : Fin M => f (s.orderEmbOfFin hs t)) := by
  classical
  let emb : Fin M → Fin m := s.orderEmbOfFin hs
  have hsort : (List.finRange m).filter (fun j => decide (j ∈ s)) = s.sort := by
    apply List.SortedLT.eq_of_mem_iff
    · exact ((List.sortedLT_finRange m).pairwise.filter _).sortedLT
    · exact s.sortedLT_sort
    · intro a
      simp [Finset.mem_sort]
  have hidx : (List.finRange m).filter (fun j => f j != 1) =
      (List.map emb (List.finRange M)).filter (fun j => f j != 1) := by
    have hleft : (List.finRange m).filter (fun j => f j != 1) =
        ((List.finRange m).filter (fun j => decide (j ∈ s))).filter
          (fun j => f j != 1) := by
      rw [List.filter_filter]
      apply List.filter_congr
      intro j hj
      by_cases hfj : f j != 1
      · have hjs : j ∈ s := by
          by_contra hjs
          have hh := hf j hjs
          simp [hh] at hfj
        simp [hfj, hjs]
      · simp [hfj]
    calc
      (List.finRange m).filter (fun j => f j != 1) =
          ((List.finRange m).filter (fun j => decide (j ∈ s))).filter
            (fun j => f j != 1) := hleft
      _ = (s.sort).filter (fun j => f j != 1) := by rw [hsort]
      _ = ((List.map emb (List.finRange M)).filter (fun j => f j != 1)) := by
        rw [Finset.listMap_orderEmbOfFin_finRange s hs]
  have hmap :
      ((List.finRange m).map f).filter (fun z => z != 1) =
      ((List.finRange M).map (fun t => f (emb t))).filter (fun z => z != 1) := by
    rw [List.filter_map, List.filter_map]
    change List.map f ((List.finRange m).filter (fun j => f j != 1)) =
      List.map (fun t => f (emb t))
        ((List.finRange M).filter (fun t => f (emb t) != 1))
    rw [hidx, List.filter_map, List.map_map]
    rfl
  calc
    orderedProduct f = (((List.finRange m).map f).filter (fun z => z != 1)).prod := by
      rw [orderedProduct, List.ofFn_eq_map]
      exact (List.prod_filter_bne_one ((List.finRange m).map f)).symm
    _ = (((List.finRange M).map (fun t => f (emb t))).filter
        (fun z => z != 1)).prod := by rw [hmap]
    _ = ((List.finRange M).map (fun t => f (emb t))).prod :=
      List.prod_filter_bne_one _
    _ = orderedProduct (fun t : Fin M => f (emb t)) := by
      simp [orderedProduct, List.ofFn_eq_map]

theorem actual_selected_supported_ordered_product_reconstruction_with_support
    {S R I : Type u} [Group S] [Fintype R] [Fintype I]
    [DecidableEq R] [DecidableEq I]
    {m q M : ℕ}
    (k : Fin m → MulAut (I → S)) (σ : Fin m → Equiv.Perm I)
    (β : Fin m → I → MulAut S)
    (hcoord : ∀ j z i, k j z (σ j i) = β j i (z i))
    (rep : R → I) (hinjrep : Function.Injective rep)
    (Iset : R → Finset (Fin m)) (hIcard : ∀ r, (Iset r).card = M)
    (e : R → Fin m → ℕ)
    (hdiv : ∀ r j, j ∈ Iset r → 0 < e r j ∧ e r j ∣ q)
    (hreturn : ∀ r j, j ∈ Iset r → (σ j ^ e r j) (rep r) = rep r)
    (hminimal : ∀ r j, j ∈ Iset r → ∀ n, 0 < n → n < e r j →
      (σ j)^[n] (rep r) ≠ rep r)
    (hind : ∀ r r' j, r ≠ r' → j ∈ Iset r → j ∈ Iset r' →
      (Function.periodicOrbit (σ j) (rep r)).toFinset ≠
        (Function.periodicOrbit (σ j) (rep r')).toFinset)
    (hscalar : ∀ r, PartIIScalarProductInput q M
      (fun t : Fin M =>
        cycleComponent β σ ((Iset r).orderEmbOfFin (hIcard r) t)
          (rep r) (e r ((Iset r).orderEmbOfFin (hIcard r) t)))
      (fun t : Fin M => e r ((Iset r).orderEmbOfFin (hIcard r) t))) :
    ∃ y : Fin m → (I → S),
      ∀ r t, ∃ c : Fin m → (I → S),
        orderedProduct (fun j => fun i =>
          (c j i)⁻¹ *
            (((k j * MulAut.conj (y j)⁻¹) ^ q) (c j)) i) =
          (fun i => if i = rep r then t else 1) ∧
        (∀ j i, j ∉ Iset r ∨ i ≠ rep r → c j i = 1) := by
  classical
  let emb : ∀ r : R, Fin M → Fin m := fun r =>
    (Iset r).orderEmbOfFin (hIcard r)
  let index : ∀ r : R, ∀ j : Fin m, j ∈ Iset r → Fin M := fun r j hj =>
    ((Iset r).orderIsoOfFin (hIcard r)).symm ⟨j, hj⟩
  have hemb_mem : ∀ r t, emb r t ∈ Iset r := by
    intro r t
    exact Finset.orderEmbOfFin_mem (Iset r) (hIcard r) t
  have hindex_emb : ∀ r t, index r (emb r t) (hemb_mem r t) = t := by
    intro r t
    have hs : (⟨emb r t, hemb_mem r t⟩ : Iset r) =
        (Iset r).orderIsoOfFin (hIcard r) t := by
      apply Subtype.ext
      exact Finset.coe_orderIsoOfFin_apply (Iset r) (hIcard r) t
    simp [index, hs]
  have hxbase : ∀ r, ∃ x₀ : Fin M → S, ∀ t : S, ∃ c₀ : Fin M → S,
      orderedProduct (fun a => (c₀ a)⁻¹ *
        (((cycleComponent β σ (emb r a) (rep r) (e r (emb r a)) *
          MulAut.conj (x₀ a)⁻¹) ^ (q / e r (emb r a))) (c₀ a))) = t := by
    intro r
    exact hscalar r (fun t => hdiv r (emb r t) (hemb_mem r t))
  choose x₀ hx₀ using hxbase
  let x : R → Fin m → S := fun r j =>
    if hj : j ∈ Iset r then x₀ r (index r j hj) else 1
  have hx_emb : ∀ r t, x r (emb r t) = x₀ r t := by
    intro r t
    dsimp [x]
    simp only [dif_pos (hemb_mem r t)]
    simpa only [hindex_emb r t]
  obtain ⟨y, hy⟩ := actual_factor_tuple_q_power_from_coordinate q k σ β hcoord
    rep hinjrep Iset x e
    (by intro r j hj; exact hdiv r j hj)
    (by intro r j hj; exact hreturn r j hj)
    (by intro r j hj n hn hne; exact hminimal r j hj n hn hne)
    (by intro r r' j hne hj hj'; exact hind r r' j hne hj hj')
  refine ⟨y, ?_⟩
  intro r t
  obtain ⟨c₀, hc₀⟩ := hx₀ r t
  let c : Fin m → (I → S) := fun j i =>
    if hj : j ∈ Iset r then if i = rep r then c₀ (index r j hj) else 1 else 1
  let g : Fin m → MulAut (I → S) := fun j =>
    k j * MulAut.conj (y j)⁻¹
  have hstep_support : ∀ (j : Fin m) (z : I → S) (a : I),
      (∀ i, i ≠ a → z i = 1) →
        ∀ i, i ≠ σ j a → (g j z) i = 1 := by
    intro j z a hz i hi
    let b := (σ j).symm i
    have hb : σ j b = i := (σ j).apply_symm_apply i
    have hba : b ≠ a := by
      intro hba
      apply hi
      simpa [b, hba] using hb.symm
    have hzb : z b = 1 := hz b hba
    rw [← hb]
    change (k j * MulAut.conj (y j)⁻¹) z (σ j b) = 1
    rw [step_formula k σ β hcoord]
    simp [hzb]
  have hiterate_support : ∀ (j : Fin m) (n : ℕ) (z : I → S) (a : I),
      (∀ i, i ≠ a → z i = 1) →
        ∀ i, i ≠ (σ j)^[n] a → (((g j) ^ n) z) i = 1 := by
    intro j n
    induction n with
    | zero =>
        intro z a hz i hi
        simpa using hz i hi
    | succ n ih =>
        intro z a hz i hi
        rw [pow_succ']
        simp only [MulAut.mul_apply]
        apply hstep_support j (((g j) ^ n) z) ((σ j)^[n] a)
        · exact ih z a hz
        · simpa [Function.iterate_succ_apply'] using hi
  have hpower_iterate : ∀ (j : Fin m) (n : ℕ) (i : I),
      (σ j ^ n) i = (σ j)^[n] i := by
    intro j n
    induction n with
    | zero => intro i; simp
    | succ n ih =>
        intro i
        rw [pow_succ]
        change (σ j ^ n) ((σ j) i) = _
        rw [ih]
        exact (Function.iterate_succ_apply (σ j) n i).symm
  have hqfix : ∀ j : Fin m, j ∈ Iset r → (σ j ^ q) (rep r) = rep r := by
    intro j hj
    have heq : e r j * (q / e r j) = q :=
      Nat.mul_div_cancel' (hdiv r j hj).2
    have hfix : ∀ n : ℕ, (((σ j) ^ e r j) ^ n) (rep r) = rep r := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
          rw [pow_succ]
          simp only [Equiv.Perm.coe_mul, Function.comp_apply]
          rw [hreturn r j hj, ih]
    calc
      ((σ j) ^ q) (rep r) = ((σ j) ^ (e r j * (q / e r j))) (rep r) := by rw [heq]
      _ = (((σ j) ^ e r j) ^ (q / e r j)) (rep r) := by rw [pow_mul]
      _ = rep r := hfix (q / e r j)
  have hEval : ∀ (f : Fin m → (I → S)) (i : I),
      (orderedProduct f) i = orderedProduct (fun j => f j i) := by
    intro f i
    simpa [orderedProduct, List.map_ofFn, Function.comp_def] using
      (map_list_prod (Pi.evalMonoidHom (fun _ : I => S) i) (List.ofFn f))
  have hterm_selected : ∀ (j : Fin m) (hj : j ∈ Iset r),
      (c j (rep r))⁻¹ * (((g j) ^ q) (c j)) (rep r) =
        (c₀ (index r j hj))⁻¹ *
          (((cycleComponent β σ j (rep r) (e r j) *
            MulAut.conj (x r j)⁻¹) ^ (q / e r j))
              (c₀ (index r j hj))) := by
    intro j hj
    have hjq := hy r j hj (c j)
    have hcj : c j (rep r) = c₀ (index r j hj) := by
      simp [c, hj]
    rw [hcj, hjq]
    simp [c, hj]
  have hterm_outside : (∀ (j : Fin m), j ∉ Iset r →
      (c j (rep r))⁻¹ * (((g j) ^ q) (c j)) (rep r) = 1) := by
    intro j hj
    have hcg : c j = (1 : I → S) := by
      funext i
      simp [c, hj]
    rw [hcg]
    simp
  have hzero : ∀ j : Fin m, j ∈ Iset r → ∀ i : I, i ≠ rep r →
      (c j i)⁻¹ * (((g j) ^ q) (c j)) i = 1 := by
    intro j hj i hi
    have hci : c j i = 1 := by simp [c, hj, hi]
    have hiter : i ≠ (σ j)^[q] (rep r) := by
      intro heq
      have hfixiter : (σ j)^[q] (rep r) = rep r :=
        (hpower_iterate j q (rep r)).symm.trans (hqfix j hj)
      exact hi (heq.trans hfixiter)
    have hg := hiterate_support j q (c j) (rep r)
      (by intro a ha; simp [c, hj, ha]) i hiter
    rw [hci, hg]
    simp
  refine ⟨c, ?_, ?_⟩
  · funext i
    by_cases hi : i = rep r
    · subst i
      rw [hEval]
      change orderedProduct (fun j =>
        (c j (rep r))⁻¹ * (((g j) ^ q) (c j)) (rep r)) = _
      have hout : ∀ j, j ∉ Iset r →
          (c j (rep r))⁻¹ * (((g j) ^ q) (c j)) (rep r) = 1 :=
        hterm_outside
      have hprod := orderedProduct_restrict_finset (Iset r) (hIcard r)
        (fun j => (c j (rep r))⁻¹ * (((g j) ^ q) (c j)) (rep r)) hout
      rw [hprod]
      have hterms : (fun a : Fin M =>
          (c (emb r a) (rep r))⁻¹ * (((g (emb r a)) ^ q)
            (c (emb r a))) (rep r)) =
          (fun a : Fin M =>
            (c₀ a)⁻¹ *
              ((((cycleComponent β σ (emb r a) (rep r) (e r (emb r a))) *
                MulAut.conj (x₀ r a)⁻¹) ^
                  (q / e r (emb r a))) (c₀ a))) := by
        funext a
        have ha := hterm_selected (emb r a) (hemb_mem r a)
        simpa [hindex_emb r a, hx_emb r a, x] using ha
      rw [hterms]
      simpa using hc₀
    · rw [hEval]
      change orderedProduct (fun j =>
        (c j i)⁻¹ * (((g j) ^ q) (c j)) i) = _
      have hvals : (fun j => (c j i)⁻¹ * (((g j) ^ q) (c j)) i) =
          (fun _ => (1 : S)) := by
        funext j
        by_cases hj : j ∈ Iset r
        · exact hzero j hj i hi
        · have hcg : c j = (1 : I → S) := by
            funext a
            simp [c, hj]
          rw [hcg]
          simp
      rw [hvals]
      simp [hi, orderedProduct]
  · intro j i h
    rcases h with hj | hi
    · simp [c, hj]
    · by_cases hj : j ∈ Iset r <;> simp [c, hj, hi]

theorem actual_selected_interval_with_support
    {S R I : Type u} [Group S] [Fintype R] [Fintype I]
    [DecidableEq R] [DecidableEq I]
    {m q D M : ℕ} (hq : 0 < q) (hD : 0 < D) (hM : 0 < M)
    (hm : M * D * (q + D) ≤ m)
    (rep : R → I) (hinjrep : Function.Injective rep)
    (good : Fin m → I → Prop) (σ : Fin m → Equiv.Perm I)
    [∀ j, DecidablePred (good j)]
    (hperiod : ∀ j x, good j x → Function.IsPeriodicPt (σ j) q x)
    (hbad : ∀ o,
      (Finset.univ.filter (fun j : Fin m => ¬ good j (rep o))).card < D)
    (k : Fin m → MulAut (I → S)) (β : Fin m → I → MulAut S)
    (hcoord : ∀ j z i, k j z (σ j i) = β j i (z i))
    (hscalar : ∀ (Iset : R → Finset (Fin m)),
      (hIcard : ∀ r, (Iset r).card = M) →
      (hgood : ∀ r j, j ∈ Iset r → good j (rep r)) →
      ∀ r, PartIIScalarProductInput q M
        (fun t : Fin M =>
          cycleComponent β σ ((Iset r).orderEmbOfFin (hIcard r) t)
            (rep r)
              (Function.minimalPeriod
                (σ ((Iset r).orderEmbOfFin (hIcard r) t)) (rep r)))
        (fun t : Fin M => Function.minimalPeriod
          (σ ((Iset r).orderEmbOfFin (hIcard r) t)) (rep r))) :
    ∃ J : R → Fin D, ∃ Iset : R → Finset (Fin m),
      (∀ r, Iset r ⊆ prefixPiece good rep r (J r) ∧ (Iset r).card = M) ∧
      (∀ r, ConsecutiveInterval (prefixPiece good rep r (J r))) ∧
      (∀ r j, j ∈ prefixPiece good rep r (J r) → good j (rep r)) ∧
      ∃ y : Fin m → (I → S),
      ∀ r t, ∃ c : Fin m → (I → S),
        orderedProduct (fun j => fun i =>
          (c j i)⁻¹ *
            (((k j * MulAut.conj (y j)⁻¹) ^ q) (c j)) i) =
          (fun i => if i = rep r then t else 1) ∧
          (∀ j i, j ∉ Iset r ∨ i ≠ rep r → c j i = 1) := by
  obtain ⟨J, Iset, hI, hfixed, hinterval, hind⟩ :=
    lemma10_3_interval_selection_actual hq hD hM hm rep hinjrep good σ
      hperiod hbad
  have hIcard : ∀ r, (Iset r).card = M := by
    intro r
    exact (hI r).2
  have hgood : ∀ r j, j ∈ Iset r → good j (rep r) := by
    intro r j hj
    exact (Finset.mem_filter.mp (hfixed r j hj)).2
  let e : R → Fin m → ℕ := fun r j => Function.minimalPeriod (σ j) (rep r)
  have hdiv : ∀ r j, j ∈ Iset r → 0 < e r j ∧ e r j ∣ q := by
    intro r j hj
    have hp := hperiod j (rep r) (hgood r j hj)
    exact ⟨by simpa [e] using hp.minimalPeriod_pos hq,
      by simpa [e] using hp.minimalPeriod_dvd⟩
  have hreturn : ∀ r j, j ∈ Iset r →
      (σ j ^ e r j) (rep r) = rep r := by
    intro r j hj
    have hp := (Function.isPeriodicPt_minimalPeriod (σ j) (rep r)).isFixedPt.eq
    simpa [e, Equiv.Perm.coe_pow] using hp
  have hminimal : ∀ r j, j ∈ Iset r → ∀ n, 0 < n → n < e r j →
      (σ j)^[n] (rep r) ≠ rep r := by
    intro r j hj n hn hlt hfix
    have hp : Function.IsPeriodicPt (σ j) n (rep r) := hfix
    have hz := hp.eq_zero_of_lt_minimalPeriod (by simpa [e] using hlt)
    exact (Nat.ne_of_gt hn) hz
  have hind' : ∀ r r' j, r ≠ r' → j ∈ Iset r → j ∈ Iset r' →
      (Function.periodicOrbit (σ j) (rep r)).toFinset ≠
        (Function.periodicOrbit (σ j) (rep r')).toFinset := by
    intro r r' j hrr hj hj'
    have hp := hind (o := r) (j := j) (o' := r') (j' := j)
      (by intro h; exact hrr (congrArg Prod.fst h)) hj hj'
    rcases hp with hp | hp
    · exact (hp rfl).elim
    · exact hp
  refine ⟨J,Iset,hI,hinterval,?_,?_⟩
  · intro r j hj
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp hj).1).2
  · exact actual_selected_supported_ordered_product_reconstruction_with_support
      k σ β hcoord rep hinjrep Iset hIcard e hdiv hreturn hminimal hind'
      (by
        intro r
        simpa [e] using hscalar Iset hIcard hgood r)

end NikolovSegal
