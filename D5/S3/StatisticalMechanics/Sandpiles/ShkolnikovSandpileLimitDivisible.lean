/- GID: D5/S3/StatisticalMechanics/Sandpiles/ShkolnikovSandpileLimitDivisible
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/Sandpiles/ShkolnikovSandpileLimitDivisible
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Shkolnikov's direct limit of rectangular sandpile groups is divisible. -/

/-
proof_shape: result: bind-only (open-problem-resolution settlement); all private helper theorems are bind-only and consumed by result.
escape_witness: none (the settling result is admitted under open-problem-resolution).
admission_basis: open-problem-resolution (#20011; Proved)
escape_audit_issue: https://github.com/the-omega-institute/trureturing/issues/20360
Direct frozen dependencies: D5/S1/Recurrence/FiniteCompanionSquareDefect.headCodomainEquiv
(statement_id: sha256:bc77669224c3485a06b5cee672f63a146fc49a3712a811398af6ac98ed52084c).
The source definitions stay literal in `claim`; proofs use the inverse two-head equivalence with additive normalization, the row recurrence and finite-denominator constructions.
-/

import Mathlib.Topology.Instances.AddCircle.Real
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import D5.S1.Recurrence.FiniteCompanionSquareDefect


namespace D5.S3.StatisticalMechanics.Sandpiles.ShkolnikovSandpileLimitDivisible
variable {V : Type*} [AddCommGroup V]

private def transfer (B : V →+ V) (uv : V × V) : V × V :=
  (D5.S1.Recurrence.FiniteCompanionSquareDefect.headCodomainEquiv
    (B - AddMonoidHom.id V) 2).symm uv

@[simp] private theorem transfer_apply (B : V →+ V) (uv : V × V) :
    transfer B uv = (uv.2, B uv.2 - uv.1) := by
  apply Prod.ext
  · rfl
  · change uv.2 + (B uv.2 - uv.2) - uv.1 = B uv.2 - uv.1
    abel

private theorem transfer_injective (B : V →+ V) : Function.Injective (transfer B) :=
  (D5.S1.Recurrence.FiniteCompanionSquareDefect.headCodomainEquiv
    (B - AddMonoidHom.id V) 2).symm.injective

private def rows (B : V →+ V) (a : V) (n : ℕ) : V := ((transfer B)^[n] (0,a)).1

@[simp] private theorem rows_zero (B : V →+ V) (a : V) : rows B a 0 = 0 := rfl
@[simp] private theorem rows_one (B : V →+ V) (a : V) : rows B a 1 = a := rfl

private theorem rows_pair (B : V →+ V) (a : V) (n : ℕ) :
    (transfer B)^[n] (0,a) = (rows B a n, rows B a (n+1)) := by
  apply Prod.ext
  · rfl
  · simp only [rows, Function.iterate_succ_apply', transfer_apply]

private theorem rows_rec (B : V →+ V) (a : V) (n : ℕ) :
    rows B a (n+2) = B (rows B a (n+1)) - rows B a n := by
  have h := congrArg Prod.snd (rows_pair B a (n+1))
  rw [Function.iterate_succ_apply', rows_pair] at h
  simpa only [transfer_apply] using h.symm

private theorem recurrence_unique (B : V →+ V) (r s : ℕ → V)
    (h0 : r 0 = s 0) (h1 : r 1 = s 1)
    (hr : ∀ n, r (n+2) = B (r (n+1)) - r n)
    (hs : ∀ n, s (n+2) = B (s (n+1)) - s n) : r = s := by
  have hpair : ∀ n, r n = s n ∧ r (n+1) = s (n+1) := by
    intro n
    induction n with
    | zero => exact ⟨h0,h1⟩
    | succ n ih => exact ⟨ih.2, by rw [hr, hs, ih.1, ih.2]⟩
  funext n
  exact (hpair n).1

private theorem rows_nsmul (B : V →+ V) (a : V) (k n : ℕ) :
    rows B (k • a) n = k • rows B a n := by
  let F : V × V → V × V := fun uv => (k • uv.1,k • uv.2)
  have hF : Function.Semiconj F (transfer B) (transfer B) := by
    intro uv
    exact (map_nsmul
      (D5.S1.Recurrence.FiniteCompanionSquareDefect.headCodomainEquiv
        (B - AddMonoidHom.id V) 2).symm k uv).symm
  simpa [F,rows] using (congrArg Prod.fst (hF.iterate_right n (0,a))).symm

private theorem rows_period (B : V →+ V) (a : V) [Finite V] :
    ∃ P : ℕ, 0 < P ∧ ∀ n, rows B a (n+P) = rows B a n := by
  obtain ⟨P,hP,h⟩ := Function.Injective.mem_periodicPts (transfer_injective B) (0,a)
  refine ⟨P,hP,fun n => ?_⟩
  have hn := h.apply_iterate n
  simpa only [Function.IsPeriodicPt, Function.IsFixedPt, ← Function.iterate_add_apply,
    add_comm P n, rows] using congrArg Prod.fst hn

private theorem rows_reflect (B : V →+ V) (a : V) {q : ℕ} (hq : 0 < q)
    (hz : rows B a q = 0) :
    ∀ t, t ≤ q → rows B a (q+t) = - rows B a (q-t) := by
  have hfirst : rows B a (q+1) = -rows B a (q-1) := by
    have h := rows_rec B a (q-1)
    have he : q-1+1=q := by exact Nat.sub_add_cancel hq
    have he' : q-1+2=q+1 := by
      exact Eq.symm ((fun {m k n} => Nat.add_left_inj.mpr) (id (Eq.symm he)))
    rw [he, he', hz, map_zero, zero_sub] at h
    exact h
  have hp : ∀ t, t ≤ q →
      rows B a (q+t) = -rows B a (q-t) ∧
      (t < q → rows B a (q+t+1) = -rows B a (q-t-1)) := by
    intro t
    induction t with
    | zero => intro _; simpa [hz] using And.intro (show (0:V) = -0 by simp) (fun _ => hfirst)
    | succ t ih =>
      intro ht
      obtain ⟨h0,h1⟩ := ih (by omega)
      refine ⟨by simpa [Nat.add_assoc, Nat.sub_sub] using h1 (by omega), ?_⟩
      intro htq
      have hleft := rows_rec B a (q+t)
      have hright := rows_rec B a (q-t-2)
      have e0 : q-t-2+2=q-t := by omega
      have e1 : q-t-2+1=q-t-1 := by
        exact Eq.symm ((fun {n m} => Nat.pred_eq_succ_iff.mpr) (id (Eq.symm e0)))
      rw [e0,e1] at hright
      have h1' := h1 (by omega)
      rw [h1',h0,map_neg] at hleft
      have e2 : q+(t+1)+1=q+t+2 := by exact Nat.add_left_inj.mpr rfl
      have e3 : q-(t+1)-1=q-t-2 := by exact Eq.symm (Nat.sub_succ' (q - t) 1)
      rw [e2,e3,hleft]
      rw [hright]
      abel
  exact fun t ht => (hp t ht).1

private theorem rows_double_period (B : V →+ V) (a : V) {q : ℕ} (hq : 0 < q)
    (hz : rows B a q = 0) : ∀ n, rows B a (n+2*q) = rows B a n := by
  have hr := rows_reflect B a hq hz
  have h2q : rows B a (2*q) = 0 := by simpa [two_mul] using hr q (le_refl q)
  have h2qm : rows B a (2*q-1) = -a := by
    have h := hr (q-1) (by omega)
    have e0 : q+(q-1)=2*q-1 := by exact Nat.self_add_sub_one q
    have e1 : q-(q-1)=1 := by exact Nat.sub_sub_self hq
    rw [e0,e1] at h
    exact h.trans (congrArg Neg.neg (rows_one B a))
  have h2qp : rows B a (2*q+1) = a := by
    have h := rows_rec B a (2*q-1)
    have e0 : 2*q-1+1=2*q := by omega
    have e1 : 2*q-1+2=2*q+1 := by
      exact Eq.symm ((fun {m k n} => Nat.add_left_inj.mpr) (id (Eq.symm e0)))
    simpa [e0,e1,h2q,h2qm] using h
  have he : (fun n => rows B a (n+2*q)) = rows B a := by
    apply recurrence_unique B
    · simpa using h2q
    · simpa [add_comm] using h2qp
    · intro n; simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using rows_rec B a (n+2*q)
    · exact rows_rec B a
  intro n; exact congrFun he n

end D5.S3.StatisticalMechanics.Sandpiles.ShkolnikovSandpileLimitDivisible

namespace D5.S3.StatisticalMechanics.Sandpiles.ShkolnikovSandpileLimitDivisible
variable {V W : Type*} [AddCommGroup V] [AddCommGroup W]

private theorem rows_map (B : V →+ V) (C : W →+ W) (F : V →+ W)
    (hBC : ∀ v, F (B v) = C (F v)) (a : V) (n : ℕ) :
    F (rows B a n) = rows C (F a) n := by
  let G : V × V → W × W := fun uv => (F uv.1,F uv.2)
  have hG : Function.Semiconj G (transfer B) (transfer C) := by
    intro uv
    apply Prod.ext
    · rfl
    · simp [G,transfer_apply,map_sub,hBC]
  simpa [G,rows] using congrArg Prod.fst (hG.iterate_right n (0,a))

private theorem rows_eq_upto (B : V →+ V) (s : ℕ → V) (q : ℕ)
    (h0 : s 0 = 0) (hs : ∀ n, n+2 ≤ q → s (n+2) = B (s (n+1)) - s n) :
    ∀ n, n ≤ q → rows B (s 1) n = s n := by
  have hh : ∀ n, n ≤ q → rows B (s 1) n = s n ∧
      (n+1 ≤ q → rows B (s 1) (n+1) = s (n+1)) := by
    intro n
    induction n with
    | zero => intro _; simp [h0]
    | succ n ih =>
      intro hn
      obtain ⟨h,h'⟩ := ih (by omega)
      refine ⟨h' hn, ?_⟩
      intro hn'
      rw [rows_rec,hs n hn',h,h' hn]
  intro n hn; exact (hh n hn).1

private theorem rows_period_mul (B : V →+ V) (a : V) {d : ℕ}
    (hd : ∀ n, rows B a (n+d) = rows B a n) (n l : ℕ) :
    rows B a (n+d*l) = rows B a n := by
  simpa [Nat.mul_comm] using
    (show Function.Periodic (rows B a) d from hd).nat_mul l n

-- Signed-reflection identity expressed in quotient/remainder coordinates.
private theorem rows_tile (B : V →+ V) (a : V) {q : ℕ} (hq : 0 < q)
    (hz : rows B a q = 0) (l t : ℕ) (ht : t < q) :
    rows B a (l*q+t) =
      if l % 2 = 0 then rows B a t else -rows B a (q-t) := by
  have hper := rows_double_period B a hq hz
  have hl : l = 2*(l/2)+l%2 := by exact Eq.symm (Nat.div_add_mod l 2)
  by_cases he : l%2=0
  · rw [if_pos he]
    have hi : l*q+t=t+(2*q)*(l/2) := by
      calc
        _ = (2*(l/2)+l%2)*q+t := congrArg (fun u : ℕ => u*q+t) hl
        _ = _ := by rw [he]; ring
    rw [hi,rows_period_mul B a hper]
  · have ho : l%2=1 := by exact Nat.mod_two_ne_zero.mp he
    rw [if_neg he]
    have hi : l*q+t=(q+t)+(2*q)*(l/2) := by
      calc
        _ = (2*(l/2)+l%2)*q+t := congrArg (fun u : ℕ => u*q+t) hl
        _ = _ := by rw [ho]; ring
    rw [hi,rows_period_mul B a hper]
    exact rows_reflect B a hq hz t ht.le

end D5.S3.StatisticalMechanics.Sandpiles.ShkolnikovSandpileLimitDivisible


set_option maxHeartbeats 1000000

namespace D5.S3.StatisticalMechanics.Sandpiles.ShkolnikovSandpileLimitDivisible
open Finset Matrix
private abbrev Site (p q : ℕ) := ↥(Finset.Ioo (0:ℤ) p ×ˢ Finset.Ioo (0:ℤ) q)

variable {A : Type*} [AddCommGroup A]

private noncomputable abbrev ext0 {p q : ℕ} (v : Site p q → A) : ℤ × ℤ → A :=
  Function.extend (Subtype.val : Site p q → ℤ × ℤ) v (fun _ => 0)

@[simp] private theorem ext0_site {p q : ℕ} (v : Site p q → A) (i : Site p q) : ext0 v i.val = v i :=
  Function.Injective.extend_apply Subtype.val_injective v (fun _ => 0) i

private theorem ext0_apply {p q : ℕ} (v : Site p q → A) (z : ℤ × ℤ) :
    ext0 v z = if h : z ∈ (Finset.Ioo (0:ℤ) p ×ˢ Finset.Ioo (0:ℤ) q) then v ⟨z,h⟩ else 0 := by
  classical
  by_cases h : z ∈ (Finset.Ioo (0:ℤ) p ×ˢ Finset.Ioo (0:ℤ) q)
  · simpa only [dif_pos h] using ext0_site v ⟨z,h⟩
  · rw [dif_neg h]
    exact Function.extend_apply' v (fun _ => 0) z (by
      rintro ⟨i, hi⟩
      exact h (hi ▸ i.property))

private noncomputable def lap {p q : ℕ} (v : Site p q → A) (i : Site p q) : A :=
  (4:ℤ) • v i - ext0 v (i.val.1-1,i.val.2) - ext0 v (i.val.1+1,i.val.2) -
    ext0 v (i.val.1,i.val.2-1) - ext0 v (i.val.1,i.val.2+1)

private noncomputable def lapMatrix (p q : ℕ) : Matrix (Site p q) (Site p q) ℤ := fun i j => lap (Pi.single j 1) i

private theorem ext0_sum_single {p q : ℕ} (v : Site p q → A) (z : ℤ × ℤ) :
    ∑ j, (ext0 (Pi.single j 1) z : ℤ) • v j = ext0 v z := by
  classical
  simp only [ext0_apply]
  split_ifs with h
  · simpa only [Fintype.linearCombination_apply, Pi.single_apply, eq_comm, one_smul] using
      (Fintype.linearCombination_apply_single ℤ v (⟨z,h⟩ : Site p q) 1)
  · simp

private theorem matrix_action {p q : ℕ} (v : Site p q → A) (i : Site p q) :
    ∑ j, lapMatrix p q i j • v j = lap v i := by
  classical
  simp only [lapMatrix, lap, zsmul_eq_mul, sub_smul, mul_smul, Finset.sum_sub_distrib]
  rw [ext0_sum_single,ext0_sum_single,ext0_sum_single,ext0_sum_single]
  simp [Pi.single_apply, lap]

-- The maximum principle is stated with the exact zero extension.
private theorem integer_harmonic_zero {p q : ℕ} (v : Site p q → ℤ)
    (hv : ∀ i, lap v i = 0) : v = 0 := by
  classical
  by_contra hne
  have hnot : ¬ ∀ i, v i = 0 := by
    intro h; apply hne; funext i; exact h i
  obtain ⟨i,hi⟩ := not_forall.mp hnot
  letI : Nonempty (Site p q) := ⟨i⟩
  obtain ⟨b,_,hb⟩ := Finset.exists_mem_eq_sup' (Finset.univ_nonempty : (Finset.univ : Finset (Site p q)).Nonempty)
    (fun j => |v j|)
  let M := |v b|
  have hbnd : ∀ j, |v j| ≤ M := fun j =>
    (Finset.le_sup' (fun j : Site p q => |v j|) (Finset.mem_univ j)).trans_eq hb
  have hM : 0 < M := lt_of_lt_of_le (abs_pos.mpr hi) (hbnd i)
  have hbound : ∀ z, |ext0 v z| ≤ M := by
    intro z
    simp only [ext0_apply]
    split_ifs with hz
    · exact hbnd ⟨z,hz⟩
    · simpa using hM.le
  have propagate : ∀ z : ℤ × ℤ, |ext0 v z| = M → |ext0 v (z.1+1,z.2)| = M := by
    intro z hz
    have hzmem : z ∈ (Finset.Ioo (0:ℤ) p ×ˢ Finset.Ioo (0:ℤ) q) := by
      by_contra hn
      simp [ext0_apply,hn] at hz
      linarith
    have heq := hv ⟨z,hzmem⟩
    have hh : 4 * |ext0 v z| ≤ |ext0 v (z.1-1,z.2)| + |ext0 v (z.1+1,z.2)| +
        |ext0 v (z.1,z.2-1)| + |ext0 v (z.1,z.2+1)| := by
      have he : 4 * ext0 v z = ext0 v (z.1-1,z.2) + ext0 v (z.1+1,z.2) +
          ext0 v (z.1,z.2-1) + ext0 v (z.1,z.2+1) := by
        rw [show ext0 v z = v ⟨z,hzmem⟩ from by simp only [ext0_apply,dif_pos hzmem]]
        dsimp [lap] at heq
        linarith
      calc
        _ = |4 * ext0 v z| := by rw [abs_mul]; norm_num
        _ = _ := congrArg abs he
        _ ≤ _ := by
          have h1 := abs_add_le (ext0 v (z.1-1,z.2)) (ext0 v (z.1+1,z.2))
          have h2 := abs_add_le (ext0 v (z.1-1,z.2) + ext0 v (z.1+1,z.2)) (ext0 v (z.1,z.2-1))
          have h3 := abs_add_le (ext0 v (z.1-1,z.2) + ext0 v (z.1+1,z.2) + ext0 v (z.1,z.2-1)) (ext0 v (z.1,z.2+1))
          linarith
    have h1 := hbound (z.1-1,z.2)
    have h2 := hbound (z.1+1,z.2)
    have h3 := hbound (z.1,z.2-1)
    have h4 := hbound (z.1,z.2+1)
    rw [hz] at hh
    linarith
  have hr : ∀ n : ℕ, |ext0 v (b.val.1+n,b.val.2)| = M := by
    intro n
    induction n with
    | zero => simpa [M] using congrArg abs (ext0_site v b)
    | succ n ih => simpa [Nat.cast_add,add_assoc] using propagate _ ih
  have hout := hr p
  have hnon : (b.val.1 + (p:ℤ),b.val.2) ∉ (Finset.Ioo (0:ℤ) p ×ˢ Finset.Ioo (0:ℤ) q) := by
    have hbmem := b.property
    simp only [Finset.mem_product,Finset.mem_Ioo] at hbmem ⊢
    omega
  simp [ext0_apply,hnon] at hout
  linarith

private theorem lap_det_ne_zero (p q : ℕ) : (lapMatrix p q).det ≠ 0 := by
  intro hd
  obtain ⟨v,hv,hz⟩ := (Matrix.exists_mulVec_eq_zero_iff (M := lapMatrix p q)).mpr hd
  apply hv
  apply integer_harmonic_zero
  intro i
  have h := congrFun hz i
  rw [← matrix_action v i]
  exact h

private abbrev action {I : Type*} [Fintype I] (M : Matrix I I ℤ) (v : I → A) (i : I) : A :=
  Fintype.linearCombination ℤ v (M i)

private theorem action_mul {I : Type*} [Fintype I] (M N : Matrix I I ℤ) (v : I → A) :
    action (M*N) v = action M (action N v) := by
  funext i
  simp only [action, Fintype.linearCombination_apply, Matrix.mul_apply, Finset.sum_smul, Finset.smul_sum, mul_smul]
  exact Finset.sum_comm

private theorem action_det {I : Type*} [Fintype I] [DecidableEq I]
    (M : Matrix I I ℤ) (v : I → A) (hv : action M v = 0) : M.det • v = 0 := by
  have h := congrArg (action M.adjugate) hv
  rw [← action_mul, Matrix.adjugate_mul] at h
  funext i
  have hi := congrFun h i
  change ∑ j, ((M.det • (1 : Matrix I I ℤ)) i j) • v j = _ at hi
  simpa only [Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, mul_smul,
    ite_smul, smul_ite, one_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ,
    ite_true, action, Fintype.linearCombination_apply, Pi.zero_apply, smul_zero, Finset.sum_const_zero, Pi.smul_apply] using hi

private theorem lap_torsion {p q : ℕ} (v : Site p q → A) (hv : ∀ i, lap v i = 0) :
    ∃ N : ℕ, 0 < N ∧ N • v = 0 := by
  have hd := lap_det_ne_zero p q
  have hz : (lapMatrix p q).det • v = 0 := by
    apply action_det
    funext i
    exact (matrix_action v i).trans (hv i)
  refine ⟨(lapMatrix p q).det.natAbs, Int.natAbs_pos.mpr hd, ?_⟩
  exact natAbs_nsmul_eq_zero.mpr hz

end D5.S3.StatisticalMechanics.Sandpiles.ShkolnikovSandpileLimitDivisible



namespace D5.S3.StatisticalMechanics.Sandpiles.ShkolnikovSandpileLimitDivisible
variable {A : Type*} [AddCommGroup A]

private def rowSpace (p : ℕ) (A : Type*) [AddCommGroup A] : AddSubgroup (ℤ → A) :=
  AddSubgroup.pi {x : ℤ | ¬ (0 < x ∧ x < p)} (fun _ => (⊥ : AddSubgroup A))

private abbrev Row (p : ℕ) (A : Type*) [AddCommGroup A] := rowSpace p A

@[simp] private theorem row_out {p : ℕ} (u : Row p A) (x : ℤ) (hx : ¬ (0 < x ∧ x < p)) : u.val x = 0 :=
  u.property x hx

private instance finiteRow (p : ℕ) [Finite A] : Finite (Row p A) := by
  apply Finite.of_injective (fun u : Row p A => fun i : Fin p => u.val (i.val:ℤ))
  intro u v h
  apply Subtype.ext
  funext x
  by_cases hx : 0 < x ∧ x < p
  · let i : Fin p := ⟨x.toNat, by omega⟩
    have hh := congrFun h i
    change u.val (x.toNat:ℤ) = v.val (x.toNat:ℤ) at hh
    simpa only [Int.toNat_of_nonneg hx.1.le] using hh
  · rw [row_out u x hx,row_out v x hx]

private noncomputable def rowB (p : ℕ) : Row p A →+ Row p A where
  toFun u := ⟨fun x => if 0 < x ∧ x < p then (4:ℤ) • u.val x - u.val (x-1) - u.val (x+1) else 0,
    by
      intro x hx
      change ¬ (0 < x ∧ x < p) at hx
      change (if 0 < x ∧ x < p then _ else 0) = 0
      exact if_neg hx⟩
  map_zero' := by apply Subtype.ext; funext x; simp
  map_add' u v := by
    apply Subtype.ext; funext x
    dsimp
    split_ifs
    · simp only [zsmul_add]; abel
    · simp

end D5.S3.StatisticalMechanics.Sandpiles.ShkolnikovSandpileLimitDivisible


/-! Binding conventions for M. Shkolnikov, "Algebraic Limits of Sandpiles", arXiv:2506.09912v3 (2 September 2025).

* Remark 1: `G(Γ) ≅ Ker(Δ ⊗ ℝ/ℤ)`, "the group of 'strictly harmonic' circle-valued functions on the graph"; for
  `Γ(p, q)`, the lattice points of the open rectangle `(0, p) × (0, q)` with the wired exterior, these are the
  functions `f` vanishing outside `Γ(p, q)` with `4 f(x, y) = f(x−1, y) + f(x+1, y) + f(x, y−1) + f(x, y+1)` on `Γ(p, q)`.
* Section 3: "for any pair (m, n) of positive integers, the monomorphism from G(Γ(p, q)) to G(Γ(mp, nq)) is given by
  assigning to ϕ (x, y) ∈ Γ(mp, nq) ↦ (−1)^{⌊x/p⌋+⌊y/q⌋} ϕ(µ⁻¹_{p,⌊x/p⌋}(x), µ⁻¹_{q,⌊y/q⌋}(y)), where … ϕ is extended
  by 0 outside Γ(p, q), and µ_{p,k} : [0, p] → [kp, (k + 1)p] is given by µ_{p,k}(x) = kp + x if k even, (k + 1)p − x
  otherwise."
* Section 3, after Proposition 5: the direct limit of these groups embeds in the inverse limit of extended sandpile
  groups; "one may expect that it is a rational subtorus or a divisible group". -/

namespace D5.S3.StatisticalMechanics.Sandpiles.ShkolnikovSandpileLimitDivisible

/-- The circle `ℝ/ℤ`. -/
abbrev T := AddCircle (1 : ℝ)

/-- `(x, y) ∈ Γ(p, q)`: a lattice point of the open rectangle `(0, p) × (0, q)`. -/
def InRect (p q : ℕ) (z : ℤ × ℤ) : Prop := 0 < z.1 ∧ z.1 < p ∧ 0 < z.2 ∧ z.2 < q

/-- Remark 1: `f` is an element of `G(Γ(p, q))`, a strictly harmonic circle-valued function extended by `0`. -/
def IsSandpile (p q : ℕ) (f : ℤ × ℤ → T) : Prop :=
  (∀ z, ¬ InRect p q z → f z = 0) ∧
    ∀ z, InRect p q z → (4 : ℤ) • f z = f (z.1 - 1, z.2) + f (z.1 + 1, z.2) + f (z.1, z.2 - 1) + f (z.1, z.2 + 1)

/-- `µ⁻¹_{p,⌊x/p⌋}(x)`: `x − kp` on an even tile `k = ⌊x/p⌋`, `(k + 1)p − x` on an odd tile. -/
def unfold (p : ℕ) (x : ℤ) : ℤ :=
  if (x / p) % 2 = 0 then x - (x / p) * p else (x / p + 1) * p - x

open Classical in
/-- Section 3: the monomorphism `G(Γ(p, q)) → G(Γ(mp, nq))`. -/
noncomputable def embed (p q m n : ℕ) (φ : ℤ × ℤ → T) : ℤ × ℤ → T := fun z =>
  if InRect (m * p) (n * q) z then
    ((-1 : ℤ) ^ (z.1 / p + z.2 / q).toNat) • φ (unfold p z.1, unfold q z.2)
  else 0

/-- Divisibility of the direct limit: every element of every `G(Γ(p, q))` has, for every `k ≥ 1`, a `k`-th root at
some later stage `G(Γ(mp, nq))` of the direct system. -/
def claim : Prop :=
  ∀ p q : ℕ, 1 ≤ p → 1 ≤ q → ∀ f : ℤ × ℤ → T, IsSandpile p q f → ∀ k : ℕ, 1 ≤ k →
    ∃ m n : ℕ, 1 ≤ m ∧ 1 ≤ n ∧ ∃ g : ℤ × ℤ → T, IsSandpile (m * p) (n * q) g ∧ k • g = embed p q m n f

end D5.S3.StatisticalMechanics.Sandpiles.ShkolnikovSandpileLimitDivisible

namespace D5.S3.StatisticalMechanics.Sandpiles.ShkolnikovSandpileLimitDivisible

private noncomputable def frow {p q : ℕ} {f : ℤ × ℤ → T} (hf : IsSandpile p q f) (y : ℕ) : Row p T :=
  ⟨fun x => f (x,y), by intro x hx; apply hf.1; intro h; exact hx ⟨h.1,h.2.1⟩⟩

private theorem frow_zero {p q : ℕ} {f : ℤ × ℤ → T} (hf : IsSandpile p q f) : frow hf 0 = 0 := by
  apply Subtype.ext; funext x
  apply hf.1
  simp [InRect]

private theorem frow_end {p q : ℕ} {f : ℤ × ℤ → T} (hf : IsSandpile p q f) : frow hf q = 0 := by
  apply Subtype.ext; funext x
  apply hf.1
  simp [InRect]

private theorem frow_rec {p q : ℕ} {f : ℤ × ℤ → T} (hf : IsSandpile p q f) (n : ℕ) (hn : n+2 ≤ q) :
    frow hf (n+2) = rowB p (frow hf (n+1)) - frow hf n := by
  apply Subtype.ext; funext x
  by_cases hx : 0 < x ∧ x < p
  · have h := hf.2 (x,(n+1:ℕ)) ⟨hx.1,hx.2,by omega,by omega⟩
    change f (x,((n+2:ℕ):ℤ)) =
      (if 0<x ∧ x<p then (4:ℤ) • f (x,((n+1:ℕ):ℤ)) - f (x-1,((n+1:ℕ):ℤ)) - f (x+1,((n+1:ℕ):ℤ)) else 0) - f (x,(n:ℤ))
    rw [if_pos hx]
    have e0 : ((n+1:ℕ):ℤ)-1=n := by exact Int.sub_eq_iff_eq_add.mpr rfl
    have e1 : ((n+1:ℕ):ℤ)+1=((n+2:ℕ):ℤ) := by exact Int.ofNat_add_one_out (n + 1)
    rw [e0,e1] at h
    rw [h]
    abel
  · change (frow hf (n+2)).val x = (rowB p (frow hf (n+1)) - frow hf n).val x
    rw [row_out _ x hx,row_out _ x hx]

private theorem rows_frow {p q : ℕ} {f : ℤ × ℤ → T} (hf : IsSandpile p q f) (n : ℕ) (hn : n ≤ q) :
    rows (rowB p) (frow hf 1) n = frow hf n := by
  have h := rows_eq_upto (rowB p) (frow hf) q (frow_zero hf) (frow_rec hf) n hn
  exact h

private theorem rows_closed {p q : ℕ} {f : ℤ × ℤ → T} (hf : IsSandpile p q f) :
    rows (rowB p) (frow hf 1) q = 0 := by rw [rows_frow hf q (le_refl q),frow_end]

private theorem f_torsion {p q : ℕ} {f : ℤ × ℤ → T} (hf : IsSandpile p q f) :
    ∃ N : ℕ, 0 < N ∧ ∀ z, N • f z = 0 := by
  let v : Site p q → T := fun i => f i.val
  have hext : ∀ z, ext0 v z = f z := by
    intro z
    simp only [ext0_apply]
    split_ifs with h
    · rfl
    · exact (hf.1 z (by simpa only [InRect,Finset.mem_product,Finset.mem_Ioo,and_assoc] using h)).symm
  have hv : ∀ i, lap v i = 0 := by
    intro i
    have h := hf.2 i.val (by simpa only [InRect,Finset.mem_product,Finset.mem_Ioo,and_assoc] using i.property)
    simp only [lap,hext]
    change (4:ℤ) • f i.val - _ - _ - _ - _ = 0
    rw [h]
    abel
  obtain ⟨N,hN,hNv⟩ := lap_torsion v hv
  refine ⟨N,hN,fun z => ?_⟩
  by_cases hz : InRect p q z
  · exact congrFun hNv ⟨z,by simpa only [InRect,Finset.mem_product,Finset.mem_Ioo,and_assoc] using hz⟩
  · simp [hf.1 z hz]

private noncomputable def rowMap {A C : Type*} [AddCommGroup A] [AddCommGroup C] (p : ℕ) (F : A →+ C) : Row p A →+ Row p C :=
  (AddMonoidHom.pi (fun x => F.comp
    ((Pi.evalAddMonoidHom (fun _ : ℤ => A) x).comp (rowSpace p A).subtype))).codRestrict
    (rowSpace p C) (by intro u x hx; simp [row_out u x hx])

private theorem rowMap_B {A C : Type*} [AddCommGroup A] [AddCommGroup C] (p : ℕ) (F : A →+ C) (u : Row p A) :
    rowMap p F (rowB p u) = rowB p (rowMap p F u) := by
  apply Subtype.ext; funext x
  change F (if 0 < x ∧ x < p then _ else 0) =
    (if 0 < x ∧ x < p then (4 : ℤ) • F (u.val x) - F (u.val (x-1)) -
      F (u.val (x+1)) else 0)
  split_ifs <;> simp only [map_sub, map_zsmul, map_zero]

end D5.S3.StatisticalMechanics.Sandpiles.ShkolnikovSandpileLimitDivisible


namespace D5.S3.StatisticalMechanics.Sandpiles.ShkolnikovSandpileLimitDivisible

private theorem unfold_nat (q n : ℕ) (hq : 0 < q) :
    unfold q (n:ℤ) = if (n/q)%2=0 then ((n%q:ℕ):ℤ) else ((q-n%q:ℕ):ℤ) := by
  have hr : n%q ≤ q := (Nat.mod_lt n hq).le
  have hn : (n:ℤ) = (n/q:ℕ)* (q:ℤ) + (n%q:ℕ) := by
    exact_mod_cast (Nat.div_add_mod' n q).symm
  have hpar : (((n/q:ℕ):ℤ)%2=0) ↔ (n/q)%2=0 := by omega
  unfold unfold
  rw [←Int.natCast_ediv]
  simp only [hpar]
  split_ifs with he
  · linarith
  · rw [Nat.cast_sub hr]
    linarith

private theorem rows_fold {p q : ℕ} (hq : 0 < q) {f : ℤ × ℤ → T} (hf : IsSandpile p q f) (n : ℕ) (x : ℤ) :
    (rows (rowB p) (frow hf 1) n).val x =
      ((-1:ℤ)^(n/q)) • f (x,unfold q (n:ℤ)) := by
  have hclosed := rows_closed hf
  have htile := rows_tile (q := q) (rowB p) (frow hf 1)
  have ht := htile hq hclosed (n/q) (n%q) (Nat.mod_lt n hq)
  rw [Nat.div_add_mod'] at ht
  rw [unfold_nat q n hq,neg_one_pow_eq_pow_mod_two]
  by_cases he : (n/q)%2=0
  · rw [if_pos he] at ht
    rw [if_pos he,he,pow_zero,one_zsmul,ht,rows_frow hf _ (Nat.mod_lt n hq).le]
    rfl
  · have ho : (n/q)%2=1 := by exact Nat.mod_two_ne_zero.mp he
    rw [if_neg he] at ht
    rw [if_neg he,ho,pow_one,neg_one_zsmul,ht,rows_frow hf _ (Nat.sub_le _ _)]
    rfl

private theorem embed_rows {p q n : ℕ} (hq : 0 < q) {f : ℤ × ℤ → T} (hf : IsSandpile p q f)
    (z : ℤ × ℤ) (hz : InRect p (n*q) z) :
    embed p q 1 n f z = (rows (rowB p) (frow hf 1) z.2.toNat).val z.1 := by
  have hxdiv : z.1 / (p:ℤ) = 0 := Int.ediv_eq_zero_of_lt hz.1.le hz.2.1
  have hxun : unfold p z.1 = z.1 := by simp [unfold,hxdiv]
  have hy : (z.2.toNat:ℤ)=z.2 := Int.toNat_of_nonneg hz.2.2.1.le
  rw [embed,if_pos (by simpa using hz),hxdiv,zero_add,hxun]
  rw [rows_fold hq hf]
  rw [hy]
  congr 1
  rw [←hy,←Int.natCast_ediv]
  simp only [Int.toNat_natCast]

end D5.S3.StatisticalMechanics.Sandpiles.ShkolnikovSandpileLimitDivisible


namespace D5.S3.StatisticalMechanics.Sandpiles.ShkolnikovSandpileLimitDivisible

private noncomputable def fromRows (p H : ℕ) (s : ℕ → Row p T) (z : ℤ × ℤ) : T :=
  if 0 < z.2 ∧ z.2 < H then (s z.2.toNat).val z.1 else 0

private theorem fromRows_eq {p H : ℕ} {s : ℕ → Row p T} (h0 : s 0 = 0) (hH : s H = 0)
    (x j : ℤ) (hj : 0 ≤ j ∧ j ≤ H) : fromRows p H s (x,j) = (s j.toNat).val x := by
  by_cases hi : 0 < j ∧ j < H
  · simp [fromRows,hi]
  · have hcase : j=0 ∨ j=H := by omega
    rcases hcase with rfl | rfl
    · simp [fromRows,h0]
    · simp [fromRows,hH]

private theorem fromRows_sandpile {p H : ℕ} (s : ℕ → Row p T) (h0 : s 0 = 0) (hH : s H = 0)
    (hs : ∀ n, s (n+2) = rowB p (s (n+1)) - s n) : IsSandpile p H (fromRows p H s) := by
  constructor
  · intro z hz
    by_cases hy : 0 < z.2 ∧ z.2 < H
    · have hx : ¬(0<z.1 ∧ z.1<p) := by intro hx; exact hz ⟨hx.1,hx.2,hy.1,hy.2⟩
      simp only [fromRows,if_pos hy,row_out _ _ hx]
    · simp [fromRows,hy]
  · intro z hz
    have hzpos : 0 < z.2 := hz.2.2.1
    have hzlt : z.2 < H := hz.2.2.2
    have hj : 0 ≤ z.2 ∧ z.2 ≤ H := ⟨hz.2.2.1.le,hz.2.2.2.le⟩
    rw [fromRows_eq h0 hH z.1 z.2 hj,
      fromRows_eq h0 hH (z.1-1) z.2 hj,fromRows_eq h0 hH (z.1+1) z.2 hj,
      fromRows_eq h0 hH z.1 (z.2-1) (by omega),fromRows_eq h0 hH z.1 (z.2+1) (by omega)]
    have hrec := congrArg (fun u : Row p T => u.val z.1) (hs (z.2.toNat-1))
    have e0 : z.2.toNat-1+1=z.2.toNat := by omega
    have e1 : z.2.toNat-1+2=(z.2+1).toNat := by omega
    have e2 : z.2.toNat-1=(z.2-1).toNat := by exact Eq.symm (Int.pred_toNat z.2)
    rw [e0,e1,e2] at hrec
    change (s (z.2+1).toNat).val z.1 =
      (if 0<z.1 ∧ z.1<p then (4:ℤ) • (s z.2.toNat).val z.1 - (s z.2.toNat).val (z.1-1) - (s z.2.toNat).val (z.1+1) else 0) - (s (z.2-1).toNat).val z.1 at hrec
    rw [if_pos ⟨hz.1,hz.2.1⟩] at hrec
    rw [hrec]
    abel

private theorem finite_row_lift {p q k : ℕ} {f : ℤ × ℤ → T} (hf : IsSandpile p q f) (hk : 0 < k) :
    ∃ P : ℕ, 0 < P ∧ ∃ s : ℕ → Row p T,
      s 0 = 0 ∧ s (P*q) = 0 ∧
      (∀ n, s (n+2) = rowB p (s (n+1)) - s n) ∧
      ∀ n, k • s n = rows (rowB p) (frow hf 1) n := by
  classical
  obtain ⟨N,hN,hfN⟩ := f_torsion hf
  let H : AddSubgroup T := (nsmulAddMonoidHom (α:=T) (k*N)).ker
  letI : Fintype H := (AddCircle.finite_torsion (1:ℝ) (Nat.mul_pos hk hN)).fintype
  have hroot : ∀ x : ℤ, ∃ a : T, k • a = f (x,1) := by
    intro x
    obtain ⟨a,ha⟩ := DivisibleBy.surjective_smul T ℤ (by exact_mod_cast hk.ne' : (k:ℤ) ≠ 0) (f (x,1))
    exact ⟨a,by simpa using ha⟩
  choose a ha using hroot
  have haN : ∀ x, (k*N) • a x = 0 := by
    intro x
    rw [mul_nsmul,ha,hfN]
  let aH : Row p H := ⟨fun x => if hx : 0<x ∧ x<p then ⟨a x,haN x⟩ else 0,
    by
      intro x hx
      change ¬ (0 < x ∧ x < p) at hx
      change (if hx : 0 < x ∧ x < p then (⟨a x, haN x⟩ : H) else 0) = 0
      exact dif_neg hx⟩
  let F : Row p H →+ Row p T := rowMap p H.subtype
  have hkinit : k • F aH = frow hf 1 := by
    apply Subtype.ext; funext x
    by_cases hx : 0<x ∧ x<p
    · change k • (if hx : 0<x ∧ x<p then (⟨a x,haN x⟩:H) else 0).val = f (x,1)
      simp only [dif_pos hx]
      exact ha x
    · change (k • F aH).val x = (frow hf 1).val x
      rw [row_out _ x hx,row_out _ x hx]
  obtain ⟨P,hP,hper⟩ := rows_period (rowB p : Row p H →+ Row p H) aH
  let s : ℕ → Row p T := fun n => F (rows (rowB p) aH n)
  refine ⟨P,hP,s,?_,?_,?_,?_⟩
  · change F (rows (rowB p) aH 0) = 0
    rw [rows_zero (rowB p) aH, map_zero]
  · have hmul := rows_period_mul (d := P) (rowB p) aH
    have hh := hmul hper 0 q
    have hh0 : rows (rowB p) aH (P*q) = 0 := by
      simpa only [Nat.zero_add, rows_zero] using hh
    change F (rows (rowB p) aH (P*q)) = 0
    rw [hh0, map_zero]
  · intro n
    dsimp [s]
    rw [rows_rec (rowB p) aH n,map_sub,rowMap_B]
  · intro n
    dsimp [s]
    have hmap := rows_map (rowB p) (rowB p) F
    rw [hmap (rowMap_B p H.subtype)]
    rw [← rows_nsmul (V := Row p T) (rowB (A := T) p) (F aH) k n,hkinit]

theorem result : ShkolnikovSandpileLimitDivisible.claim := by
  intro p q hp hq f hf k hk
  obtain ⟨P,hP,s,hs0,hsH,hsrec,hscale⟩ := finite_row_lift hf (by omega : 0 < k)
  refine ⟨1,P,by omega,by omega,fromRows p (P*q) s,?_,?_⟩
  · simpa using fromRows_sandpile s hs0 hsH hsrec
  · funext z
    by_cases hz : InRect p (P*q) z
    · have hj : 0 ≤ z.2 ∧ z.2 ≤ P*q := ⟨hz.2.2.1.le,hz.2.2.2.le⟩
      change k • fromRows p (P*q) s z = embed p q 1 P f z
      rw [fromRows_eq hs0 hsH z.1 z.2 hj,embed_rows (by omega) hf z hz]
      exact congrArg (fun u : Row p T => u.val z.1) (hscale z.2.toNat)
    · have hzero := (fromRows_sandpile s hs0 hsH hsrec).1 z hz
      simp only [Pi.smul_apply,hzero,smul_zero,embed]
      rw [if_neg (by simpa using hz)]

end D5.S3.StatisticalMechanics.Sandpiles.ShkolnikovSandpileLimitDivisible
