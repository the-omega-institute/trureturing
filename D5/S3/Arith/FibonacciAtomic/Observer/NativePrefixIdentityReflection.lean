/- GID: D5/S3/Arith/FibonacciAtomic/Observer/NativePrefixIdentityReflection
   generality: G
   mirror-B: none(waiver:unbounded-symbolic-proof)
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Native identity reflection from independent live prefix frontiers. -/

import D5.S3.Arith.FibonacciAtomic.Observer.NativeDepthPatterns
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000

namespace D5.S3.Arith.FibonacciAtomic.Observer.NativePrefixIdentityReflection

open GenealogicalFiberTransport (Source substitution)
open NativeDepthPatterns (Pattern Frontier fill)
open scoped BigOperators

/-- Grounds and fixed native powers retain their original residual names. -/
inductive MixedExpr (ι : Type) where
  | ground : Source → MixedExpr ι
  | residual : Nat → ι → MixedExpr ι
  | pair : MixedExpr ι → MixedExpr ι → MixedExpr ι

/-- The unary operation is the interpreted native substitution. -/
def eval {ι : Type} (z : ι → Source) : MixedExpr ι → Source
  | .ground g => g
  | .residual a i => substitution^[a] (z i)
  | .pair A B => .mul (eval z A) (eval z B)

def atomicRank : Source → Option Nat
  | .of true => some 0
  | .of false => some 1
  | .mul s t =>
    match atomicRank s, atomicRank t with
    | some a, some b => if a = b + 1 then some (b + 2) else none
    | _, _ => none

private theorem atomicRank_substitution (t : Source) :
    atomicRank (substitution t) = (atomicRank t).map Nat.succ := by
  induction t with
  | of b => cases b <;> simp [substitution, atomicRank]
  | mul s t ihs iht =>
      change atomicRank (.mul (substitution s) (substitution t)) = _
      simp only [atomicRank, ihs, iht]
      cases hs : atomicRank s <;> cases ht : atomicRank t <;> simp only [Option.map_none, Option.map_some]
      rename_i a b
      have h : a + 1 = (b + 1) + 1 ↔ a = b + 1 := by omega
      simp only [Nat.succ_eq_add_one, h]
      split <;> simp <;> omega

def gamma : Source → Nat
  | .of _ => 0
  | .mul s t =>
      if (atomicRank (.mul s t)).isSome then 0 else 1 + gamma s + gamma t

theorem gamma_positive (t : Source) : 0 < gamma t ↔ atomicRank t = none := by
  cases t with
  | of b => cases b <;> simp [gamma, atomicRank]
  | mul s t => cases h : atomicRank (.mul s t) <;> simp [gamma, ← FreeMagma.mul_eq, h]

private theorem gamma_substitution (t : Source) : gamma (substitution t) = gamma t := by
  induction t with
  | of b => cases b <;> simp [substitution, gamma, atomicRank]
  | mul s t ihs iht =>
      change gamma (.mul (substitution s) (substitution t)) = _
      have hc := atomicRank_substitution (.mul s t)
      change atomicRank (.mul (substitution s) (substitution t)) = _ at hc
      simp only [gamma]
      rw [hc]
      cases atomicRank (.mul s t) <;> simp [ihs, iht]

theorem gamma_iterate (a : Nat) (t : Source) :
    gamma (substitution^[a] t) = gamma t := by
  induction a with
  | zero => rfl
  | succ a ih => rw [Function.iterate_succ_apply', gamma_substitution, ih]

theorem gamma_pair (s t : Source) (h : 0 < gamma s ∨ 0 < gamma t) :
    gamma (.mul s t) = 1 + gamma s + gamma t := by
  rcases h with h | h
  · have hs := (gamma_positive s).mp h
    simp [gamma, atomicRank, hs]
  · have ht := (gamma_positive t).mp h
    cases hs : atomicRank s <;> simp [gamma, atomicRank, ht, hs]

theorem gamma_parent (s t : Source) :
    gamma s ≤ gamma (.mul s t) ∧ gamma t ≤ gamma (.mul s t) := by
  by_cases h : 0 < gamma s ∨ 0 < gamma t
  · rw [gamma_pair s t h]; constructor <;> omega
  · have hs : gamma s = 0 := by omega
    have ht : gamma t = 0 := by omega
    rw [hs,ht]; exact ⟨Nat.zero_le _,Nat.zero_le _⟩

def kappa : Source → Nat
  | .of true => 0
  | .of false => 1
  | .mul _ t => 2 + kappa t

private theorem kappa_substitution (t : Source) : kappa (substitution t) = kappa t + 1 := by
  induction t with
  | of b => cases b <;> simp [substitution, kappa]
  | mul s t ihs iht =>
      change 2 + kappa (substitution t) = (2 + kappa t) + 1
      rw [iht]; omega

theorem kappa_iterate (a : Nat) (t : Source) :
    kappa (substitution^[a] t) = kappa t + a := by
  induction a with
  | zero => simp
  | succ a ih => rw [Function.iterate_succ_apply', kappa_substitution, ih]; omega

def comb : Nat → Source
  | 0 => .of true
  | r + 1 => .mul (comb r) (.of true)

theorem gamma_comb (r : Nat) : gamma (comb r) = r := by
  induction r with
  | zero => rfl
  | succ r ih =>
      cases r with
      | zero => simp [comb, gamma, atomicRank]
      | succ r => rw [comb, gamma_pair _ _ (Or.inl (by rw [ih]; omega)), ih]; simp [gamma]; omega

private def hasHole : {d : Nat} → Pattern d → Bool
  | 0, _ => true
  | _ + 1, .inl _ => false
  | _ + 1, .inr p => hasHole p.1 || hasHole p.2

private theorem hasHole_iff {d : Nat} (p : Pattern d) :
    hasHole p = true ↔ Nonempty (Frontier p) := by
  induction d with
  | zero => exact ⟨fun _ => ⟨()⟩,fun _ => rfl⟩
  | succ d ih => cases p with
    | inl b => simp [hasHole, Frontier]
    | inr p => simp [hasHole, Frontier, ih, nonempty_sum]

private theorem frontier_empty {d : Nat} (p : Pattern d) (h : hasHole p = false) :
    IsEmpty (Frontier p) := by
  refine ⟨fun x => ?_⟩
  have he := (hasHole_iff p).mpr ⟨x⟩
  rw [h] at he
  cases he

private theorem fill_closed {d : Nat} (p : Pattern d) (h : hasHole p = false)
    (w v : Frontier p → Source) : fill p w = fill p v := by
  letI := frontier_empty p h
  exact congrArg (fill p) (funext fun x => isEmptyElim x)

private def contextBase : {d : Nat} → Pattern d → Nat
  | 0, _ => 0
  | _ + 1, .inl _ => 0
  | d + 1, .inr p =>
      if hasHole p.1 || hasHole p.2 then 1 + contextBase p.1 + contextBase p.2
      else gamma (fill (d := d+1) (Sum.inr p) (fun _ => .of true))

private theorem context_mass {d : Nat} (p : Pattern d) :
    ∀ w : Frontier p → Source, (∀ x, 0 < gamma (w x)) →
      gamma (fill p w) = contextBase p + ∑ x, gamma (w x) ∧
      (hasHole p = true → 0 < gamma (fill p w)) := by
  induction d with
  | zero =>
      intro w hw
      change gamma (w ()) = 0 + ∑ x : Unit, gamma (w x) ∧ (true = true → 0 < gamma (w ()))
      simpa using hw ()
  | succ d ih => cases p with
    | inl b =>
        intro w hw
        change 0 = 0 + ∑ x : PEmpty, gamma (w x) ∧ (false = true → 0 < 0)
        simp
    | inr p =>
        letI : Fintype (Frontier (d := d+1) (Sum.inr p)) :=
          NativeDepthPatterns.frontierFintype (d := d+1) (Sum.inr p)
        intro w hw
        obtain ⟨hl, pl⟩ := ih p.1 (fun x => w (.inl x)) (fun x => hw (.inl x))
        obtain ⟨hr, pr⟩ := ih p.2 (fun x => w (.inr x)) (fun x => hw (.inr x))
        by_cases h : (hasHole p.1 || hasHole p.2) = true
        · have pos : 0 < gamma (fill p.1 (fun x => w (.inl x))) ∨
              0 < gamma (fill p.2 (fun x => w (.inr x))) := by
            rcases (show _ ∨ _ from by simpa using h) with h | h
            · exact Or.inl (pl h)
            · exact Or.inr (pr h)
          have add := gamma_pair _ _ pos
          change gamma (.mul _ _) = _ ∧ _
          rw [add]
          constructor
          · change 1 + gamma (fill p.1 (fun x => w (.inl x))) +
                gamma (fill p.2 (fun x => w (.inr x))) =
              contextBase (d := d+1) (Sum.inr p) +
                ∑ x : Frontier p.1 ⊕ Frontier p.2, gamma (w x)
            simp only [contextBase, h, if_true, Fintype.sum_sum_type]
            rw [hl, hr]; omega
          · intro _
            change 0 < gamma (.mul (fill p.1 (fun x => w (.inl x)))
              (fill p.2 (fun x => w (.inr x))))
            rcases pos with hp | hp
            · exact lt_of_lt_of_le hp (gamma_parent _ _).1
            · exact lt_of_lt_of_le hp (gamma_parent _ _).2
        · have hf : hasHole (d := d+1) (.inr p) = false := by
            simpa only [hasHole] using Bool.eq_false_of_not_eq_true h
          letI := frontier_empty (d := d+1) (.inr p) hf
          constructor
          · rw [fill_closed _ hf w (fun _ => .of true)]
            have hz : (∑ x : Frontier (d := d+1) (Sum.inr p), gamma (w x)) = 0 :=
              by
                apply Finset.sum_eq_zero
                intro x _
                exact isEmptyElim x
            rw [hz]
            simp only [contextBase, Bool.eq_false_of_not_eq_true h, Bool.false_eq_true, if_false, Nat.add_zero]
          · intro he; rw [hf] at he; cases he

private def occurs {m : Nat} : MixedExpr (Fin m) → Fin m → Nat
  | .ground _, _ => 0
  | .residual _ i, j => if i = j then 1 else 0
  | .pair A B, j => occurs A j + occurs B j

def active {ι : Type} : MixedExpr ι → Bool
  | .ground _ => false
  | .residual _ _ => true
  | .pair A B => active A || active B

theorem eval_closed {ι : Type} (E : MixedExpr ι) (h : active E = false)
    (z v : ι → Source) : eval z E = eval v E := by
  induction E with
  | ground g => rfl
  | residual a i => simp [active] at h
  | pair A B ihA ihB =>
      have hs := Bool.or_eq_false_iff.mp h
      exact congrArg₂ FreeMagma.mul (ihA hs.1) (ihB hs.2)

private theorem active_of_occurs {m : Nat} (E : MixedExpr (Fin m)) :
    active E = false ↔ ∀ i, occurs E i = 0 := by
  induction E with
  | ground g => simp [active, occurs]
  | residual a i =>
      simp only [active, Bool.true_eq_false, false_iff]
      intro h
      have hi := h i
      simp [occurs] at hi
  | pair A B ihA ihB =>
      simp only [active, Bool.or_eq_false_iff, ihA, ihB, occurs, Nat.add_eq_zero]
      exact ⟨fun h i => ⟨h.1 i,h.2 i⟩,fun h => ⟨fun i => (h i).1,fun i => (h i).2⟩⟩

private def base {ι : Type} : MixedExpr ι → Nat
  | .ground g => gamma g
  | .residual _ _ => 0
  | .pair A B => if active A || active B then 1 + base A + base B
      else gamma (.mul (eval (fun _ => .of true) A) (eval (fun _ => .of true) B))

private theorem expression_mass {m : Nat} (E : MixedExpr (Fin m))
    (z : Fin m → Source) (hz : ∀ i, 0 < gamma (z i)) :
    gamma (eval z E) = base E + ∑ i, occurs E i * gamma (z i) ∧
      (active E = true → 0 < gamma (eval z E)) := by
  induction E with
  | ground g => simp [eval, base, occurs, active]
  | residual a i => simpa [eval, base, occurs, active, gamma_iterate] using hz i
  | pair A B ihA ihB =>
      obtain ⟨ha, pa⟩ := ihA
      obtain ⟨hb, pb⟩ := ihB
      by_cases h : (active A || active B) = true
      · have hp : 0 < gamma (eval z A) ∨ 0 < gamma (eval z B) := by
          rcases (show _ ∨ _ from by simpa using h) with h | h
          · exact Or.inl (pa h)
          · exact Or.inr (pb h)
        change gamma (.mul _ _) = _ ∧ _
        rw [gamma_pair _ _ hp]
        constructor
        · simp only [base, h, if_true, occurs, Nat.add_mul, Finset.sum_add_distrib]
          rw [ha,hb]; omega
        · intro _
          change 0 < gamma (.mul (eval z A) (eval z B))
          rw [gamma_pair _ _ hp]; omega
      · have hf : active (.pair A B) = false := by
          exact Bool.eq_false_of_not_eq_true h
        have counts := (active_of_occurs (.pair A B)).mp hf
        constructor
        · rw [eval_closed _ hf z (fun _ => .of true)]
          simp [base, h, eval, counts]
        · intro he; rw [hf] at he; cases he

private theorem cylinder_mass {m : Nat} (d : Fin m → Nat)
    (p : (i : Fin m) → Pattern (d i)) (live : ∀ i, Nonempty (Frontier (p i)))
    (E : MixedExpr (Fin m)) (w : (i : Fin m) → Frontier (p i) → Source)
    (hw : ∀ i x, 0 < gamma (w i x)) :
    gamma (eval (fun i => fill (p i) (w i)) E) =
      base E + ∑ i, occurs E i * (contextBase (p i) + ∑ x, gamma (w i x)) := by
  have hm := fun i => context_mass (p i) (w i) (hw i)
  have hz : ∀ i, 0 < gamma (fill (p i) (w i)) :=
    fun i => (hm i).2 ((hasHole_iff (p i)).mpr (live i))
  rw [(expression_mass E _ hz).1]
  congr 1
  exact Finset.sum_congr rfl (fun i _ => congrArg (fun n => occurs E i * n) (hm i).1)

private theorem delta_sum {m : Nat} (d : Fin m → Nat)
    (p : (i : Fin m) → Pattern (d i)) (f : Fin m → Nat)
    (i : Fin m) (x : Frontier (p i)) :
    (∑ j, f j * ∑ y : Frontier (p j),
      if (⟨j,y⟩ : (j : Fin m) × Frontier (p j)) = ⟨i,x⟩ then 1 else 0) = f i := by
  classical
  calc
    _ = ∑ j, ∑ y : Frontier (p j), f j *
        (if (⟨j,y⟩ : (j : Fin m) × Frontier (p j)) = ⟨i,x⟩ then 1 else 0) := by
          simp only [Finset.mul_sum]
    _ = ∑ y : (j : Fin m) × Frontier (p j), f y.1 *
        (if y = ⟨i,x⟩ then 1 else 0) := (Fintype.sum_sigma (fun y : (j : Fin m) × Frontier (p j) =>
          f y.1 * (if y = ⟨i,x⟩ then 1 else 0))).symm
    _ = f i := by simp

private theorem mass_growth {m : Nat} (d : Fin m → Nat)
    (p : (i : Fin m) → Pattern (d i)) (f : Fin m → Nat)
    (b : Nat) (i : Fin m) (x : Frontier (p i)) :
    b + (∑ j, f j * (contextBase (p j) +
      ∑ y : Frontier (p j), (1 +
        if (⟨j,y⟩ : (j : Fin m) × Frontier (p j)) = ⟨i,x⟩ then 1 else 0))) =
    (b + ∑ j, f j * (contextBase (p j) + Fintype.card (Frontier (p j)))) + f i := by
  classical
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, Nat.cast_id, Nat.mul_one]
  simp_rw [← Nat.add_assoc, Nat.mul_add]
  rw [Finset.sum_add_distrib, delta_sum]
  omega

private theorem cylinder_coefficients {m : Nat} (d : Fin m → Nat)
    (p : (i : Fin m) → Pattern (d i)) (live : ∀ i, Nonempty (Frontier (p i)))
    (A B : MixedExpr (Fin m))
    (h : ∀ w : (i : Fin m) → Frontier (p i) → Source,
      eval (fun i => fill (p i) (w i)) A = eval (fun i => fill (p i) (w i)) B) :
    (∀ i, occurs A i = occurs B i) ∧ base A = base B := by
  classical
  let w₀ : (i : Fin m) → Frontier (p i) → Source := fun _ _ => comb 1
  have positive₀ : ∀ i x, 0 < gamma (w₀ i x) := by
    intro i x; simp [w₀, gamma_comb]
  have equal₀ := congrArg gamma (h w₀)
  rw [cylinder_mass d p live A w₀ positive₀,
      cylinder_mass d p live B w₀ positive₀] at equal₀
  simp only [w₀, gamma_comb, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, Nat.cast_id, Nat.mul_one] at equal₀
  have counts : ∀ i, occurs A i = occurs B i := by
    intro i
    obtain ⟨x⟩ := live i
    let w₁ : (j : Fin m) → Frontier (p j) → Source := fun j y => comb
      (1 + if (⟨j,y⟩ : (j : Fin m) × Frontier (p j)) = ⟨i,x⟩ then 1 else 0)
    have positive₁ : ∀ j y, 0 < gamma (w₁ j y) := by
      intro j y; simp only [w₁, gamma_comb]; omega
    have equal₁ := congrArg gamma (h w₁)
    rw [cylinder_mass d p live A w₁ positive₁,
        cylinder_mass d p live B w₁ positive₁] at equal₁
    simp only [w₁, gamma_comb] at equal₁
    rw [mass_growth, mass_growth, equal₀] at equal₁
    exact Nat.add_left_cancel equal₁
  refine ⟨counts, ?_⟩
  have hs : (∑ i, occurs A i * (contextBase (p i) + Fintype.card (Frontier (p i)))) =
      ∑ i, occurs B i * (contextBase (p i) + Fintype.card (Frontier (p i))) := by
    exact Finset.sum_congr rfl (fun i _ => congrArg (fun n => n * _) (counts i))
  rw [hs] at equal₀
  exact Nat.add_right_cancel equal₀

/-- Equality on the entire independent live-frontier cylinder reflects to
all finite source valuations, including residual dimension zero. -/
theorem prefix_identity_reflection
    (m : Nat) (d : Fin m → Nat) (p : (i : Fin m) → Pattern (d i))
    (live : ∀ i, Nonempty (Frontier (p i))) (A B : MixedExpr (Fin m))
    (on_cylinder : ∀ w : (i : Fin m) → Frontier (p i) → Source,
      eval (fun i => fill (p i) (w i)) A =
      eval (fun i => fill (p i) (w i)) B) :
    ∀ z : Fin m → Source, eval z A = eval z B := by
  classical
  induction A generalizing B with
  | ground g =>
      obtain ⟨counts, _⟩ := cylinder_coefficients d p live (.ground g) B on_cylinder
      have closed : active B = false := (active_of_occurs B).mpr (fun i => (counts i).symm)
      intro z
      rw [eval_closed B closed z (fun i => fill (p i) (fun _ => .of true))]
      exact on_cylinder (fun _ _ => .of true)
  | residual a i =>
      obtain ⟨counts, bases⟩ := cylinder_coefficients d p live (.residual a i) B on_cylinder
      cases B with
      | ground g =>
          have no := counts i
          simp [occurs] at no
      | residual b j =>
          have ij : i = j := by
            by_contra hij
            have no := counts i
            simp [occurs, hij, Ne.symm hij] at no
          subst j
          have clock := congrArg kappa (on_cylinder (fun _ _ => .of true))
          simp only [eval, kappa_iterate] at clock
          have ab : a = b := by omega
          subst b
          intro z; rfl
      | pair C D =>
          have liveB : active (.pair C D) = true := by
            apply Bool.eq_true_of_not_eq_false
            intro hf
            have no := (active_of_occurs (.pair C D)).mp hf i
            have ci := counts i
            simp only [occurs, if_pos rfl, ite_true] at ci no
            omega
          have pb : 1 ≤ base (.pair C D) := by
            change 1 ≤ if active C || active D then _ else _
            change (active C || active D) = true at liveB
            rw [liveB]; simp; omega
          change 0 = base (.pair C D) at bases
          omega
  | pair A₁ A₂ ih₁ ih₂ =>
      cases B with
      | ground g =>
          obtain ⟨counts, _⟩ := cylinder_coefficients d p live (.pair A₁ A₂) (.ground g) on_cylinder
          have closed : active (.pair A₁ A₂) = false :=
            (active_of_occurs (.pair A₁ A₂)).mpr counts
          intro z
          rw [eval_closed _ closed z (fun i => fill (p i) (fun _ => .of true))]
          exact on_cylinder (fun _ _ => .of true)
      | residual a i =>
          obtain ⟨counts, bases⟩ := cylinder_coefficients d p live (.pair A₁ A₂) (.residual a i) on_cylinder
          have liveA : active (.pair A₁ A₂) = true := by
            apply Bool.eq_true_of_not_eq_false
            intro hf
            have no := (active_of_occurs (.pair A₁ A₂)).mp hf i
            have ci := counts i
            simp only [occurs, if_pos rfl, ite_true] at ci no
            omega
          have pa : 1 ≤ base (.pair A₁ A₂) := by
            change 1 ≤ if active A₁ || active A₂ then _ else _
            change (active A₁ || active A₂) = true at liveA
            rw [liveA]; simp; omega
          change base (.pair A₁ A₂) = 0 at bases
          omega
      | pair B₁ B₂ =>
          have children (w : (i : Fin m) → Frontier (p i) → Source) :
              eval (fun i => fill (p i) (w i)) A₁ = eval (fun i => fill (p i) (w i)) B₁ ∧
              eval (fun i => fill (p i) (w i)) A₂ = eval (fun i => fill (p i) (w i)) B₂ := by
            have h := on_cylinder w
            change FreeMagma.mul _ _ = FreeMagma.mul _ _ at h
            injection h with hl hr
            exact ⟨hl,hr⟩
          intro z
          exact congrArg₂ FreeMagma.mul (ih₁ B₁ (fun w => (children w).1) z)
            (ih₂ B₂ (fun w => (children w).2) z)

#print axioms prefix_identity_reflection

end D5.S3.Arith.FibonacciAtomic.Observer.NativePrefixIdentityReflection
