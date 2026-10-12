/- GID: D5/S3/Arith/FibonacciAtomic/Observer/NativeUniformResidualRealization
   generality: G
   mirror-B: none(waiver:unbounded-symbolic-proof)
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: One finite native residual tuple reflects equality at every atomic rank vector. -/

import D5.S3.Arith.FibonacciAtomic.Observer.NativePrefixIdentityReflection

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.Observer.NativeUniformResidualRealization

open GenealogicalFiberTransport (Source substitution)
open NativePrefixIdentityReflection

/-- Syntax weight counts ground mass and explicit pairs, never decorations. -/
def weight {ι : Type} : MixedExpr ι → Nat
  | .ground g => gamma g
  | .residual _ _ => 0
  | .pair A B => 1 + weight A + weight B

/-- Largest residual decoration, including zero for a closed expression. -/
def decoration {ι : Type} : MixedExpr ι → Nat
  | .ground _ => 0
  | .residual a _ => a
  | .pair A B => max (decoration A) (decoration B)

/-- The same finite code is used for the entire bounded syntax class. -/
def separator (m M d : Nat) (i : Fin m) : Source :=
  substitution^[i.val * (d + 1)] (comb (M+1))

private theorem separator_mass (m M d : Nat) (i : Fin m) :
    gamma (separator m M d i) = M+1 := by
  rw [separator, gamma_iterate, gamma_comb]

private theorem pair_mass_le (s t : Source) :
    gamma (.mul s t) ≤ 1 + gamma s + gamma t := by
  simp only [gamma]
  split <;> omega

private theorem closed_mass {ι : Type} (E : MixedExpr ι)
    (closed : active E = false) (z : ι → Source) :
    gamma (eval z E) ≤ weight E := by
  induction E with
  | ground g => exact Nat.le_refl _
  | residual a i => simp [active] at closed
  | pair A B ihA ihB =>
      have hc := Bool.or_eq_false_iff.mp closed
      have ha := ihA hc.1
      have hb := ihB hc.2
      exact (pair_mass_le _ _).trans (by change _ ≤ 1 + weight A + weight B; omega)

private theorem active_mass (m M d : Nat) (E : MixedExpr (Fin m))
    (live : active E = true) :
    M+1 ≤ gamma (eval (separator m M d) E) := by
  induction E with
  | ground g => simp [active] at live
  | residual a i => simp only [eval, gamma_iterate, separator_mass]; omega
  | pair A B ihA ihB =>
      rcases (show active A = true ∨ active B = true from by simpa [active] using live) with h | h
      · exact (ihA h).trans (gamma_parent _ _).1
      · exact (ihB h).trans (gamma_parent _ _).2

private theorem active_pair_mass (m M d : Nat) (A B : MixedExpr (Fin m))
    (live : active (.pair A B) = true) :
    M+2 ≤ gamma (eval (separator m M d) (.pair A B)) := by
  rcases (show active A = true ∨ active B = true from by simpa [active] using live) with h | h
  · have ha := active_mass m M d A h
    change _ ≤ gamma (.mul _ _)
    rw [gamma_pair _ _ (Or.inl (by omega))]
    omega
  · have hb := active_mass m M d B h
    change _ ≤ gamma (.mul _ _)
    rw [gamma_pair _ _ (Or.inr (by omega))]
    omega

private theorem closed_of_equal_active (m M d : Nat) (A B : MixedExpr (Fin m))
    (ha : weight A ≤ M) (hb : weight B ≤ M)
    (eq : eval (separator m M d) A = eval (separator m M d) B) :
    active A = false ↔ active B = false := by
  constructor
  · intro hc
    have bound := (closed_mass A hc (separator m M d)).trans ha
    by_contra hn
    have lower := active_mass m M d B (Bool.eq_true_of_not_eq_false hn)
    rw [eq] at bound
    omega
  · intro hc
    have bound := (closed_mass B hc (separator m M d)).trans hb
    by_contra hn
    have lower := active_mass m M d A (Bool.eq_true_of_not_eq_false hn)
    rw [eq] at lower
    omega

private theorem decoration_intervals {m d a b : Nat} (i j : Fin m)
    (ha : a ≤ d) (hb : b ≤ d)
    (eq : i.val * (d + 1) + a = j.val * (d + 1) + b) : i = j ∧ a = b := by
  have hab : a = b := by
    have he := congrArg (fun x => x % (d + 1)) eq
    simpa only [Nat.add_mod, Nat.mul_mod, Nat.mod_self, Nat.mul_zero,
      Nat.zero_mod, Nat.zero_add, Nat.mod_eq_of_lt (by omega : a < d+1),
      Nat.mod_eq_of_lt (by omega : b < d+1)] using he
  have hiv : i.val = j.val := by
    rw [hab] at eq
    exact Nat.eq_of_mul_eq_mul_right (by omega : 0 < d+1) (Nat.add_right_cancel eq)
  exact ⟨Fin.ext hiv,hab⟩

/-- Equality at one tuple reflects every equality in the bounded syntax class.
Closed native equalities are retained without requiring syntax equality. -/
theorem bounded_identity_reflection (m M d : Nat) (A B : MixedExpr (Fin m))
    (wa : weight A ≤ M) (wb : weight B ≤ M)
    (da : decoration A ≤ d) (db : decoration B ≤ d) :
    eval (separator m M d) A = eval (separator m M d) B ↔
      ∀ z : Fin m → Source, eval z A = eval z B := by
  constructor
  · intro eq
    induction A generalizing B with
    | ground g =>
        have closed := (closed_of_equal_active m M d (.ground g) B wa wb eq).mp rfl
        intro z
        rw [eval_closed B closed z (separator m M d)]
        exact eq
    | residual a i =>
        have live : active B = true := by
          apply Bool.eq_true_of_not_eq_false
          intro hc
          have no := (closed_of_equal_active m M d (.residual a i) B wa wb eq).mpr hc
          cases no
        cases B with
        | ground g => cases live
        | residual b j =>
            have clock := congrArg kappa eq
            simp only [eval, separator, kappa_iterate] at clock
            have ab : i = j ∧ a = b := decoration_intervals i j da db (by omega)
            rcases ab with ⟨rfl,rfl⟩
            intro z; rfl
        | pair C D =>
            have lower := active_pair_mass m M d C D live
            have mass : gamma (eval (separator m M d) (.residual a i)) = M+1 := by
              simp only [eval, gamma_iterate, separator_mass]
            rw [← eq, mass] at lower
            omega
    | pair A C ihA ihC =>
        cases B with
        | ground g =>
            have closed := (closed_of_equal_active m M d (.pair A C) (.ground g) wa wb eq).mpr rfl
            intro z
            rw [eval_closed _ closed z (separator m M d)]
            exact eq
        | residual b j =>
            have live : active (.pair A C) = true := by
              apply Bool.eq_true_of_not_eq_false
              intro hc
              have no := (closed_of_equal_active m M d (.pair A C) (.residual b j) wa wb eq).mp hc
              cases no
            have lower := active_pair_mass m M d A C live
            have mass : gamma (eval (separator m M d) (.residual b j)) = M+1 := by
              simp only [eval, gamma_iterate, separator_mass]
            rw [eq, mass] at lower
            omega
        | pair B D =>
            change FreeMagma.mul _ _ = FreeMagma.mul _ _ at eq
            injection eq with ab cd
            have weights : weight A ≤ M ∧ weight C ≤ M ∧ weight B ≤ M ∧ weight D ≤ M := by
              simp only [weight] at wa wb
              omega
            have decs : decoration A ≤ d ∧ decoration C ≤ d ∧
                decoration B ≤ d ∧ decoration D ≤ d := by
              simp only [decoration, Nat.max_le] at da db
              exact ⟨da.1,da.2,db.1,db.2⟩
            intro z
            exact congrArg₂ FreeMagma.mul
              (ihA B weights.1 weights.2.2.1 decs.1 decs.2.2.1 ab z)
              (ihC D weights.2.1 weights.2.2.2 decs.2.1 decs.2.2.2 cd z)
  · intro universal
    exact universal (separator m M d)

/-- Rank names occupy the left summand; residual names occupy the right. -/
abbrev RankedExpr (k m : Nat) := MixedExpr (Fin k ⊕ Fin m)

/-- Ranked atoms are native iterates of alpha, at unbounded shared ranks. -/
def rankedEval {k m : Nat} (n : Fin k → Nat) (z : Fin m → Source)
    (E : RankedExpr k m) : Source :=
  eval (Sum.elim (fun j => substitution^[n j] (.of true)) z) E

/-- Fixing ranks changes only ranked leaves into actual native grounds. -/
def instantiate {k m : Nat} (n : Fin k → Nat) : RankedExpr k m → MixedExpr (Fin m)
  | .ground g => .ground g
  | .residual a (.inl j) => .ground (substitution^[n j + a] (.of true))
  | .residual a (.inr i) => .residual a i
  | .pair A B => .pair (instantiate n A) (instantiate n B)

/-- Only decorations on residual names enter the separator clock budget. -/
def rankedDecoration {k m : Nat} : RankedExpr k m → Nat
  | .ground _ => 0
  | .residual _ (.inl _) => 0
  | .residual a (.inr _) => a
  | .pair A B => max (rankedDecoration A) (rankedDecoration B)

theorem instantiate_eval {k m : Nat} (n : Fin k → Nat) (z : Fin m → Source)
    (E : RankedExpr k m) : eval z (instantiate n E) = rankedEval n z E := by
  induction E with
  | ground g => rfl
  | residual a i => cases i with
    | inl j =>
        change substitution^[n j + a] (.of true) = substitution^[a] (substitution^[n j] (.of true))
        rw [Nat.add_comm (n j) a,Function.iterate_add_apply]
    | inr i => rfl
  | pair A B ihA ihB => exact congrArg₂ FreeMagma.mul ihA ihB

private theorem instantiate_weight {k m : Nat} (n : Fin k → Nat) (E : RankedExpr k m) :
    weight (instantiate n E) = weight E := by
  induction E with
  | ground g => rfl
  | residual a i => cases i with
    | inl j => simp [instantiate, weight, gamma_iterate, gamma]
    | inr i => rfl
  | pair A B ihA ihB => simp only [instantiate, weight, ihA, ihB]

private theorem instantiate_decoration {k m : Nat} (n : Fin k → Nat) (E : RankedExpr k m) :
    decoration (instantiate n E) = rankedDecoration E := by
  induction E with
  | ground g => rfl
  | residual a i => cases i <;> rfl
  | pair A B ihA ihB => simp only [instantiate, decoration, rankedDecoration, ihA, ihB]

/-- Maximum of the side weights in a list; repetitions are retained. -/
def listWeight {ι : Type} : List (MixedExpr ι × MixedExpr ι) → Nat
  | [] => 0
  | p :: ps => max (max (weight p.1) (weight p.2)) (listWeight ps)

/-- Maximum of the residual decorations in the ranked input list. -/
def listDecoration {k m : Nat} : List (RankedExpr k m × RankedExpr k m) → Nat
  | [] => 0
  | p :: ps => max (max (rankedDecoration p.1) (rankedDecoration p.2)) (listDecoration ps)

/-- This tuple is determined before any rank vector is supplied. -/
def uniformSeparator {k m : Nat} (pairs : List (RankedExpr k m × RankedExpr k m)) :
    Fin m → Source := separator m (listWeight pairs) (listDecoration pairs)

private theorem member_bounds {k m : Nat} (pairs : List (RankedExpr k m × RankedExpr k m))
    (p : RankedExpr k m × RankedExpr k m) (hp : p ∈ pairs) :
    weight p.1 ≤ listWeight pairs ∧ weight p.2 ≤ listWeight pairs ∧
    rankedDecoration p.1 ≤ listDecoration pairs ∧ rankedDecoration p.2 ≤ listDecoration pairs := by
  induction pairs with
  | nil => simp at hp
  | cons q ps ih =>
      rcases List.mem_cons.mp hp with rfl | hp
      · simp only [listWeight, listDecoration]; omega
      · obtain ⟨wa,wb,da,db⟩ := ih hp
        simp only [listWeight, listDecoration]; omega

/-- One computable finite tuple reflects all listed equalities simultaneously,
for every unbounded atomic rank vector and every residual dimension. -/
theorem uniform_residual_reflection (k m : Nat)
    (pairs : List (RankedExpr k m × RankedExpr k m)) :
    ∀ (n : Fin k → Nat) (p : RankedExpr k m × RankedExpr k m), p ∈ pairs →
      (rankedEval n (uniformSeparator pairs) p.1 = rankedEval n (uniformSeparator pairs) p.2 ↔
        ∀ z : Fin m → Source, rankedEval n z p.1 = rankedEval n z p.2) := by
  intro n p hp
  obtain ⟨wa,wb,da,db⟩ := member_bounds pairs p hp
  have reflection := bounded_identity_reflection m (listWeight pairs) (listDecoration pairs)
    (instantiate n p.1) (instantiate n p.2)
    (by rwa [instantiate_weight]) (by rwa [instantiate_weight])
    (by rwa [instantiate_decoration]) (by rwa [instantiate_decoration])
  simpa only [instantiate_eval, uniformSeparator] using reflection

/-- A finite conjunction has one common finite completion at every feasible rank. -/
theorem simultaneous_completion (k m : Nat)
    (pairs : List (RankedExpr k m × RankedExpr k m)) (n : Fin k → Nat) :
    (∀ p ∈ pairs, ∃ z : Fin m → Source, rankedEval n z p.1 ≠ rankedEval n z p.2) ↔
      ∀ p ∈ pairs, rankedEval n (uniformSeparator pairs) p.1 ≠
        rankedEval n (uniformSeparator pairs) p.2 := by
  constructor
  · intro h p hp eq
    obtain ⟨z,hz⟩ := h p hp
    exact hz ((uniform_residual_reflection k m pairs n p hp).mp eq z)
  · intro h p hp
    exact ⟨uniformSeparator pairs,h p hp⟩

#print axioms bounded_identity_reflection
#print axioms uniform_residual_reflection
#print axioms simultaneous_completion

end D5.S3.Arith.FibonacciAtomic.Observer.NativeUniformResidualRealization
