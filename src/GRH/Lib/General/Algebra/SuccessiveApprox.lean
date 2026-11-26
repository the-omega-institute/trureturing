import GRH.Lib.General.Algebra.AdicRingHomExt
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! General lemmas of commutative and general algebra (textbook or folklore).

This file: Successive approximation in adically complete modules; extracting the largest power of an
element. -/


open IsHausdorff AdicCompletion Submodule
variable {R R' N M} [CommRing R] [CommRing R'] [AddCommGroup N] [Module R N] [AddCommGroup M]
  [Module R' M] {π : R} {π' : R'}

instance [IsHausdorff (.span {π}) N] : Fact (shiftDiff N π).Injective := ⟨fun x y h ↦ funext
  (.span {π}) fun k m ↦ by induction k generalizing m <;> simp_all [Submodule.Quotient.eq,
  ← smul_sub, pow_succ', mul_smul, sub_eq_sub_iff_sub_eq_sub.1 congr($h m), smul_mem_smul]⟩

instance [IsAdicComplete (.span {π}) N] : Fact (shiftDiff N π).Surjective := ⟨fun y ↦
  (map_surjective_of_mkQ_comp_surjective (f := 1 - π • .funLeft _ _ .succ) (Quot.ind (⟨·,
  SModEq.sub_mem.2 (by simp [smul_mem_smul])⟩)) (of (.span {π}) _ y)).imp'
  ((ofLinearEquiv ..).symm ∘ ·.pi _ _) ((mk_surjective _ _).forall.2 fun x h ↦
  funext (of_injective (.span {π}) _ <| by simpa [shiftDiff] using! congr(pi _ _ $h ·)))⟩

/-- Successive approximation: let `shiftDiff` be surjective for π on N and injective for π' on M,
and f: N → M additive with f(πn) = π'f(n). If a set S ⊂ M lies in f(N) + π'S, then S lies in
f(N). -/
lemma mem_range_of_approx [s : Fact (shiftDiff N π).Surjective]
    [i : Fact (shiftDiff M π').Injective] (f : N →+ M) (hf : ∀ n, f (π • n) = π' • f n)
    {X : Type*} (g : X → M) (h : ∀ x, ∃ n y, g x = f n + π' • g y) x : ∃ n, f n = g x := by
  choose n y e using h
  exact (s.1 (n <| y^[·] x)).rec fun u h ↦ ⟨_, congrFun (@i.1 (f ∘ u) (g <| y^[·] x) (by
    grind [shiftDiff, =_ congrFun h, y.iterate_succ_apply'])) 0⟩

lemma exists_eq_pow_mul_of_not_forall_dvd (π x : R) (h : ¬∀ n, π ^ n ∣ x) : ∃ n c, x = π ^ n * c ∧
  ¬π ∣ c := ⟨_, (FiniteMultiplicity.not_iff_forall.not_right.2 h).exists_eq_pow_mul_and_not_dvd⟩
