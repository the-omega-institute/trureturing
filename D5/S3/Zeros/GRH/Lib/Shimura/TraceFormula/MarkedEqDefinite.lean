/- GID: D5/S3/Zeros/GRH/Lib/Shimura/TraceFormula/MarkedEqDefinite
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/Shimura/TraceFormula/MarkedEqDefinite
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.Shimura.TraceFormula.MarkedEqDefinite. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/Shimura/TraceFormula/MarkedEqDefinite.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.Shimura.HeckeTower.WildType
import D5.S3.Zeros.GRH.Lib.Shimura.Transfer.MarkedPairs
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Known result: the simple trace formula, with the Hecke trace on a definite group and the
vanishing of non-elliptic terms. Here the group is a definite unitary similitude group, the level is
neat, and finite sums over cosets replace Haar integrals. Non-elliptic terms cancel for a regular
test function with a cuspidal type at one split place (n odd), and such a function not killing a
given vector exists. Source: Dummigan, A simple trace formula for algebraic modular forms, Exp.
Math. 22 (2013); Arthur and Clozel, Simple algebras, base change and the advanced theory of the
trace formula (1989), ch. 1 §2, after Deligne and Kazhdan.

This file: Non-elliptic terms vanish for a cuspidal type, so marked and definite counts agree. -/

attribute [-instance] instCoeTCOfCoe
open Function NumberField Matrix Polynomial Set QuotientGroup MulAction Pointwise ConjAct Fintype
  IsCoprime IsIdempotentElem Multiplicative
attribute [local simp] mul_assoc mul_add add_mul sub_mul orbit mul_sub units_smul_def eq
  mul_self_mul SemiconjBy orbitRel_apply Quotient.eq aeval_self_charpoly

/-- Let Γ permute the blocks π p of a partition of X and act freely on the support of an
invariant function F. If F has finite support and sum zero on each block meeting its
support, its orbit sum is zero. -/
lemma finsum_orbits_eq_zero_of_blocks {Γ X} [Group Γ] [MulAction Γ X] {F : orbitRel.Quotient Γ
  X → ℂ} (π : X → _) (hm : ∀ p, p ∈ π p) (hπ : ∀ (z : Γ) {p q}, p ∈ π q → π (z • p) = z • π q) (h0 :
  ∀ s, F ⟦s⟧ ≠ 0 → stabilizer Γ s ≤ ⊥ ∧ (π s ∩ support (F ⟦·⟧)).Finite ∧ ∑ᶠ p ∈ π s, F ⟦p⟧ = 0) :
  ∑ᶠ c, F c = 0 := have m p q := Iff.intro (@hπ 1 p q) (by grind [one_smul])
  (finsum_def _).trans (dite_eq_right_iff.2 fun S : Set.Finite _ ↦
    Finset.sum_cancels_of_partition_cancels ((orbitRel ..).comap _) fun c l ↦ by
  obtain ⟨⟨_, T, h⟩, _⟩ := h0 c.out (by aesop), (hπ · <| hm ·)
  use (finsum_cond_eq_sum_of_cond_iff _ fun k ↦ by simpa [*, Quotient.mk_eq_iff_out] using!
    mem_orbit_symm).symm.trans
    (finsum_image_eq_zero_of_fibers T (⟦·⟧) (by rwa [finsum_mem_inter_support])
    fun p h ↦ by rw [← Nat.card_congr ((Equiv.Set.image (· • p) (stabilizer Γ (π c.out)) fun a b e ↦
    inv_mul_eq_one.1 ((h0 p h.2).1 (by simp [mul_smul, ← e]))).trans (Set.equivOfEq (by aesop)))]))

/-- Let E⁺ ≠ ℚ, n odd, 𝔑 neat, f a regular Hecke function of level K(𝔑), χ-eigen under left
translation by J at w₀ with χ cuspidal, both unweighted counts finite modulo GL_n(E). Then
for any weight w the marked and definite orbit sums agree.

Known result: Simple trace formula: Hecke trace on a definite group; non-elliptic terms vanish. -/
lemma sum_countTerm_marked_eq_definite {E n} [Field E] [Ψ : CMBase E] [Fintype n] {𝔑 : 𝓞 E} (hN :
  IsNeat n 𝔑) (hn : Odd (card n)) {f : heckeAlgebra n ℂ 𝔑} (hr : IsRegularHecke f) {w₀ J χ} (hχ :
  IsCuspidalType J χ) (hJ : ↑f ∈ fixedToEigen (levelGU n 𝔑) (conjAtSplit w₀) J χ) w (fin : ∀ ε,
  (countTerm ε f 1).support.Finite) : ∑ᶠ c, countTerm True f w c = ∑ᶠ c, countTerm False f w c := by
  let u P := ite (Irreducible P) 0 (w P)
  have z ε : finsum (countTerm ε f u) = 0
  choose q hq using fun P : (LocField w₀.1)[X] ↦ (dite _ (fun ⟨h, h', hu⟩ ↦ by
    obtain ⟨A, B, rfl, _⟩ := by simpa [irreducible_iff, hu] using h'
    have ⟨u, v, l⟩ := h.isCoprime; use u * A, ⟨-u * v, by grind⟩
    simp_all [← l, mul_left_iff, mul_right_iff, isCoprime_self]) (⟨0, by simp, ·.elim⟩) : ∃ p, P ∣
    p * p - p ∧ (P.Separable ∧ ¬Irreducible P ∧ ¬IsUnit P → ¬IsCoprime P (1 - p) ∧ ¬IsCoprime P p))
  let e g := (q (charpoly (n := n) g)).aeval g
  have he g : IsIdempotentElem (e g) := by simpa using! aeval_dvd g (hq g.charpoly).1
  let A g := MonoidHom.toHomUnits ⟨⟨(1 + e g * toAdd · * (1 - e g)), by simp⟩,
    by simp [add_assoc, he, -mul_sub]⟩
  let K := levelGU n 𝔑; let G (p : MarkedTriple K n) := dualComponent w₀ (γ p.2.1 p.1.out)
  let r p Y : MarkedTriple K n := (p.1.out * conjAtSplit w₀ (A (G p) Y), p.2)
  use finsum_orbits_eq_zero_of_blocks (range ∘ r) (fun _ ↦ ⟨1, congr(($(by simp), _))⟩) (by
    rintro z _ q ⟨m, rfl⟩; obtain ⟨k, hk : (z • r q m).1.out = _⟩ := mk_out_eq_mul K _
    erw [smul_set_range, ← ((mul_right_surjective m).comp (toPerm (β := Matrix ..)
      (toConjAct (A (G q) m * dualComponent w₀ k))).surjective).range_comp]
    use congr(range fun a ↦ ($(QuotientGroup.eq.2 ?_), _))
    conv in A (G q) _ => erw [map_mul, fun b g Y ↦ (by ext1; unfold A e; simp [↓aeval_smul,
     charpoly_mul_comm] : A g (ofAdd (toConjAct b • Y.toAdd)) = b * A (toConjAct b⁻¹ • g) Y * b⁻¹)]
    simp [G, hk, show (z • r q m).2.1 = _ * q.2.1 * _ by rfl,
      ← by simpa using conj_conjAtSplit (w := w₀) k.2.1]) fun s l ↦ ?_
  let g := G s; rw [← s.eta, ← s.1.out_eq, countTerm_mk, ite_ne_right_iff, mul_ne_zero_iff] at l
  have ⟨j, Y, hj, c⟩ := And.elim (hχ _ (he g)) (by
    apply ((hq g.1.charpoly).2 _).imp <;> simp +contextual [← isUnit_aeval_iff_isCoprime, e,
      not_imp_not]
    simp [g, G, isUnit_iff_degree_eq_zero, hn.pos.ne', -mul_assoc]
    erw [← coe_units_inv, charpoly_transpose, charpoly_map, charpoly_map, Polynomial.map_map]
    use (hr l.2.1).map, mt ((charpoly_monic _).irreducible_of_irreducible_map _)
      (l.2.2 <| by simp [u, ·]))
  have hF {a} : countTerm ε f u ⟦r s a⟧ = _ :=
    countTerm_mk.trans ((ite_eq_left (by simp [isSignedFrame_mul_iff 1, ratConj, l])).trans
      (congrArg
    (heckeCosetFn f ⟦·⟧ * _) (show _ = conjAtSplit _ ((A g a)⁻¹ * g * A g a) * _ by
    simpa [g, G] using
      eq_mul_of_mul_inv_eq (conj_conjAtSplit (heckeAlgebra.mem_GUPlus_of_ne_zero l.2.1).1 _))))
  have R : .ker (r s) = leftRel (K.comap ((conjAtSplit _).comp (A g))) := by
    ext; simp [r, MarkedTriple, QuotientGroup.eq, ↓leftRel_apply, g]
  refine ⟨fun z e ↦ hN.2 l.1 (by simpa [← QuotientGroup.eq] using ((Quotient.mk_smul_out
    ..).trans congr($e.1)).symm) ((ratConj_eigenReflection _).trans congr(eigenReflection _ $e.2.1 _)), ((finite_quotient_image_of_isCompact
    ((isOpen_comap_conjAtSplit hN.1).preimage (.of_coeHom_comp (.const_add (by fun_prop) 1)))
    ((isCompact_LocInt _).matrix.image_auto (ofAdd <| aeval · (q g.1.charpoly)))
    ).image (Quot.lift _ R.ge)).subset fun | _, ⟨⟨m, rfl⟩, h⟩ => ⟨_, ⟨_, ⟨_, (fun a k i j ↦
    mem_Ô.1 (k.2 j i) _ : ∀ a ∈ GUPlus E n, ↑(dualComponent w₀ a) ∈ _) _ (heckeAlgebra.mem_GUPlus_of_ne_zero (left_ne_zero_of_mul
    (h ∘ hF.trans))), rfl⟩, rfl⟩, congr((⟦_ * conjAtSplit _ $(Units.ext ?_)⟧, _))⟩, ?_⟩
  simp [A, -coe_units_inv, -mul_assoc, -mul_add, -mul_sub]
  erw [aeval_smul _ (toConjAct (A g m)⁻¹)]; simp +zetaDelta [he, ← map_inv]
  let a := (q g.1.charpoly).aeval (j * g).1
  have hj' : SemiconjBy (A g (ofAdd a)) (j * g) g := Units.ext (by
    have c : Commute _ (e g) := aeval_semiconj rfl _
    have ⟨s, t, d⟩ : SemiconjBy (e g) (e g) a ∧ SemiconjBy (1 - e g) a (e g) ∧
      Commute (j.1 * g.1) a := by and_intros <;> apply aeval_semiconj <;> simp [← hj, he, c.eq]
    simp [he] at s t; simp [A, ← s, ← d.eq]
    simp [← hj, he, c.eq, c.symm.left_comm, ← t]; abel)
  erw [Function.comp, mk_surjective.range_comp (Quot.lift _ R.ge), finsum_mem_range
    (by rwa [Setoid.lift_injective_iff_ker_eq_of_le])]
  use eq_zero_of_mul_eq_self_left (inv_ne_one.2 c) ((mul_finsum ..).trans (finsum_eq_of_bijective
    _ (toPerm (ofAdd a)).bijective (Quot.ind fun m ↦ congr(_ * $hF).trans (hF.trans ?_).symm)))
  simpa [← mul_assoc g, ← hj'.eq, ← (Units.ext hj : A g (ofAdd _) = _), ((Commute.all m _).map
    (A g)).inv_left.left_comm] using! congr($(hJ single_one_mem_levelSpace j⁻¹).coeff ⟦_⟧ * _)
  suffices finsum (countTerm True f (w - u)) = finsum (countTerm False f (w - u)) by
    simpa [finsum_countTerm_eq_sum (w - u), ← finsum_countTerm_eq_sum, *]
  let s μ ε w (i : n) : ℤˣ := ite (w = Ψ.v₀ → ε → i = μ) 1 (-1)
  choose e U H c he using exists_hasSignType_mul_iff (s · True) (by
    simp_all [s, Finset.prod_ite, prod_eq_single v₀, Finset.filter_ne', hn.tsub_odd]) _
  convert finsum_comp_equiv e with ⟨⟨x⟩, y, μ⟩
  erw [he, countTerm_mk, countTerm_mk]; simp [(c ..).inv_left.left_comm]; by_contra h
  obtain ⟨⟨ν, k⟩, _⟩ := (heckeAlgebra.mem_GUPlus_of_ne_zero (h <| by rw [·]; simp)).1,
    Nonempty.intro μ
  have B ε x j : IsSignedFrame x (eigenReflection ε y μ) ↔ HasSignType (s μ ε) ν y {m | ∃ c :
    (Ô ℚ)ˣ, m = finAdeleIncl ℚ E c • 1} x := exists_congr fun _ ↦
    (iff_and_self.2 (⟨by_contra (h <| by simp [u, ·]), k.1.ne', ·.similitude_and_root_norm j (by
    simp [ratConj_eigenReflection])⟩)).trans (and_congr_right' (by
    delta eigenReflection; congr!
    split_ifs <;> simp [s, apply_ite, Lagrange.sum_basis, (numberedRoots ..).injective, *]))
  simp_all [s, Pi.mul_def, (c ..).inv_left.left_comm]
