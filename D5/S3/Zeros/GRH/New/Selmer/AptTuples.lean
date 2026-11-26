/- GID: D5/S3/Zeros/GRH/New/Selmer/AptTuples
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/New/Selmer/AptTuples
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module New.Selmer.AptTuples. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/New/Selmer/AptTuples.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.New.Selmer.AptTupleDefs
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Set-up for this proof: size bookkeeping for the data of this proof.

Set-up for this proof: records of the data and parameters of this proof, names for its objects.

This file: Divisibility and counting bookkeeping at the level; lattice versus representation
dictionary. Basic properties of apt label tuples and their idempotents; a place off the level. -/

open Data Finset Fint Gf LinearMap Matrix NeZero

variable {P} (D : Data P) (ℓ : ℕ) [ThePrime ℓ]

/-- For 1 ≤ d ≤ rt, g_i^d − 1 divides `Data.chosenGroupOrder`. -/
lemma g_pow_sub_one_dvd_chosenGroupOrder {i d} (hd : d ∈ Set.Icc 1 (D.r * D.t)) :
  D.g i ^ d - 1 ∣ D.chosenGroupOrder := by
  grw [← D.card_GL_dvd_chosenGroupOrder (card_fin d ▸ hd.2), Nat.card_pi,
    ← dvd_prod_of_mem _ (mem_univ ⟨i, D.chosenEquiv i 1⟩),
    Subsingleton.elim (Classical.decEq _), card_GL_field, ← dvd_prod_of_mem _ (mem_univ ⟨0, hd.1⟩)]
  grind [chosen, Fintype.card_eq_nat_card, card_ResField, q_eq_g, dvd_rfl]

/-- For each of the two primes g_i and each 1 ≤ d ≤ rt, the ℓ-adic valuation of g_i^d − 1 is at
most `crudeUnit`. -/
lemma ellVal_le_crudeUnit i {d} (h : d ∈ Set.Icc 1 (D.r * D.t)) : @ellVal ℓ _ (D.g i ^ d - 1) ≤
  crudeUnit ℓ D := by simpa [pos, crudeUnit, ellVal_natCast,
  ne] using le_add_right (dvd_iff_ellVal_le.1 (g_pow_sub_one_dvd_chosenGroupOrder D h).natCast)

lemma card_le_of_subset_placesAboveG {T : Finset (FinPlace D.E)} (s : ↑T ⊆ placesAboveG D) :
    #T ≤ 4 * D.f := (univ.card_le_card_of_surjOn (D.chosen ⊕ᵥ star ∘ D.chosen) (s.trans fun _ ⟨_,
  a⟩ ↦ by simp [Set.range_comp, range_chosen, D.isChosen_star_iff a, em])).trans
  (by simp +arith [card_chosenPlace])

lemma exists_chosen_notMem_placesDividing :
    ∃ w i, D.IsChosen w ∧ w ∈ placesAboveG D \ placesDividing _ ℓ ∧ w.q = D.g i :=
  (D.g_injective.exists_ne ℓ).elim fun i h ↦ ⟨_, i, (D.chosenEquiv i 1).2.imp_right fun b ↦
  ⟨⟨⟨i, b⟩, h ∘ (FinPlace.charP_quotient _ b).eq _ ∘ FinPlace.charP_quotient _⟩, D.q_eq_g b⟩⟩

variable {D ℓ} {n} [Fintype n] {O : CoeffRing ℓ} {R} {u : AbsGal D →* Matrix n n O} (h :
  IsLatticeIn R u)

include h in
/-- If u is a lattice in R over O, some injective O-algebra map F from matrices over O to
matrices over ℚ̄_ℓ sends u(g) to R(g) and preserves determinants and traces. -/
lemma IsLatticeIn.exists_algHom : ∃ F : _ →ₐ[O] Matrix n n _, (⇑F).Injective ∧ (∀ g, F (u g) =
  R g) ∧ ∀ A, (F A).det = A.det.1 ∧ (F A).trace = A.trace := h.elim fun (P : ConjAct _) h ↦
  ⟨(MulSemiringAction.toAlgHom O _ P).comp (Algebra.ofId ..).mapMatrix, fun _ ↦ by
  simp [smul_left_cancel_iff, ← ext_iff], (eq_inv_smul_iff.1 <| h · |>.symm),
  fun A ↦ by erw [det_units_conj, trace_units_conj]; simp [Matrix.trace, det_apply]⟩

lemma IsLatticeIn.continuous (h : IsLatticeIn R u) (_ : Continuous R) : Continuous u :=
    Topology.IsInducing.subtypeVal.matrix_map.continuous_iff.2 (.congr (by fun_prop) h.choose_spec)

lemma IsLatticeIn.eq_one (h : IsLatticeIn R u) {g} (e : R g = 1) : u g = 1 :=
  h.exists_algHom.elim (by aesop)

lemma IsLatticeIn.trace_eq (h : IsLatticeIn R u) g : (u g).trace.1 = (R g).1.trace :=
  h.exists_algHom.elim (by grind)

variable {r} {n : Type} [Fintype r] [Fintype n] {O : AuxPair D.E r n} {c : (i : O.ChosenIndex) →
  Polynomial (ResField (O.chosenPlace i))} {ϑ y w} (hw : _ ≠ w) (hS : w ∉ O.places.conjClosure)

namespace IsApt

lemma card_le : IsApt O c ϑ → Fintype.card n ≤ 2 * D.n D.m := by
  grind [IsApt, Data.n, mul_le_mul_left D.le_m D.t]

lemma isSymmetric_tupleProj : (tupleProj O c).IsSymmetric :=
  O.innerAt_groupAlgAction (isCentralProj_tupleIdem _) _

lemma tupleProj_eq_self_of_mem_range : y ∈ (tupleProj O c).range → tupleProj O c y = y :=
  ((isCentralProj_tupleIdem _).1.map _).mem_range_iff.1

lemma range_tupleProj_mem_invtSubmodule X : (tupleProj O c).range ∈ (O.heckePolyOnForms hw hS
  X).invtSubmodule := O.range_groupAlgAction_mem_invtSubmodule fun _ _ ↦ (map_smul ..).trans
  (congrArg _ (map_heckePolyOp (algFormRep _ _ _) X fun _ h ↦ by rw [← Module.End.mul_apply,
  ← (commute_supportedOn_trivialOn h (by grind [liftResidue, mem_trivialOn, mem_supportedOn])).map,
  Module.End.mul_apply]).symm)

lemma _root_.frequently_isSplit_notMem_places (O : AuxPair D.E r n) : ∃ᶠ w in .cofinite, w.IsSplit ∧
  w ∉ O.places.conjClosure := frequently_prime_q.mp
  ((eventually_notMem_star_notMem 1 O.places.toFinset).mono (by grind [isSplit_of_q_prime]))
