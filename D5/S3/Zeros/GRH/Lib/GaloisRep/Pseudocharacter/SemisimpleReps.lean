/- GID: D5/S3/Zeros/GRH/Lib/GaloisRep/Pseudocharacter/SemisimpleReps
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/GaloisRep/Pseudocharacter/SemisimpleReps
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.GaloisRep.Pseudocharacter.SemisimpleReps. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/GaloisRep/Pseudocharacter/SemisimpleReps.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.General.LinearAlgebra.CommonEigenvectors
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Part of: Pseudocharacters, Brauer–Nesbitt, Clifford; compact subgroups of GL_n stabilise a
lattice (known result; see Lib.GaloisRep.Pseudocharacter.FibreSum).

This file: Wedderburn tools, Brauer-Nesbitt, Clifford, representation from a trace, continuity from
the trace. -/

open Algebra ConjAct Fintype IsArtinianRing LinearMap Matrix Pi Submodule Units

attribute [local simp ←] single_mul_left

attribute [local simp] sum_sigma Matrix.mul_assoc Matrix.mul_sum Matrix.sum_mul

variable {k G H n N B : Type} [Field k] [Group G] [Fintype n] [Fintype N] {m} {d : Fin m → ℕ}
  {r : G →* GL n k} [∀ i, NeZero (d i)]

/-- The product ∏_i M_{d_i}(k) of the matrix rings of sizes d_i over k, for a finite family of
natural numbers d_i. -/
abbrev PiMat k (d : Fin m → ℕ) := ∀ i, Matrix (Fin (d i)) (Fin (d i)) k

/-- The R-algebra homomorphism from ∏_i M_{m_i}(R) to matrices indexed by the disjoint union of
the m_i, sending a family of square matrices to the block diagonal matrix. -/
@[simps!] noncomputable def blockDiagonalAlgHom {R o} {m : o → Type} [CommRing R] [DecidableEq o]
  [Fintype o] [∀ i, Fintype (m i)] : (∀ i, Matrix (m i) (m i) R) →ₐ[R] Matrix (Σ i, m i) (Σ i,
  m i) R := .mk' (by use! blockDiagonal' <;> simp [Pi.mul_def]) (by simp)

/-- The element of the product of matrix algebras M_{d_i}(k) that is the matrix unit E_ab in
factor i and zero elsewhere; a, b default to 0. -/
noncomputable abbrev piMatrixUnit i (a b : Fin (d i) := 0) : PiMat k d := single i (single a b 1)

lemma sum_piMatrixUnit : ∑ i, ∑ a, (piMatrixUnit i a a : PiMat k d) = 1 :=
  funext (by simp_all [sum_eq_single ·, sum_single_one])

variable {p : Matrix n n k} (f : PiMat k d →ₐ[k] Matrix N N k) (f' : PiMat k d →ₐ[k] Matrix n n k)
  [CharZero k] [IsAlgClosed k] [Ring B] [Group H] [Algebra k B] [Module.Finite k B] (ρ : G →* B)

lemma trace_of_idempotent (e : IsIdempotentElem p) : p.trace = p.rank ∧ (p = 0 ↔ p.trace = 0) := by
  simp [p.trace_toLin'_eq ▸ (e.map toLinAlgEquiv').isProj_range.trace, range_eq_bot]; rfl

attribute [local ext] ext_linearMap

omit [CharZero k] [IsAlgClosed k] [Module.Finite k B] in
lemma isIdempotentElem_map_piMatrixUnit (f : PiMat k d →ₐ[k] B) i :
  IsIdempotentElem (f (piMatrixUnit i)) := .map (symm (by simp)) f

omit [∀ i, NeZero (d i)] in
lemma IsTraceNondeg.of_span_piMat {s} (u : span k (.range s) = ⊤) (e : ∀ g, f' (s g) = r g) :
    IsTraceNondeg r := fun x hx h ↦ (mem_span.1 hx f'.range.toSubmodule (by aesop)).rec fun a E ↦ by
  choose c he b hb using by simpa [le_antisymm_iff, mem_span_singleton] using
    IsSemisimpleRing.ideal_eq_span_idempotent (_ ∙ a)
  rw [← E, ← hb, map_mul, (trace_of_idempotent (he.map _)).2.2, mul_zero]
  refine closure_induction ?_ ?_ ?_ (u.ge ⟨⟩ : c ∈ _) <;> simp_all [x.trace_mul_comm, add_mul]

lemma exists_rep_of_trace {s : G →* PiMat k d} (u : span k (.range s) = ⊤) (τ : PiMat k d →ₗ[k] k)
  (c : ∀ x y, τ (x * y) = τ (y * x)) (h : ∀ i, ∃ m : ℕ, τ (piMatrixUnit i) = m) (e : τ 1 = card n) :
    ∃ r, IsTraceNondeg (n := n) r ∧ ∀ g, (r g).1.trace = τ (s g) := by
  choose m h using h
  obtain rfl : τ = lsum k _ k (m · • traceLinearMap ..); ext i a b; by_cases a = b <;>
    simpa [-lsum_apply, lsum_piSingle, eq_comm, *] using c (piMatrixUnit i a) (piMatrixUnit i 0 b)
  exact (fun φ ↦ (⟨.toHomUnits (.comp φ s), .of_span_piMat φ u (by simp), ·⟩)) ((reindexAlgEquiv k k
    (equivOfCardEq (by simp_all [← @Nat.cast_inj k]))).toAlgHom.comp (.comp
    blockDiagonalAlgHom (.pi (evalAlgHom k _ <| @Sigma.fst _ (Fin <| m ·) ·))))
    (by simp +instances [-coe_reindexAlgEquiv, trace_blockDiagonal'])

/-- For algebra maps f, f' from the product of M_{d_i}(k) to matrix algebras and matrices U_i,
the matrix Σ_i Σ_a f(E^i_{a0}) U_i f'(E^i_{0a}). -/
noncomputable def intertwiner (U : _ → Matrix N n k) := ∑ i, ∑ a,
  f (piMatrixUnit i a) * U i * f' (piMatrixUnit i 0 a)

section

omit [CharZero k] [IsAlgClosed k]

lemma intertwiner_mul_piMatrixUnit U i a
  b : let x := f (piMatrixUnit i a) * U i * f' (piMatrixUnit i 0 b)
  intertwiner f f' U * f' (piMatrixUnit i a b) = x ∧ f (piMatrixUnit i a b) * intertwiner f f' U =
    x := by simp_all [intertwiner,
  ← map_mul, ← (f _).mul_assoc (f _), eq_comm, sum_eq_single i, sum_eq_single a, sum_eq_single b]

lemma mul_intertwiner U z : f z * intertwiner f f' U = intertwiner f f' U * f' z :=
  (Pi.basis fun _ ↦ stdBasis
  ..).sum_repr z ▸ by simp [sum_prod_type, stdBasis_eq_single, intertwiner_mul_piMatrixUnit]

lemma exists_piMat_retract (h : ∀ i, (f' (piMatrixUnit i)).rank ≤ (f (piMatrixUnit i)).rank) :
    ∃ (P : Matrix N n k) (Q : Matrix n N k), Q * P = 1 ∧ ∀ z, f z * P = P * f' z := by
  choose J j using (finrank_le_iff_exists_linearMap.1 <| h ·)
  choose U u using (J · |> (Module.projective_lifting_property _ · (surjective_rangeRestrict _)))
  choose L l using (Submodule.subtype _ ∘ₗ J · |>.exists_leftInverse_of_injective (by aesop))
  refine ⟨_, intertwiner f' f (Submodule.subtype _ ∘ₗ L · |>.toMatrix'), ?_,
    mul_intertwiner f _ (U · ∘ₗ rangeRestrict _ |>.toMatrix')⟩
  simp_all [intertwiner.eq_1 f', intertwiner_mul_piMatrixUnit, ext_iff_mulVec, ← mulVec_mulVec,
    sum_mulVec, DFunLike.ext_iff, ← SetLike.coe_eq_coe, -Subtype.forall]
  simp [← sum_mulVec, ← map_mul, ← map_sum, sum_piMatrixUnit]

end

variable (k) in
/-- The span of ρ(G) in B is semiprime: any x in it with x ρ(g) x = 0 for all g is zero. -/
def HasSemiprimeSpan := ∀ x ∈ span k (.range ρ), (∀ g, x * ρ g * x = 0) → x = 0

/-- Wedderburn–Clifford: k algebraically closed of characteristic 0, B finite-dimensional, f(H)
normal, no nonzero x in span ρ(G) with xρ(G)x = 0. Then ρ∘f = F∘s with s(H) spanning a
finite product of matrix algebras and F an injective algebra map into B. -/
lemma exists_wedderburn (f : H →* G) (h : HasSemiprimeSpan k ρ) (hf :
  f.range.Normal := by exact ⟨by simp⟩) : ∃ b d,
  ∃ (_ : ∀ i : Fin b, NeZero (d i)) (s : H →* PiMat k d) (F : _ →ₐ[k] B), (∀ i, F (piMatrixUnit i) ≠
  0) ∧ span k (Set.range s) = ⊤ ∧ ∀ g, F (s g) = ρ (f g) := let A := adjoin k (Set.range (ρ.comp f))
  have u := MonoidHom.mclosure_range (ρ.comp f) ▸ adjoin_eq_span k _
  have := of_finite k A
  have c g : A ≤ A.comap (MulSemiringAction.toAlgHom k B (toConjAct (ρ.toHomUnits g))) :=
    adjoin_le fun _ ⟨y, _⟩ ↦ subset_adjoin ((hf.1 _ ⟨y, rfl⟩ g).imp (by aesop))
  have ⟨_, d, h, ⟨e⟩⟩ := (isSemisimpleRing_iff_jacobson.2
    ((eq_bot_or_exists_atom_le _).resolve_right fun ⟨_, a, l⟩ ↦ a.bot_lt.2 fun (x : A) m ↦
    x.ext (h _ (span_mono (by simp) (u.le x.2)) fun g ↦ by
    simpa [units_smul_def, mul_assoc, Subtype.ext_iff] using (a.2 _ (FG.of_finite.jacobson_smul_lt
      a.1)).le (smul_mem_smul (@Ring.le_comap_jacobson _ _ _ _ (.restrict _ _ _ (c g⁻¹)) ⟨(⟨⟨_, c g
      ·.2⟩, by aesop⟩)⟩ _ (l m)) m)))).exists_algEquiv_pi_matrix_of_isAlgClosed k
  have e : A ≃ₐ[k] PiMat k d := by convert! e
  ⟨_, _, h, .comp e ((ρ.comp f).codRestrict A (by bound)), A.val.comp e.symm, by
  erw [Set.range_comp e, span_image e.toLinearMap, (span_range_subtype_eq_top_iff ..).2 u.symm]
  simp [← ext_iff, Matrix.single]⟩

omit [CharZero k] [IsAlgClosed k] in
/-- Let r: G → GL_n(k) have non-degenerate trace form on the span of r(G). Then any x in that span
with x r(g) x = 0 for all g is zero. -/
lemma IsTraceNondeg.hasSemiprimeSpan (h : IsTraceNondeg r) :
  HasSemiprimeSpan k ((coeHom _).comp r) := (h · · ∘ fun H g ↦
  (Matrix.isNilpotent_trace_of_isNilpotent ⟨2, by erw [sq, ← mul_assoc, H, zero_mul]⟩).eq_zero)

/-- Clifford's theorem: over an algebraically closed field of characteristic zero, if r: G →
GL_n(k) is semisimple (trace form non-degenerate on its span) and f: H → G has normal image,
then r ∘ f is semisimple in the same sense. -/
lemma IsTraceNondeg.comp (h : IsTraceNondeg r) (f : H →* G) (hf :
  f.range.Normal := by simp <;> infer_instance) :
  IsTraceNondeg (r.comp f) := let ⟨_, _, _, _, F, h⟩ := exists_wedderburn _ f h.hasSemiprimeSpan hf
  h.2.elim (of_span_piMat F)

/-- Let k be algebraically closed of characteristic 0, B finite-dimensional, r satisfy
`IsTraceNondeg`, ρ: G → B satisfy `HasSemiprimeSpan`, and φ: B → M_n(k) be an algebra map. If tr
r = tr φρ, then r(g)P = Pφ(ρ(g)) for some invertible P.

Known result: this is the Brauer–Nesbitt theorem. -/
lemma IsTraceNondeg.exists_conj_of_trace_eq (h : IsTraceNondeg r) (φ : B →ₐ[k] _) (j :
  HasSemiprimeSpan k ρ) (t : ∀ g, (r g).1.trace = (φ (ρ g)).trace) : ∃ P : GL n k, ∀ g, (r g).1 *
  P = P * φ (ρ g) := have ⟨_, _, _, s, f, _, u, a⟩ :=
    exists_wedderburn (((coeHom _).comp r).prod ρ) (.id G) fun x m ↦ by simp_all [Prod.ext_iff,
    (span_prod_le _ _ (span_mono _ m)).imp (h.hasSemiprimeSpan _) (j _)]
  have ⟨_, _, e, H⟩ := exists_piMat_retract (.comp (.fst ..) f) (φ.comp (.comp (.snd ..) f)) fun i ↦
    Eq.le (by simp only [← @Nat.cast_inj k, ← trace_of_idempotent,
                isIdempotentElem_map_piMatrixUnit]
              refine closure_induction ?_ ?_ ?_ (u.ge ⟨⟩ : piMatrixUnit i ∈ _) <;> simp_all)
  ⟨⟨_, _, mul_eq_one_symm e, e⟩, (by simpa [a] using H <| s ·)⟩

omit [CharZero k] [IsAlgClosed k] in
/-- A representation r of a topological group into GL_n(k), k a field with a ring topology, with
non-degenerate trace form on the span of its image, is continuous as soon as its trace is
continuous. -/
lemma IsTraceNondeg.continuous_of_trace [TopologicalSpace k] [IsTopologicalRing k] [TopologicalSpace
  G] [IsTopologicalGroup G] (h : IsTraceNondeg r) (hc : Continuous (r · |>.1.trace)) :
  Continuous r := .of_coeHom_comp (continuous_matrix fun i j ↦ mem_span.1
  (FiniteDimensional.mem_span_of_iInf_ker_le_ker (K := (entryLinearMap k k i j).domRestrict (span
  k (Set.range (r ·)))) (L := fun g ↦ (traceLinearMap .. ∘ₗ .mulRight _ ↑(r g)).domRestrict _)
  (by simp_all [IsTraceNondeg, LE.le])) ((continuousSubmodule ..).comap
  (.pi (applyₗ ⟨r ·, by aesop⟩))) (by simpa using! hc.comp' ∘' continuous_mul_const))
