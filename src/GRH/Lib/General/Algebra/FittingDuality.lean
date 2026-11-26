import GRH.Lib.Adelic.Witt.FrameAction
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! General lemmas of commutative and general algebra (textbook or folklore).

This file: Relative lengths, kernels and determinants over a DVR; functions cut by matrix relations.
Elementary bounds for relative lengths of Z_p-submodules: additivity, torsion layers, generators.
Fitting ideals: base change, one more relation, iterated along a triangular family. Duality over
O/p; dividing by a finite-length submodule costs its length in Fitting ideals. -/
seal Finset.univ Finset.sum Finset.prod

noncomputable section

section

attribute [-simp] map_eq_zero

open Matrix Module Submodule LinearMap Classical Finsupp LinearEquiv IsDiscreteValuationRing Ideal
variable {O O' Γ n A : Type*} [CommRing O] [CommRing O'] [Fintype n] [Ring A] {m M M' : Type*}
  [Fintype m] [AddCommGroup M] [Module A M] [AddCommGroup M'] [Module A M'] (S T : Submodule A M)
  (R : Set (Γ →₀ Matrix n n O)) (B : Type*) [AddCommGroup B] [Module O B] {B' : Type*}
  [AddCommGroup B'] [Module O B'] {c : Γ → n → B} (φ : B →ₗ[O] B') (e : O →+* O')
  (Z : Submodule O (Γ → n → O)) {S' T' : Submodule A M'} (f : M →ₗ[A] M') {a p : O}

/-- O is a discrete valuation ring (in particular a domain). -/
class DVR O [CommRing O] extends IsDomain O, IsDiscreteValuationRing O

/-- The quotient ring O/aO. -/
abbrev QuotSpan (a : O) := O ⧸ span {a}

/-- O is a discrete valuation ring of characteristic 0, finite and free over ℤ_ℓ, with finite
quotients by nonzero ideals: the integer ring of a finite extension of ℚ_ℓ. -/
class PadicIntegerRing O (ℓ : outParam ℕ) [Fact ℓ.Prime] [CommRing O] extends Algebra ℤ_[ℓ] O,
  DVR O, CharZero O, Free ℤ_[ℓ] O, Module.Finite ℤ_[ℓ] O, Ring.HasFiniteQuotients O

instance [h : Ring.HasFiniteQuotients O] [NeZero a] : Finite (QuotSpan a) := h.1 (by aesop)

/-- For a finitely supported f from Γ to n × n matrices over O, the O-linear map c ↦ Σ_γ
f(γ)c(γ) from functions Γ → B^n to B^n. -/
@[simp] def relEval := bilinearCombination (Matrix n n O) O (α := Γ) (M := n → B).flip

/-- The submodule of functions c: Γ → B^n obeying every relation f in R, that is Σ_γ f(γ)c(γ) = 0 in
B^n. -/
def obeying := ⨅ f ∈ R, (relEval B f).ker

/-- The matrix-valued finitely supported function obtained from f by applying the ring
homomorphism e: O → O' to every matrix entry. -/
def mapRel (f : Γ →₀ Matrix n n O) := f.mapRange e.mapMatrix (by simp)

/-- The linear relations of Z: the finitely supported matrix-valued f on Γ with Σ_γ f(γ)z(γ) = 0
in O^n for all z in Z. -/
def relationsOn := {f : _ →₀ Matrix n n O | ∀ z ∈ Z, relEval O f z = 0}

/-- The length of S/(S ∩ T) as an A-module, for submodules S, T of M. -/
def relLength := length A (S ⧸ T.submoduleOf S)

lemma relLength_ker : relLength S f.ker = length A (S.map f) :=
  f.range_domRestrict S ▸ (f.domRestrict S).quotKerEquivRange.length_eq

lemma relLength_eq_length_map_mkQ : relLength S T =
  length A (S.map T.mkQ) := by simp [← relLength_ker]

lemma relLength_comap : relLength S (comap f T') = relLength (S.map f) T' := by
  rw [relLength_eq_length_map_mkQ _ T', ← map_comp, ← relLength_ker, f.ker_comp, ker_mkQ]

lemma relLength_iInf_le (T : m → _) : relLength S (⨅ i, T i) ≤ ∑ i, relLength S (T i) :=
  (length_le_of_injective _ (ker_eq_bot.1 (ker_liftQ_eq_bot' _ (pi fun _ ↦ mkQ _) (by
    simp! [ker_pi, submoduleOf])))).trans_eq (length_pi_of_fintype ..)

lemma relLength_add_length_inf : relLength S T + length A ↥(S ⊓ T) = length A S := by
  erw [add_comm, ← length_eq_add_of_exact _ _ (inclusion_injective inf_le_left) (mkQ_surjective _)]
  simp! [exact_iff, range_inclusion, submoduleOf]

@[simp] lemma relLength_bot : relLength S ⊥ = length A S := by rw [← ker_id, relLength_ker,
  S.map_id]

variable {R B S T Z}

lemma smul_quot_eq_zero_of_dvd : a ∣ p → ∀ b : QuotSpan a,
  p • b = 0 := by simp_all [dvd_def, Algebra.smul_def]

lemma nsmul_quot_eq_zero {ℓ M : ℕ} (h : a ∣ ℓ ^ M := by rfl) : ∀ x : QuotSpan a, ℓ ^ M • x = 0 :=
  mod_cast smul_quot_eq_zero_of_dvd h

lemma mem_obeying : c ∈ obeying R B ↔ ∀ f ∈ R, relEval B f c = 0 := by simp [obeying]

lemma comp_mem_obeying_iff : (φ <| c · ·) ∈ obeying R B' ↔ ∀ f ∈ R, ∀ i,
  φ (relEval B f c i) = 0 := by simp [obeying, linearCombination, sum, funext_iff]

lemma comp_mem_obeying z : z ∈ Z → ((span {a}).mkQ <| z · ·) ∈ obeying (relationsOn Z) _ := by
  simp_all [relationsOn, ↓comp_mem_obeying_iff]

/-- The set of matrix-valued relations, one for each pair (g, h), expressing the cocycle
identity c(gh) = c(g) + ρ(g)c(h). -/
def cocycleRels [Mul Γ] (ρ : Γ → Matrix n n O) :=
  {f | ∃ g h, f = .single (g * h) 1 - .single g 1 - Finsupp.single h (ρ g)}

lemma mem_obeying_cocycleRels [Mul Γ] {ρ : Γ → Matrix n n O} : c ∈ obeying (cocycleRels ρ) B ↔ ∀ g
  h, c (g * h) = c g + ρ g • c h := by aesop (add simp [obeying, cocycleRels, sub_eq_iff_eq_add'])

lemma relLength_le_of_inj (h : ∀ x ∈ S, f x ∈ S') (h' : ∀ x ∈ S, f x ∈ T' → x ∈ T) : relLength S T ≤
    relLength S' T' := (length_le_of_surjective _ (factor_surjective (h' _ ·.2))).trans
    (length_le_of_injective (mapQ _ _ (f.restrict h) le_rfl) (by simp [← ker_eq_bot, ker_mapQ]))

lemma relLength_mono {S' T'} : S ≤ S' → T' ≤ T → relLength S T ≤ relLength S' T' :=
  (relLength_le_of_inj id · ∘ by tauto)

@[simp] lemma relLength_eq_zero : relLength S T = 0 ↔ S ≤ T := by simp [relLength, length_quotient]

lemma length_mono : S ≤ T → length A S ≤ length A T := (by simpa using relLength_mono · (le_refl ⊥))

lemma length_le_of_le_map S (h : T' ≤ .map f S) : length A T' ≤ length A S := by
  grw [length_mono h, ← relLength_ker, ← relLength_add_length_inf S f.ker]; simp

variable [DVR O]

/-- For a discrete valuation ring O and a finitely generated module Z of functions Γ → O^n, n ≥
1, the functions Γ → B^n obeying all relations of Z have length at most rank Z · length B. -/
lemma length_obeying_relationsOn_le (h : Module.Finite O Z) (i : n) :
    length O (obeying (relationsOn Z) B) ≤ finrank O Z * length O B := by
  let φ := (((relEval O).restrictScalars O).compr₂ (proj i)).compl₂ Z.subtype
  grw [← finrank_linearMap_self _ O, ← φ.range.finrank_le, length_le_of_le_map (.pi fun g ↦
    .pi fun j ↦ applyₗ (φ.ker.mkQ (single g (.single i j 1)))) ⊤ fun c h ↦ ⟨liftQ _ (proj i ∘ₗ
    (lift _ _ _ c).restrictScalars O) fun f e ↦ by simpa using! (mem_obeying.1 h (single i i (1 :
    O) • f) (by simp_all [relationsOn, φ, DFunLike.ext_iff])), ⟨⟩, by simp! [funext_iff]⟩,
    length_top, ← (((finBasis ..).map φ.quotKerEquivRange.symm).constr O).length_eq]; simp

@[simp] lemma length_quot_span_eq_addVal : length O (QuotSpan a) = addVal O a :=
  Ring.ord_eq_addVal a

lemma addVal_prod (f : m → O) : addVal O (∏ i, f i) = ∑ i, addVal O (f i) := by
  erw [map_prod (addVal O).1]; rfl'

/-- For a square matrix M over a discrete valuation ring O and p in O, the kernel of M acting on
(O/p)^n has O-length at most the valuation of det M, normalised so that a uniformiser has
valuation 1. -/
lemma length_ker_le_addVal_det (M : Matrix n n O) (p : O) :
  length O (ker (M • 1 : End O (n → QuotSpan p))) ≤ addVal O M.det := by
  obtain ⟨⟨Q, -, P, -, a, rfl⟩, h⟩ := isValuationPair_top.smith_normal_form M,
    IsPrincipal.of_comap _ (span {p}).mkQ_surjective
  grw [length_le_of_le_map (P⁻¹ • piMap fun i ↦ liftQSpanSingleton _ (toSpanSingleton O ..)
    (h (torsionBy O _ (a i))).generator_mem) ⊤ fun w m ↦ ?_]
  simp [addVal_prod, le_add_right]
  choose t ht using by simpa [mul_smul, funext_iff, diagonal, ← mem_torsionBy_iff,
    IsPrincipal.mem_iff_eq_smul_generator] using m
  use (t ·), ⟨⟩, .symm ((smul_eq_iff_eq_inv_smul P).1 (funext ht))

/-- Let O be a discrete valuation ring and Z an O-module of functions Γ → O/p. If n_i·z(q_i) = 0
for all z in Z, and only z = 0 vanishes at all the finitely many points q_i, then length Z ≤
v(∏ n_i). -/
lemma length_le_of_detecting_points {n q : m → _} {Z : Submodule O (Γ → B)} (e : B ≃ₗ[O] QuotSpan p)
    (h : ∀ z ∈ Z, ∀ i, n i • z (q i) = 0) (h' : ∀ z ∈ Z, (∀ i, z (q i) = 0) → z = 0) :
    length O Z ≤ addVal O (∏ i, n i : ℕ) := by
  grw [Nat.cast_prod, ← det_diagonal, ← length_ker_le_addVal_det]
  apply length_le_of_injective (.restrict (pi ((e.1 ∘ₗ proj ·) ∘ q)) _) <;>
    simp_all! [funext_iff, Nat.cast_smul_eq_nsmul, ← e.map_smul, disjoint_def, diagonal]

/-- Let O be a discrete valuation ring and aO^n ⊆ L ⊆ O^n, a ≠ 0. There are a square matrix M
with rows in L and a submodule S of (O/a)^n whose annihilator in O^n is exactly L, with
v(det M) ≤ length S. -/
lemma exists_matrix_addVal_det_le_length (L : Submodule O _) (ha : a ≠ 0) (h : ∀ v, a • v ∈ L) :
  ∃ M, ∃ S : Submodule O (n → QuotSpan a), (∀ i, M i ∈ L) ∧ (∀ v, v ∈ L ↔ ∀ w ∈ S, ∑ j, v j • w j =
  0) ∧ addVal O (det M) ≤ length O S := by
  let g := codRestrict L (a • .id) h
  have b := ofFinrankEq _ _ (L.finrank_le.antisymm' (g.finrank_le_finrank_of_injective
    ((lsmul_injective ha).codRestrict h)))
  obtain ⟨M, N, rfl, k⟩ : ∃ M N : Matrix n n O, L = M.toLinearMapRight'.range ∧ M * N = a • 1 :=
    ⟨(L.subtype ∘ₗ b).toMatrixRight', (b.symm ∘ₗ g).toMatrixRight', by
    simp [ext_iff_vecMul, ↓vecMul_smul, ← toLinearMapRight'_apply, symm_apply_eq]; tauto⟩
  have c := right_ne_zero_of_mul (mt (det_mul M N).trans (by aesop))
  use M, .map (N • 1 : End O _) ⊤, (⟨_, M.single_one_vecMul ·⟩), fun v ↦ .trans (by simp [←
    (vecMul_injective_iff.2 (linearIndependent_rows_of_det_ne_zero c)).eq_iff (b := v), k, skolem,
    vecMul_smul, funext_iff, Quotient.eq_zero_iff_dvd, dvd_def, @eq_comm O]) (.trans
    (dotProduct_eq_zero_iff (v := (span {a}).mkQ.compLeft _ (v ᵥ* N))).symm (by
    simp [vecMul_eq_sum, sum_dotProduct]; rfl)), by grw [← ENat.add_le_add_iff_right
    (addVal_eq_top_iff.ne.2 c), ← addVal_mul, ← det_mul, k, ← length_ker_le_addVal_det, ←
    relLength_ker, ← length_mono inf_le_right, relLength_add_length_inf]; simp

end

open Module Submodule Cardinal Function Matrix IsDiscreteValuationRing

namespace Lift

variable {p V} [Fact p.Prime] [AddCommGroup V] [Module ℤ_[p] V] {L L' L'' : Submodule ℤ_[p] V}
  {m n : ℕ}

lemma relLength_trans (h : relLength L L' ≤ m) (g : relLength L' L'' ≤ n) : relLength L L'' ≤
  ↑(m + n) := by grw [relLength_eq_length_map_mkQ, ← relLength_add_length_inf, length_mono
  inf_le_right, ← relLength_eq_length_map_mkQ, g, ← relLength_comap, relLength_mono, h] <;> simp

/-- Let L, L' be Z_p-submodules of V with p^t L ⊆ L'. Suppose any m + 1 elements x_j of L with
px_j in L' have a combination ∑ a_j x_j in L' with some a_j = 1. Then L/(L ∩ L') has length
≤ tm. -/
lemma relLength_le_of_relations t (e : ∀ x ∈ L, p ^ t • x ∈ L') (h : ∀ x : Fin (m + 1) → V,
  (∀ j, x j ∈ L ∧ (p : ℤ_[p]) • x j ∈ L') → ∃ᵉ (a : _ → ℤ_[p]) (j), a j = 1 ∧ ∑ j, a j • x j ∈ L') :
  relLength L L' ≤ ↑(t * m) := by
  induction' t with _ ih generalizing L'; simpa using! e
  let T := L ⊓ L'.comap (.lsmul _ V p)
  let := ((isTorsionBy_quotient_iff (L'.submoduleOf T) _).2 (·.2.2)).module
  let := @Ideal.Quotient.field ℤ_[p] _ _ PadicInt.prime_p.isMaximal_span_singleton
  grw [add_one_mul, relLength_trans (@ih T (by simp_all [T, nsmul_mem, mul_smul, pow_add,
       Nat.cast_smul_eq_nsmul]) fun x l ↦ by simpa [T, sum_smul_mem, l] using h _ (l · |>.2))]
  erw [← not_lt, ← ENat.natCast_add_one_le_iff, relLength, length_eq_of_surjective (mkQ_surjective
    (ℤ_[p] ∙ ↑p)), length_eq_rank, natCast_le_toENat, le_rank_iff,
    (mkQ_surjective _).comp_left.exists]
  intro ⟨x, y⟩; choose a j n k using h _ (x · |>.2); simpa [n] using Fintype.linearIndependent_iff.1
    y (a ·) ((map_sum ..).symm.trans ((ker_mkQ _).ge (mod_cast k))) j

end Lift

variable {R ι : Type} [CommRing R] [Fintype ι] {N : Submodule R (ι → R)}

/-- The ideal of R generated by the determinants of square matrices with all rows in N ⊆ R^ι:
the zeroth Fitting ideal of R^ι modulo N. -/
def fittingIdeal (N : Submodule R (ι → R)) := Ideal.span (det '' {B | ∀ i, B i ∈ N})

/-- For an ideal I, the Fitting ideal of N + I·R^ι is contained in the Fitting ideal of N plus
I. -/
lemma fittingIdeal.sup_smul_top_le {I} : fittingIdeal (N ⊔ I • ⊤) ≤ fittingIdeal N ⊔ I :=
  span_le.2 fun _ ⟨B, h, e⟩ ↦ e ▸ by
  choose n h m k E using mem_sup.1 ∘' h
  exact I.mem_quotient_iff_mem_sup.1 (subset_span ⟨_, subset_span ⟨of n, h, rfl⟩, by simp [← E,
    det_apply, by simpa using fun i j ↦ I.smul_top_le_comap_smul_top (I.mkQ ∘ₗ .proj j) (k i)]⟩)

/-- If rv ∈ N, then r multiplies the Fitting ideal of N + Rv into that of N. -/
lemma fittingIdeal.mul_mem_of_smul_mem {r v} (h : r • v ∈ N) : ∀ d ∈ fittingIdeal (N ⊔ R ∙ v), r *
  d ∈ fittingIdeal N := span_le (p := comap (.mulLeft R r) (fittingIdeal N)).2 fun _ ⟨B, hB, e⟩ ↦ by
  choose c k H using mem_span_set.1 ∘' (N.sup_span ▸ hB)
  erw [← e, ← funext H, det, MultilinearMap.map_sum_finset]
  exact sum_mem fun s m ↦ (det_mul_column ..).symm.subst (smul_mem _ _ (by_contra fun u ↦
    u ((fittingIdeal N).smul_mem r (subset_span ⟨s, fun i ↦ by_contra fun k ↦
    u (subset_span ⟨update s i (r • s i), by simp_all [Set.subset_def, det]; grind [zero_mem,
    detRowAlternating.map_eq_zero_of_eq s]⟩), rfl⟩))))

/-- If, for each j in I, r_j v_j lies in N plus the span of the v_i with i ∈ I, i < j, then
∏_{j∈I} r_j multiplies the Fitting ideal of N + Σ_{j∈I} Rv_j into that of N. -/
lemma fittingIdeal.triangle {J} [LinearOrder J] {I : Finset J} {v} r :
  (∀ j ∈ I, ∀ K ≥ N, ↑I ∩ .Iio j ⊆ v ⁻¹' K
  → r j • v j ∈ K) → ∃ K ≥ N, ↑I ⊆ v ⁻¹' K ∧ ∀ d ∈ fittingIdeal K, d * I.prod r ∈ fittingIdeal N :=
  I.induction_on_max (by aesop) fun e s _ ih h ↦ (ih (by grind)).imp' (· ⊔ R ∙ v e) (by
    simp_all [Set.subset_def, mem_sup_right]
    grind [IsConcreteLE.le_iff, → mul_mem_of_smul_mem, le_sup_left])

variable {O R G n ι : Type} [CommRing O] [DVR O] [CommRing R] [Algebra O R]
  (Φ : (n → O) →ₗ[O] ι → R) (z : G → _) (N : Submodule R (ι → R)) (p : O)

/-- The module of functions g ↦ Ψ(z_g), for O-linear maps Ψ: O^n → O/p that vanish on Φ⁻¹(N). -/
def formsMod : Submodule O (G → Unit → QuotSpan p) :=
  (((N.restrictScalars O).comap Φ).compatibleMaps ⊥).map (.pi (.applyₗ <| z ·))

variable {Φ N p} [Fintype n] (hp : p ≠ 0) (hN : ∀ v, Φ (p • v) ∈ N)
include hp hN

/-- Let p ≠ 0 with pΦ(O^n) ⊆ N. If every O-linear map O^n → O/p vanishing on Φ⁻¹(N) vanishes at
v, then Φ(v) ∈ N. -/
lemma mem_of_forall_form_eq_zero {v} (H : ∀ Ψ : _ →ₗ[O] Unit → QuotSpan p, (∀ ⦃v⦄, Φ v ∈ N →
  Ψ v = 0) → Ψ v = 0) : Φ v ∈ N := have ⟨_, _, _, k, _⟩ :=
    exists_matrix_addVal_det_le_length ((N.restrictScalars O).comap Φ) hp hN
  (k v).2 fun w _ ↦ by
    simpa using congr($(H (.pi fun _ ↦ (Pi.basisFun O _).constr O w) (by simp_all [funext_iff])) ())

/-- Let p ≠ 0, pΦ(O^n) ⊆ N, V a module of functions G → O/p. Some K ⊇ N contains Φ(v) whenever
all linear Ψ with Ψ∘z ∈ V kill v, and some c ∈ O multiplies Fitt K into Fitt N, v(c) ≤
length of `formsMod` modulo V. -/
lemma fittingIdeal.exists_cost_le_relLength [IsNoetherianRing R] [Fintype ι] V : ∃ c, ∃ K ≥ N,
  addVal O c ≤ relLength (formsMod Φ z N p) V ∧ (∀ ⦃v⦄, (∀ Ψ : _ →ₗ[O] _, Ψ ∘ z ∈ V → Ψ v = 0) →
  Φ v ∈ K) ∧ ∀ d ∈ fittingIdeal K, c • d ∈ fittingIdeal N := by
  induction' N using IsNoetherian.induction with N i
  by_contra u
  obtain ⟨v, m, H⟩ := by simpa using (u ⟨1, N, ·⟩)
  exact (WfDvdMonoid.induction_on_irreducible p (by simp) (by simpa [IsUnit, ← Units.smul_def,
    smul_mem_iff']) fun a ϖ h hϖ h₀ _ h₁ ↦ (i _ (lt_sup_iff_notMem.2 (h₀ h)) (mem_sup_left <|
    hN ·)).elim fun c ⟨K, L, w, D⟩ ↦ u ⟨c * ϖ, K, by order, by
    grw [addVal_mul, addVal_uniformizer hϖ, w]
    simp_rw [relLength_eq_length_map_mkQ, length_submodule, formsMod, ← map_comp]
    exact Order.height_add_one_le ⟨map_mono fun _ h _ ↦ (h <| mem_sup_left ·), fun l ↦ h₀ h
      (mem_of_forall_form_eq_zero hp hN fun Ψ h ↦ (l ⟨Ψ, h, rfl⟩).elim fun s ⟨h, e⟩ ↦ by
      simpa [by simpa using m (s - Ψ) (SModEq.sub_mem.1 e)] using h (mem_sup_right (subset_span
        rfl)))⟩, D.1, by simpa [mul_smul] using (mul_mem_of_smul_mem (r :=
    ϖ • (1 : R)) (by simp_all [mul_smul]) _ <| D.2 · ·)⟩ : p ≠ 0 → Φ (p • v) ∉ N) hp (hN v)
