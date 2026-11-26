import GRH.Lib.Shimura.Uniformisation.RiemannFormAdelic
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! Known result: Hecke algebra of a pair and its action by correspondences on the base of a tower.
Here only a semigroup acts, and only far enough up the tower. The algebra is a subalgebra of the
group ring, and the cohomology theory is any linear functor for which the base is the invariants of
each cover. Source: Shimura, Introduction to the arithmetic theory of automorphic functions, 1971,
ch. 3 and 7–8.

Part of: Density of algebraic vectors, congruences to supercuspidal types; limits of eigensystems
(known result; see Lib.GaloisRep.WeightCongruence.WeightCongruence).

This file: Local GL_n at split places, spherical Hecke elements, commuting operators on base
cohomology. Existence of a wild supercuspidal-type character; principal level inside an open
subgroup. -/

noncomputable section

open NumberField Matrix CategoryTheory Set Module WithZero Valued IsLocalRing Gf FiniteField
  IsDedekindDomain.HeightOneSpectrum QuotientAddGroup QZ Polynomial Ideal Fintype IsPrime

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : Type} [Fintype n]
  {𝔑 : NumberField.RingOfIntegers E} {d₀ : ℕ} [HasQuadSubfield d₀ E] {k W : Type} [CommRing.{0} k]
  [AddCommGroup.{0} W] [Module k W] {π : Representation k (GL n (𝔸f E)) W} {w : SplitFinPlace E}
  (g : GL n (LocField w.1)) (s s' : SafePlace 𝔑 × ℕ) {x : W} (h : x ∈ levelSpace π (levelGU n 𝔑))

/-- The endomorphism of the unitary group {g : gᴴg = 1} of n × n matrices over R that applies the
involution of R to each entry. -/
def entryConj {R} [CommRing R] [StarRing R] :=
  (invTransposeGL.toMonoidHom.comp (U 1).subtype).codRestrict (U (1 :
  Matrix n n R)) fun g ↦ mul_eq_one_comm.1 (by simpa [-coe_units_inv] using! congr($(g⁻¹.2)ᵀ))

@[simp] lemma conjAtSplit_unitary :
  (conjAtSplit w g).1ᴴ * conjAtSplit w g = 1 := by simpa [U] using! (entryConj _).2

@[simp] lemma conjAtSplit_mem_GU : conjAtSplit w g ∈ GU E n := ⟨1, rfl, 1, by simp⟩

attribute [local simp] heckeSum cosetFn spanOn starRingEnd_apply Model.cosetSum mem_intGL

@[simp] lemma evalAt_conjAtSplit : .map (evalAt _) (conjAtSplit w g) =
  invTransposeGL g := congr(invTransposeGL $(atPlace_atSplit w.2 _))

lemma evalAt_conjAtSplit_of_ne {u} : u ≠ w.1 → star u ≠ w → (conjAtSplit w g).map (evalAt u) = 1 :=
  (invTransposeGL.map_eq_one_iff.2 <| atPlace_atSplit_of_ne w.2 _ · ·)

@[simp] lemma dualComponent_conjAtSplit : dualComponent w (conjAtSplit w g) =
  g := by simp [dualComponent]

lemma conj_conjAtSplit {g} : g ∈ GU E n → ∀ m, g * conjAtSplit w m * g⁻¹ =
  conjAtSplit w (dualComponent w g * m * (dualComponent w g)⁻¹) := fun ⟨c, l, _, e⟩ m ↦ by
  apply congrArg (·.1) (Gf.eq_of_supportedOn (S := {w.1}) (k := ⟨conjAtSplit w _, (entryConj _).2⟩)
      (g := U.conj g rfl ⟨_, by simp [U, by simpa [l.ne', map_smul'] using congr((c⁻¹ : E) • $e)]⟩)
    ..) <;> simp_all [Gf.atPlace, dualComponent, evalAt_conjAtSplit_of_ne]

/-- A unitary similitude g (an element of `GU`) whose component at the split place w
is 1 commutes with the image under `conjAtSplit` of every m in GL_n(E_w). -/
lemma commute_conjAtSplit {g} (h : g ∈ GU E n ⊓ (dualComponent w).ker) m :
  Commute g (conjAtSplit w m) := eq_mul_of_mul_inv_eq (by simp_all [conj_conjAtSplit])

lemma conjAtSplit_mem_intGL_iff {g} : conjAtSplit w g ∈ intGL n (Ô E) ↔
  g ∈ Kw .. := by erw [invTransposeGL_mem_intGL, atSplit_mem_Kf w.2]

/-- A similitude g in GL_n(Ô) lies in the principal level K(𝔑) if at each place v dividing 𝔑 it has
the same v-component as some element of K(𝔑). -/
lemma mem_levelGU_of_local {g} (a : g ∈ GU ..) (b : g ∈ intGL n (Ô E)) (H : ∀ u, 𝔑 ∈ u.1 →
  ∃ κ ∈ levelGU n 𝔑, g.map (evalAt u) = κ.map (evalAt u)) : g ∈ levelGU n 𝔑 :=
  ⟨a, b, fun i j ↦ mem_span_iff_valuation_le.2 ⟨by aesop, fun u h ↦ (H u h).elim fun _ ⟨k,
  e⟩ ↦ congr(v ($e i j - _)).trans_le ((mem_span_iff_valuation_le.1 (k.2.2 i j)).2 u h)⟩⟩

lemma isOpen_comap_conjAtSplit (h₀ : 𝔑 ≠ 0) : IsOpen ((levelGU n 𝔑).comap (conjAtSplit
  w)).carrier := .and (by simp) ((isOpen_congruenceGL_span h₀).preimage (.of_coeHom_comp
  (Units.continuous_coe_inv.comp (continuous_atSplit w.2).subtype_val).matrix_transpose))

/-- Let w be split, 𝔑 ∉ w̄, κ ∈ K(𝔑). Then c', the unitary element equal to κ at w and 1 away
from w, w̄, lies in K(𝔑), and c'⁻¹κ commutes with the whole image of `conjAtSplit` at w. -/
lemma conjAtSplit_dualComponent (h' : 𝔑 ∉ (star w.1).1) {κ} (hκ : κ ∈ levelGU n 𝔑) : conjAtSplit w
  (dualComponent w κ) ∈ levelGU n 𝔑 ∧ ∀ m, Commute ((conjAtSplit w (dualComponent w κ))⁻¹ * κ)
  (conjAtSplit w m) := ⟨mem_levelGU_of_local (by simp) (conjAtSplit_mem_intGL_iff.2
  ((invTransposeGL_mem_intGL _).2 (mem_intGL_Ô.1 hκ.2.1 _))) ((and_forall_ne _).1 ⟨fun _ ↦ ⟨κ, hκ,
  evalAt_conjAtSplit _⟩, by grind [star_star, evalAt_conjAtSplit_of_ne, one_mem (levelGU n 𝔑)]⟩),
  commute_conjAtSplit ⟨mul_mem (by simp) hκ.1, by simp⟩⟩

lemma mem_heckeAlgebra (h' : 𝔑 ∉ (star w.1).1) {D b} (hb : b ∈ spanOn k D) (hr : ∀ g ∈ D,
  g ∈ GUPlus E n ∧ ∀ d, (∀ m, Commute d (conjAtSplit w m)) → Commute d g) (h : b ∈ fixedToEigen
  (levelGU n 𝔑) (conjAtSplit w)) : b ∈ heckeAlgebra n k 𝔑 := ⟨Submodule.span_mono (by aesop_cat) hb,
  fun _ _ _ π v l κ ↦ (conjAtSplit_dualComponent h' κ.2).elim fun c e ↦
  .trans (by simpa [l κ, l ⟨_, inv_mem c⟩] using congr(π.asAlgebraHom $(Commute.span_right
               (fun | _, ⟨_, i, rfl⟩ => ((hr _ i).2 _ e).map _) _ hb) v)) (h l ⟨_, c⟩)⟩

omit [IsCMField E] in
lemma commute_scalar_GL z (g : GL n (𝔸f E)) : Commute g (.scalar n z) := (g.scalar_commute z).symm

/-- Let K₀ be quadratic, x a finite idele of K₀, z the scalar matrix of the conjugate of x. Then
z is a unitary similitude, and a frame for c·1 if the rational c equals the module of the
norm of x to ℚ. -/
lemma centralScalar_mem_GU x : centralScalar x ∈ GU E n ∧ ∀ c : ℚ, c = finIdeleAbs
  (x.map (adeleNorm ℚ _)) → IsScalarFrame (centralScalar x : GL n (𝔸f E)) c := mem_GU _ (by
  simp [smul_one_eq_diagonal]
  intro; generalize x.1 = y; revert y
  exact denseRange_algebraMap_finAdele.eq (by simp [← map_mul, ← map_star_CM,
    ← norm_maximalRealSubfield_eq_mul_star, ← Algebra.norm_eq_of_ringEquiv
    (CMExtension.equivMaximalRealSubfield ℚ _), RingHom.ext_iff]))

lemma tau_mem_spanOn {j} : heckeSum n k w j ∈ spanOn k (range (heckeIsogeny w)) :=
  _root_.sum_mem (by aesop)

lemma evalAt_centralScalar_of_ne {w u : FinPlace E} (h : u.below _ ≠ star (w.below (QuadField d₀)))
  x : (centralScalar (n := n) ((locIdele w x).map (adeleNorm _ E))).map (evalAt u) = 1 := by
  ext1; simp (disch := grind [below_star, star_star]) [adeleNorm_locIdele, adeleMap_apply _ rfl]

/-- At a split place w, the element `heckeIsogeny` attached to w and any subspace U is a similitude
with integral inverse. -/
lemma heckeIsogeny_mem_GUPlus w U : heckeIsogeny w U ∈ GUPlus E n := have ⟨ht, _, hd⟩ :=
    (basicCosetRep_spec U).1; by
    have L (g : GL n _) a (h : a ∈ Ô _) (H : ∀ i j, v (a w * g i j) ≤ 1) i j : a * locGL _ g i j
      ∈ _ := mem_Ô.2 ((and_forall_ne w.1).1 (by by_cases i = j <;> simp_all [locGL, mem_Ô]))
    use mul_mem (centralScalar_mem_GU _).1 (by simp)
    erw [_root_.mul_inv_rev, Units.val_mul, ← smul_eq_mul_diagonal, ← transpose_smul,
      ← mul_smul_comm, ← star_smul]
    exact IsIntMatrix.isInt_transpose
      (.mul (by simpa [ht] using! L (transposeGL (basicCosetRep U)) 1) (.isInt_conjTranspose (L _ _
      ((adeleMap_mem_Ohat _).2 (pow_mem (adeleNorm_mem_Ohat (by simp +contextual +decide [mem_Ô,
      ← and_forall_ne w.1])) _)) (by simpa [mul_comm (exp _), inv_def, hd, mul_pow,
      mul_assoc] using! (mul_le_one' (pow_le_one' (v_uniformizer_inv_mul_le_one_iff.2 (by
      erw [(isEquiv_comap_locMap _ rfl).lt_one_iff_lt_one, ← toNormedField.norm_lt_one_iff,
        norm_localNorm]
      simp +decide)) _) <| (IsIntMatrix.isInt_transpose (R := (LocInt _).1) ht).adjugate · ·)))))

include h

lemma SafePlace.mem_levelSpace_conjAtSplit : x ∈ levelSpace (π.comp (conjAtSplit s.1)) (Kw n _) :=
  fun ⟨_, a⟩ ↦ h ⟨_, mem_levelGU_of_local (by simp) (conjAtSplit_mem_intGL_iff.2 a) fun _ _ ↦
  ⟨1, by simp (disch := grind [IsSafe, below_star, star_star]) [evalAt_conjAtSplit_of_ne]⟩⟩

lemma asAlgebraHom_tau : π.asAlgebraHom (heckeSum n k s.1 s.2) x =
  π (centralScalar (unifNorm s.1.1 ^ s.2)⁻¹) (heckeGL (π.comp (conjAtSplit s.1)) s.2
  x) := by simpa [heckeIsogeny,
  heckeGL_eq_sum (SafePlace.mem_levelSpace_conjAtSplit s h)] using by congr!; aesop

/-- For a safe split place w and j in ℕ, the element τ_{w,j} as a member of the Hecke algebra of
level K(𝔑) over k. -/
def tauHecke : heckeAlgebra n k 𝔑 := ⟨_, mem_heckeAlgebra (s.1.2.2.2 _ (below_star _))
  tau_mem_spanOn (by simp [heckeIsogeny_mem_GUPlus]; simp_all [heckeIsogeny, commute_scalar_GL])
  fun _ _ _ π _ h ↦ (asAlgebraHom_tau s h).symm.subst (map_mem_levelSpace_of_commute
  ((isBiInvariant_basicDoubleCoset _).heckeFun_mem (SafePlace.mem_levelSpace_conjAtSplit s h) ⟨_,
  conjAtSplit_mem_intGL_iff.1 ·.2.2.1⟩) (by simp [commute_scalar_GL]))⟩

lemma asAlgebraHom_tauHecke_comm : let T s := π.asAlgebraHom (tauHecke s).1; T s (T s' x) =
    T s' (T s x) := by
  intro; repeat erw [asAlgebraHom_tau _ ((tauHecke _).2.2 h), asAlgebraHom_tau _ h,
    ← map_heckeFun (π _)]
  refine congr($((commute_scalar_GL ..).map π) $(heckeSplit_comm (π :=
    .comp _ (.domRestrict ..)) s.1.1.2 s'.1.1.2 _ _ ?_ ?_)) <;> exact (mem_sphericalAt_iff
    (by grind)).2 (SafePlace.mem_levelSpace_conjAtSplit _ h)
  all_goals first | exact fun _ ↦ congr($((commute_scalar_GL ..).map π) _).symm | simp

omit h

open LinearMap Submodule

/-- Suppose each π* = F(u_{i,1}) is injective with image containing the Δ_i-invariants, and
level I(w) contains all g_D at w. Then commuting t_{w,j} on F(Z), Z the base of the model,
satisfy π*t_{w,j} = ∑_{dim
D = j} u_{g_D}* on I(w), and ∑ (b·p(τ))_g Ψ(u_g*) = ∑ b_g Ψ(u_g* p(t)) on deep levels (p a
word, Ψ additive, b supported on `GUPlus`).

Known result: Hecke algebra of a pair and its action by correspondences on the base of a tower. -/
lemma Model.exists_commuting_tau_ops {E : Type} [Field E] [CMBase E]
    {𝔑 : NumberField.RingOfIntegers E} [HasQuadSubfield d₀ E] {ν R} {T : Model n _ 𝔑 ν R} {F :
  _ ⥤ ModuleCat.{2} k} (hi : ∀ i, Function.Injective (F.map (T.leg i ⟦1⟧).op)) (hd : ∀ i y,
  (∀ δ, F.map (T.deck i δ).asHom.op y = y) → y ∈ (F.map (T.leg i ⟦1⟧).op).hom.range)
    {I : SafePlace 𝔑 →
  _} (p : ∀ w U, heckeIsogeny w U ∈ T.s (I w)) : let u i q := (F.map (T.leg i q).op).hom
  ∃ t : _ → End k _, (∀ s s', Commute (t s) (t s')) ∧ (∀ w j, u (I w) ⟦1⟧ ∘ₗ t (w, j) =
    cosetSum (u _) (heckeSum n k w j)) ∧ ∀ k' [CommRing k'] (L : List _), ∀ b ∈ spanOn k' (GUPlus E
    n), ∀ᶠ i in .atTop, ∀ {N} [AddCommGroup.{2} N] [Module k' N] (Ψ : _ →+ N), cosetSum (Ψ <|
    u i ·) (b * (L.map tauHecke).prod.1) = cosetSum (Ψ <| u i · ∘ₗ (L.map t).prod) b := by
  intro u
  refine .imp (fun t ht ↦ (fun K ↦ ⟨fun s s' ↦ have A L := K.2 k L _ (OneMemClass.one_mem
      (heckeAlgebra _ _ 𝔑)).1; ((A [s, s']).and (A [s', s])).exists.elim fun i ⟨a, b⟩ ↦ (cancel_left
      (hi i)).1 (by simpa [asAlgebraHom_tauHecke_comm s, ↓single_one_mem_levelSpace, by
                      simpa using b (.id _)] using (a (.id _)).symm), K⟩) ⟨ht, fun k _ L ↦ L.rec (by
    simp [End.one_eq_id]) fun s L ih b ↦ closure_induction (by simp) (fun _ _ _ _ ↦ (·.mp <| ·.mono
    (by clear * -; simp_all))) fun | _, _, ⟨g, H, rfl⟩ => (ih _ (spanOn.mul (Submodule.subset_span
    (by tauto)) (tauHecke s).2.1 (by bound))).mp ((T.eventually_translate (I s.1) H).mono
    fun i ⟨_, f, H⟩ h _ _ _ _ ↦ ?_)⟩) ⟨Prod.rec _, fun w j ↦ codRestrictOfInjective_comp _ _ (hi _)
    fun x ↦ hd _ _ (T.deck_comp_leg _ · |>.elim fun κ
    h ↦ by simpa [tauHecke, ← F.map_comp_apply, ← op_comp, *, u] using congr(($((tauHecke (w,
    j)).2.2 single_one_mem_levelSpace κ)).coeff.linearCombination k (u _) x))⟩
  simp [tauHecke] at h ⊢; rw [h, ← map_sum]; congr with _
  simpa [← F.map_comp_apply, ← op_comp, H, p, T.one_mem,
    u] using congr(F.map f.op ($(ht ..) _)).symm

end

attribute [-instance] instCoeTCOfCoe

variable {E n : Type} [Field E] [NumberField E] [Fintype n] (w : FinPlace E)

attribute [local simp] Matrix.single_apply
  expUnit_eq_one_iff adicCompletionIntegers.isUnit_iff_valued_eq_one
  Subgroup.ofDiv exists_eq_mul_iff_v_le Matrix.transvection funext_iff

/-- For N ≥ 1 and a finite place w, some character of 1 + ϖM_N(O_w) is nontrivial on every
unipotent radical (`IsCuspidalType`) and trivial on 1 + ϖ²M_N(O_w). -/
lemma exists_isCuspidalType N [NeZero N] : ∃ θ, IsCuspidalType (localCongruence (Fin N) w 0) θ ∧
    ∀ k, k.1 ∈ localCongruence _ w 1 → θ k = 1 := by
  obtain ⟨_, a, ha⟩ := Fact.mk (CharP.prime_ringChar (ResField w)),
    Set.mem_range.1 ⟨_, v_uniformizer w⟩
  let h := Field.powerBasisOfFiniteOfSeparable (ResField w) (Extension (ResField w) _ N)
  obtain ⟨b, hb⟩ : ∃ b : Matrix (Fin N) _ (LocInt w), Irreducible (b.map (residue _)).charpoly :=
    h.finrank.symm.trans (finrank_extension ..) ▸ (residue_surjective.comp_left.comp_left _).imp fun
      _ _ ↦ by convert! charpoly_leftMulMatrix h ▸ minpoly.irreducible h.isIntegral_gen
  choose u hu using not_forall.1 (eq_zero_of_forall_hom_eq_zero (a :=
    mk' (v.leAddSubgroup (.exp (-2))) a).mt (by simp_all -dsimp +decide))
  have U {Z} h : u (b.map (·.1) * Z).trace = 0 := u.map_zero ▸ congrArg u ((eq_zero_iff _).2
    (sum_mem fun _ _ ↦ by simpa using! v_matrix_mul_le (b · · |>.2) h ..))
  use (Units.coeHom _).comp (expUnit.comp (.mk' (fun k ↦ .ofAdd (u (b.map (·.1) * (k.1 - 1)).trace))
    fun x y ↦ Multiplicative.ext ?_)), fun ε he _ _ ↦ ?_, fun _ ↦ (by simpa using U ·.2)
  simpa -dsimp [mul_sub, sub_mul, sub_eq_iff_eq_add, add_sub] using
    U (v_matrix_mul_le (A := _ - 1) x.2.2 y.2.2)
  obtain ⟨K, ⟨k, hk⟩, q, -, d, rfl⟩ := (isValuationPair_valuationSubring _).smith_normal_form ε
  rw [charpoly_map, ← charpoly_units_conj' k, ← charpoly_map] at hb
  let := Prop.linearOrder
  obtain ⟨j, i, ⟨⟩, _⟩ := by simpa [BlockTriangular] using (hb.2 <| BlockTriangular.charmatrix (b :=
    (d · = 0)) · |>.det_fintype.trans (prod_Prop _)).mt (by rintro ⟨⟩ <;> simp_all
    [← charmatrix_toSquareBlock, ← charpoly.eq_1, -det_classical,
    card_subtype, Pi.isUnit_iff, isUnit_iff_degree_eq_zero, IsIdempotentElem.iff_eq_one_of_isUnit])
  obtain ⟨t, rfl⟩ : (k⁻¹ * b * k) j i * d i ∣ a := IsUnit.dvd (by aesop)
  let s := Matrix.single i j t
  have : s * Matrix.diagonal d = 0 ∧ .single i j (d i * t) = Matrix.diagonal d * s := by aesop
  use ⟨_, mem_localCongruence_zero.2 ⟨_, reduceGL.normal_ker.conj_mem _
    (mem_localCongruence_zero.1 ⟨transvectionGL_mem_intGL (a := d i * t) (by
    lia : i ≠ j) (by simp_all +decide [v.mem_integer_iff]), by aesop⟩).2 ⟨_, k, hk⟩⟩⟩, q⁻¹ * s * K⁻¹
  simp [mul_add, add_mul, mul_sub, mul_assoc, ← s.mul_assoc, -coe_units_inv, *]
  simpa [s, ← hk, ← mul_assoc, trace_mul_cycle _ s, trace_mul_single, mul_apply, ← map_inv,
    Matrix.diagonal] using! hu

/-- Let the open H contain the integral points trivial at S, each w in S having w or w̄ in B.
Then some multiple 𝔑 of N in O_E lies exactly in the primes of B and those containing N, and
u ∈ H whenever ū has principal level 𝔑. -/
lemma exists_levelGU_conj_le [IsCMField E] {H} (hH : H.IsOpen) {S B : Finset (FinPlace E)} (hS :
    Kf E n ⊓ trivialOn n S ≤ H) (hB : ∀ w ∈ S, w ∈ B ∨ star w ∈ B) N : ∃ 𝔑, N ∣ 𝔑 ∧
    (∀ w, 𝔑 ∈ w.1 ↔ N ∈ w.1 ∨ w ∈ B) ∧ ∀ u, invTransposeGL u.1 ∈ levelGU n 𝔑 → u ∈ H := by
  choose t ht h using isOpen_pi_iff'.1 ((isCompact_Kf.diff hH).image (f := fun g (w : B) ↦ g.atPlace
    w.1) (by fun_prop)).isClosed.1 1 (by simp_all [LE.le]; grind [atPlace_star_eq_one_iff])
  choose k hk using (ht · |>.rec (·.mem_nhds) |> eventually_localCongruence_subset |>.exists)
  have ⟨_, c, y, e⟩ := exists_ideal_pow_eq_span_singleton (∏ w, w.1.1 ^ (k w + 1))
  use N * y
  simp [mul_mem_iff_mem_or_mem, ← span_singleton_le_iff_mem (x := y), ← e, prod_le, pow_le_iff, c,
    IsMaximal.out.le_iff_eq ne_top', asIdeal_injective.eq_iff, levelGU, congruenceGL]
  intro u _ U hu
  simpa using (h (fun w _ ↦ hk w ⟨mem_Kf_iff.1 (inv_mem U) _, fun i j ↦ .trans
    (by simpa [← evalAt_apply, eq_comm, -coe_units_inv] using! hu j i w) (mul_le_mul'
    (coe_algebraMap_mem ..) (v_algebraMap_eq_intValuation y ▸ (intValuation_le_pow_iff_dvd
    ..).2 (e ▸ (Finset.dvd_prod_of_mem _ (by simp)).pow c)))⟩) ⟨_, ⟨inv_mem U, ·⟩, rfl⟩)
