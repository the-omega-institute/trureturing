/- GID: D5/S3/Zeros/GRH/Lib/Cyclotomic/Kolyvagin/ComponentBound
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/Cyclotomic/Kolyvagin/ComponentBound
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.Cyclotomic.Kolyvagin.ComponentBound. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/Cyclotomic/Kolyvagin/ComponentBound.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.PadicHodge.Crystalline.RegularityFrobenius
import D5.S3.Zeros.GRH.Lib.ClassField.GaloisCohomology.TameCocycles
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Known result: Stickelberger annihilation and the Kolyvagin–Rubin bound for odd twisted
components. Here the value is taken at a negative integer in place of zero. For an integer X
divisible by the Stickelberger elements, 4X² kills the odd component at every prime, and for large
primes ℓ at most v_ℓ(X)+1 Galois elements detect its classes. Source: J. Coates, W. Sinnott, An
analogue of Stickelberger's theorem for the higher K-groups, Invent. Math. 24 (1974) 149-162; K.
Rubin, Euler Systems, 2000, III.4, Thm 4.6.

Known result: Kolyvagin's derivative classes of the Euler system of Gauss sums. Here they carry a
Tate twist and a Dirichlet character, and they are cocycles over the rationals that vanish at one
fixed element. The file treats ramification, the Frobenius-to-inertia relation and the link of the
bottom class with the Stickelberger element. Source: K. Rubin, Kolyvagin's system of Gauss sums,
Arithmetic Algebraic Geometry (Texel 1989), Progr. Math. 89, 1991, 309-324; with a Tate twist, G.
Banaszak, W. Gajda, Euler systems for higher K-theory of number fields, J. Number Theory 58 (1996).

This file: Kolyvagin derivative cocycles of Gauss sums: ramification and the Frobenius-to-inertia
relation. Artin reciprocity and Kummer duality relations for twisted cocycles over cyclotomic
fields. Stickelberger annihilation of odd twisted classes; Kolyvagin-Rubin bound on detecting
elements. -/

open Classical Finset Function HasEnoughRootsOfUnity MonoidHom MulAut Multiplicative NeZero
  Pointwise QZ Representation Submodule DiscreteUnits ZMod Ideal.Quotient

variable {O : Type} [CommRing O] {B : ClosurePlace} {g : Gal(Ω/ℚ)} {u} {m a M N l n e : ℕ} [NeZero
  m] [NeZero N] [Fact l.Prime] [Algebra ℤ_[l] O] {ψ : DirichletCharacter O N}

lemma IsFrob.sub_nsmul_mem_principalUnits (hg : IsFrob B a g) (hu : B (m • u).toMul = 1) :
  galUnitsRep g u - a • u ∈ _root_.principalUnits B :=
  show B _ < 1 by simp_all [ne, div_sub_one, hg.2, -AlgEquiv.smul_def]

lemma eq_of_mem_principalUnits {a b} (h : B m = 1) (H : (rootPowHom Ω m).1 (a - b) ∈ principalUnits
  B) : a = b := sub_eq_zero.1 ((rootPowHom Ω m).2.1 (DiscreteUnits.ext (eq_of_val_sub_lt_one h
  congr($(((rootPowHom ..).2.2 _).1 ⟨_, rfl⟩).1) (by simp) (by rwa [map_zero]))))

/-- Rigidity: let N = ma with a a unit at B. An element of the inertia group of B that fixes the
m-th roots of unity fixes the N-th roots of unity. -/
lemma mem_cycloGalGroup_of_inertia (i : g ∈ inertiaGroup _ B) (h : B a = 1) (d : m * a = N) (e :
  g ∈ cycloGalGroup m) : g ∈ cycloGalGroup N := cycCharMod_eq_one_iff.2 fun z u ↦ DiscreteUnits.ext
  (inertia_fixes_root_of_unit i h rfl (by simpa [ne, ← d] using congr(B ($u).toMul))
  congr($(cycCharMod_eq_one_iff.1 e (a • z) (by rwa [smul_smul, d])).1))

lemma exists_inertia_cycChar_eq (h : B l < 1) (c : l.Coprime a) : ∃ γ ∈ inertiaGroup Gal(Ω/ℚ) B,
  (cycChar Ω l γ).1 = a := (exists_comap_intQpBar_eq h).rec fun e h ↦ (exists_galois_restrict _ _
  e).rec fun f k ↦ (@exists_inertia_cyclotomicGp_eq l {} _ c).imp' f fun _ ↦
  .imp (h ▸ .map k) (cycChar_eq_of_equivariant l (k _) ▸ ·)

lemma cycPowDirichlet_smul (H : (cycCharMod Ω (N * m) g).1 = a) {M} [AddCommGroup M] [Module O M]
  {x : M} (hx : m • x = 0) : (cycPowDirichlet l e ψ g).1 • x = (a ^ e * ψ a) • x :=
  (_root_.map_dvd (algebraMap _ O) (((PadicInt.unitCoeff_spec (ne (m : ℤ_[l]))).dvd.trans (by
  simpa [PadicInt.valuation] using (pow_dvd_cycChar_sub_iff _).2 (cycCharMod_eq_of_dvd
    (.mul_left pow_padicValNat_dvd N) H))).trans (sub_dvd_pow_sub_pow ..))).rec fun b h ↦ by
  linear_combination (norm := (simp [cycPowDirichlet,
    cycCharMod_eq_of_dvd _ H]; module)) ψ a • (h • x + b • hx)

/-- Kolyvagin derivatives. Let Υ* = cyc^{e+1}ψ, M = Nlⁿ, P a finite set of primes ≡ 1 mod cM, B
above a prime p ≡ 1 mod M∏P. There are Υ*-cocycles κ_S (S ⊆ P) in O/lⁿ, zero at γ and on
inertia over ℚ(μ_N) off l, p and S, such that: if κ_∅ kills inertia at B, then (Υ*(γ) − 1)∑
m_c(a/M)a^eψ(a) = 0 in O/lⁿ, summed over units a mod M (m_c = `floorDiff` c); and for q
in P∖S and a Frobenius φ at A above q, κ_S(φ) is a value of κ_{S∪{q}} on inertia at A.

Known result: Kolyvagin's derivative classes of the Euler system of Gauss sums. -/
lemma exists_kolyvagin_cocycles e c γ {P : Finset Nat.Primes} (hP : ∀ q ∈ P, q ≡ 1 [MOD c * (N * l ^
  n)]) {p : Nat.Primes} (h2 : p ≡ 1 [MOD N * l ^ n * ∏ q ∈ P, ↑q]) (h3 : B.valuation p < 1) : ∃ κ :
  _ → _ → QuotSpan (l ^ n : O), ((∀ τ ∈ inertiaGroup _ B, κ ∅ τ = 0) →
  (cycPowDirichlet l (e + 1) ψ γ - 1 : O) • ↑(∑ a : (ZMod (N * l ^ n))ˣ, floorDiff c (ofZMod _
  a.1) * (a.1.val ^ e * ψ a.1.val)) = (0 : QuotSpan (l ^ n : O))) ∧ ∀ S ⊆ P, κ S ∈ vanishingCocycles
  (cycPowDirichlet l (e + 1) ψ) _ (inertiaOff N l (insert p S)) ∧ κ S γ = 0 ∧ ∀ q ∈ P, q ∉ S → ∀ A
  φ, IsFrob A q φ → A.valuation (q : Ω) < 1 → ∃ τ ∈ inertiaGroup _ A, κ (insert q S) τ = κ S φ := by
  rcases exists_jacobi_family h3 c, exists_isPlaceOver_prime h3, @nsmul_quot_eq_zero O _ _ l n
    dvd_rfl, eμ : rootPowHom Ω (l ^ n) with ⟨⟨j, hj⟩, ⟨v, o, -⟩, hA, μ, hμ⟩
  let := @algebraOfModule _ _ _ (AddCommGroup.zmodModule hA)
  choose! L hL using fun q (h : q ∈ P) ↦ ((isCyclic_units_prime q.2).1.rec fun g a ↦ ⟨_, g,
    monoidHomOfForallMemZpowers_apply_gen a (by simp [orderOf_eq_card_of_forall_mem_zpowers a,
    Nat.totient_prime q.2, (hP q h).of_mul_left.of_mul_left.symm.dvd'])⟩ : ∃ L : _ →* _,
    ofAdd (1 : ZMod (l ^ n)) ∈ L.range)
  let Λ S (d : _ → _) := (∑ a : _ˣ, .smulRight (a.1.val ^ e • .proj (ofZMod (N * l ^ n) a.1))
    (ψ a.1.val : QuotSpan (l ^ n : O))) ∘ₗ asAlgebraHom (ofDistribMulAction _ _ᵈᵐᵃ (_ →
    ZMod (l ^ n))) (∏ q ∈ S, ∑ u, .single (.mk (ofAdd (ofZMod _ u.1))) ((L q u).toAdd - d q))
  have Λ1 {q S} (h : q ∉ S) d F : Λ (insert q S) d F = Λ S d fun x ↦ ∑ u, ((L q u).toAdd - d q) * F
    (x + ofZMod q u) := by simp [Λ, *, mul_comm _ (S.prod _), sum_fn, DomMulAct.smul_apply,
    add_comm, -MonoidAlgebra.single_sub]
  obtain ⟨X, y, hy⟩ :=
    fun {m u} [NeZero m] e g ↦ congr(galUnitsRep γ $(cycCharMod_eq_one_iff.1 (by simp [mul_comm] :
    γ⁻¹ * «conj» g γ ∈ cycloGalGroup m) u e)), skolem.1 (j · |>.exists_nsmul (ne (l ^ n)))
  let F g x := invFun μ (galUnitsRep γ (y x) - galUnitsRep (g * γ * g⁻¹) (y x))
  simp_rw [← sub_eq_zero (b := j _), ← hy, map_nsmul, ← smul_sum, ← smul_sub] at hj
  choose D T V Q _ W using @hj
  have S {M x g} [NeZero M] h hx : μ (F g x) = _ := invFun_eq ((hμ.2 _).2 (by
    simpa [smul_sub] using congr(-galUnitsRep γ $(@T M _ h x hx (γ⁻¹ * «conj» g γ) 1
      (by simp [mul_comm])))))
  refine ⟨(Λ · 0 <| F ·), (forall₂_and.1 fun I hI ↦ (?_ : _root_.id _ ∧ _)).imp_left (· ∅ nofun)⟩
  have h := h2.of_dvd (mul_dvd_mul_left _ (prod_dvd_prod_of_subset _ _ _ hI))
  generalize eM : (_ * _ : ℕ) = M at h
  obtain ⟨_, b, z, dv⟩ := (⟨by simp [← eM, ne, prod_eq_zero_iff]⟩ : NeZero M), Dvd.intro _ eM,
    (natCast_eq_zero_iff M · |>.2), fun {q} h ↦ eM ▸ (dvd_prod_of_mem (a := q) _ h).mul_left _
  have H {g} {a : ℕ} (hg : (cycCharMod Ω (N * l ^ n) g).1 = a) {S d f} (ha : ∀ q ∈ S, q ∈ I ∧
    ∃ v, f q = (L q v).toAdd + d q ∧ v.1 = a) {G F} (h : ∀ {x}, M • x = 0 → G x = F (a • x)) :
    (cycPowDirichlet l e ψ g).1 • Λ S d G = Λ S f F := by
    induction' S using Finset.induction with q _ _ ih generalizing F G
    · simpa [Λ, smul_sum] using Fintype.sum_equiv (.mulLeft (cycCharMod Ω _ g)) _ _ fun _ ↦ by
        simp [cycPowDirichlet_smul hg (hA _), Algebra.smul_def, ← map_nsmul, *]; ring
    obtain ⟨⟨i, v, _⟩, k⟩ := by simpa using ha
    simpa [*] using ih k fun x ↦ sum_equiv (.mulLeft v) (by simp) (by simp [dv i, ← map_nsmul, *])
  obtain ⟨⟨hΛ, U⟩, d, τ, i, π, r, u, hr, t⟩ := by simpa using And.intro (@H 1 1) (fun {r J d} k (j :
    J ⊆ I) n ↦ @H 1 _ (.trans (by simp) ((natCast_eq_natCast_iff ..).2 (hP r k).of_mul_left.symm)) J
    d _ fun q h ↦ ⟨j h, _, rfl, invFun_eq (CharP.cast_ne_zero_of_ne_of_prime _ r.2 (mt (Subtype.ext
    · ▸ h) n)).isUnit⟩), dvd_of_mul_left_dvd b, exists_isTameGeneratorFor Gal(Ω/ℚ) (l ^ n) o
  have hE {i J} : J ⊆ I → ∀ {d}, Λ J d (F i) = Λ J 0 (F i) := J.strongInductionOn fun J ih hS d ↦
    (hΛ (by simpa +contextual) (by simp)).trans (J.induction_on' (motive := fun T ↦ Λ J (T.piecewise
    d 0) _ = _) rfl @fun r T m _ k ↦ .trans (by
    obtain ⟨s, o, e⟩ := dv (hS m), hI (hS m), ih _ (erase_ssubset m)
    have D {x} w : ∑ b, F i (x + ofZMod r b) = F i (r.1 • x) := hμ.1 (have ⟨k + 1, _, e⟩ := ((@D
      _ _ h x w r _ s (hP r o).of_mul_right.coprime_of_modEq_one.symm).of_nsmul
        out).exists_nsmul_eq_zero
      by linear_combination (norm := simp [S h, ← map_nsmul, smul_comm M, *]) -X e i)
    rw [← insert_erase m, Λ1, Λ1, ← zero_add (Λ _ _ _), ← smul_zero (d r), ← sub_eq_zero.2
      (U o _ _ D), e, ← e, ← map_sub, ← _root_.map_smul, ← map_add, hΛ] <;> simp +contextual [k,
      mul_sum, @hS _, sum_eq_add_sum_units, sub_mul, subset_iff]))
  have ev {g A a} f hg (hi : IsFrob A 1 g) b r hk (hb : galUnitsRep g r - r = μ b) (E : ∀ {x},
    M • x = 0 → A (l ^ n • (y x - floorDiff c x • r)).toMul.1 = 1) {x} hx :
    a • (floorDiff c x * b) - F g x = floorDiff c (a • x) * b := eq_of_mem_principalUnits hk (by
    obtain ⟨t, u⟩ := @T M _ h x hx g 1 (by simpa), T h hx γ a f
    convert sub_mem (hi.sub_nsmul_mem_principalUnits (@E (a • x) (by simp [smul_comm M, *])))
      (nsmul_mem (hi.sub_nsmul_mem_principalUnits (E hx)) a)
    linear_combination (norm := (simp [eμ, S h hx, ← hb, ← zsmul_eq_mul,
       smul_sub, -nsmul_eq_mul]; abel)) cycCharMod_eq_iff_unitsRep.1 (hi.cycCharMod_eq hk) u -
      cycCharMod_eq_iff_unitsRep.1
      (cycCharMod_eq_of_dvd d f) t - X t g)
  refine ⟨fun R ↦ ?_, ⟨(IsLocallyConstant.iff_eventually_eq _).2 fun g ↦ .mono (.all fun b ↦
    ((isLocallyConstant_smul _).comp_continuous (by fun_prop)).eventually_eq g) fun _
    H ↦ hΛ (by simp) (exists_ofZMod · |>.rec fun b e ↦ congr(invFun μ (_ - $(DiscreteUnits.ext
    (e ▸ H b))))), fun g i ↦ ?_, fun g ⟨A, ⟨t, j, i⟩, hA⟩ ↦ ?_⟩, by simp [F, ← Pi.zero_def,
    μ.map_zero ▸ leftInverse_invFun hμ.1 0], fun q k hqI A φ hφ hB ↦ ?_⟩
  · linear_combination (norm := (simp [↓R τ i, ↓map_sub, ↓map_nsmul, ↓sub_smul,
      Λ, ↓cycPowDirichlet_smul (cycCharMod_eq_of_dvd b zmod_eq_natCast_val) (hA _),
      Algebra.smul_def, ↓nsmul_eq_mul', -natCast_val]; ring)) @H γ _ (cycCharMod_eq_of_dvd b
     zmod_eq_natCast_val) ∅ 0 0 nofun ((_ : ℕ) • _ - _) (floorDiff c · * 1) (ev zmod_eq_natCast_val
      (decompGroup_le_cycloGalGroup h3 h i.1) i _ _ ((h.of_dvd
      d).coprime_of_modEq_one.valuation_eq_one h3) (eμ ▸ t) (by simp [↓← o.ordRat_eq_zero_iff,
      smul_sub, smul_comm, Q h ·, o.ordRat_ofBase, o.isUniformiser_iff.1 u, hr]))
  · linear_combination (norm := (simp [↓cycPowDirichlet_smul (cycCharMod_eq_of_dvd b
      zmod_eq_natCast_val) (hA _), Algebra.smul_def, hE, ↓map_nsmul, -natCast_val]; ring)) -@H g _
      (cycCharMod_eq_of_dvd b zmod_eq_natCast_val) I 0 _ (fun q h ↦ ⟨h, _, rfl,
     cycCharMod_eq_of_dvd (dv h) zmod_eq_natCast_val⟩) ((_ : ℕ) • _) (F (g * i) - F g) @fun x w ↦
      hμ.1 (have u := X (T h w g _ zmod_eq_natCast_val)
      by linear_combination (norm := (simp [S h, smul_comm M, w,
        cycCharMod_eq_of_dvd d zmod_eq_natCast_val, -natCast_val]; abel)) u g - u (g * i) +
          map_cycCharMod_mul μ g (F i x))
  · simp [LE.le.ge_iff_eq] at hA
    exact (Λ I 0).map_zero ▸ hΛ (by simp) (by
      simpa using ev zmod_eq_natCast_val (mem_cycloGalGroup_of_inertia i (by simp +contextual [*])
        (N.mul_assoc .. ▸ eM) t) i 0 0 (by simp [j]) (by simp) (by simpa using V h · _ hA.1) ·)
  obtain ⟨⟨L, eL⟩, ⟨g, _⟩, p1, C⟩ := skolem.1 (intCast_surjective <| L q · |>.toAdd), hL q k,
    h2.of_mul_left.of_dvd (dvd_prod_of_mem _ k),
    eM ▸ (hP q k).of_mul_left.coprime_of_modEq_one.mul_right
    (.prod_right fun r a ↦ (Nat.coprime_primes q.2 Fact.out).2 (hqI <| Subtype.ext · ▸ a))
  obtain ⟨vM, ⟨τ, hτ, hτ'⟩, w⟩ := C.valuation_eq_one hB, exists_inertia_cycChar_eq hB
    (val_coe_unit_coprime g⁻¹).symm, (Nat.modEq_and_modEq_iff_modEq_mul C).1 ⟨p1, h⟩
  refine ⟨τ, hτ, (Λ1 hqI ..).trans ((U k le_rfl hqI @fun x z ↦ eq_of_mem_principalUnits
    ((C.of_dvd_right d).valuation_eq_one hB) ?_).trans (hE le_rfl))⟩
  have s b : (q * M) • (x + ofZMod q b) = 0 := by simp [← map_nsmul, mul_smul, z]
  have o γ : galUnitsRep γ⁻¹ _ ∈ principalUnits A := (val_smul_lt_one γ).1 (by
    have a := by simpa using (val_smul_lt_one γ).2 hB
    simpa using! p1.coprime_of_modEq_one.symm.valuation_eq_one a |> fun v ↦ sub_mem (sum_mem (t :=
      univ) fun u _ ↦ sub_mem (zsmul_mem ((hτ.conj γ).sub_nsmul_mem_principalUnits (V w (s ↑(g * u))
      _ v)) (L u)) (mem_comap.1 (Ideal.mem_of_dvd ((principalUnits _).toIntSubmodule.comap
      (.toSpanSingleton ..)) ((intCast_zmod_eq_zero_iff_dvd (L (g * u) - L u - 1) _).1
      (by simp [*])) (W h z q _ (ofZMod q (g * u)) (by simp [← map_nsmul]) p1.symm.dvd' a))))
      ((hφ.conj γ).sub_nsmul_mem_principalUnits (V h z _ v)))
  obtain ⟨i, t, m, b, rfl⟩ := T h z _ _ (hφ.cycCharMod_eq vM), fun u ↦
    T w (s (g * u)) τ _ zmod_eq_natCast_val,
    Equiv.sum_comp (.mulLeft g) fun u ↦ (L u - 1) • (y (x + ofZMod q u) - y x), exists_ofZMod z
  simp [← map_nsmul, ← cycCharMod_eq_of_dvd _ zmod_eq_natCast_val,
    cycCharMod_eq_of_dvd _ ((pow_dvd_cycChar_sub_iff 1).1 (sub_eq_zero.2
    hτ' ▸ dvd_zero _)), hτ.cycCharMod_eq, *, -inv_coe_unit] at t
  have ⟨k + 1, _, e⟩ :=
    (D w (s 0) q (by simp) (hP q k).of_mul_right.coprime_of_modEq_one.symm).exists_nsmul_eq_zero
  convert sub_mem (cycCharMod_eq_iff_unitsRep.1 (@zmod_eq_natCast_val _ _ (cycCharMod Ω (k.succ *
    l ^ n) γ).1) ?_ ▸ nsmul_mem (o 1) _) (o γ⁻¹)
  · linear_combination (norm := (simp [eμ, ← eL, ← zsmul_eq_mul, S w, s, z,
      mul_smul, smul_comm M, smul_sub]; abel)) congr(∑ u, L u • $(X (t u) τ)) - X i φ
  linear_combination (norm := (simp [sub_smul, smul_sub, sub_nsmul, q.2.one_le, Nat.totient_prime
    q.2, sum_eq_add_sum_units, smul_comm (L _), ← smul_sum]; module)) e + k.succ • (congr(∑ u,
    L u • $(t u)) - i - l ^ n • m)

attribute [-simp] _root_.map_smul

variable {O M : Type} [CommRing O] {N l m e q ν : ℕ} [NeZero N] [NeZero m] [Fact l.Prime]
  [Fact q.Prime] [PadicIntegerRing O l] {ψ : DirichletCharacter O N} {g τ φ : Gal(Ω/ℚ)} {B :
  ClosurePlace} [AddCommGroup M] [Module O M] {χ : _ →* Oˣ} {s z} (hz :
  z ∈ vanishingCocycles χ M s) {a : ℕ} (ha : l.Coprime a)
  (h1 : a ≡ 1 [MOD N]) (hB : B.valuation q < 1) (hφ : IsFrob B q φ) {x} (hx : x ∈ component l e ψ ν)

lemma cycPowDirichlet_smul_eq_self (hg : g ∈ cycloGalGroup (N * m)) {y : M} (h : m • y = 0) :
  (cycPowDirichlet l e ψ g).1 • y = y ∧ (cycPowDirichlet l e ψ g)⁻¹.1 • y =
  y := by simp [← map_inv, cycPowDirichlet_smul (a := 1) _ h, mem_ker.1, *]

/-- For a locally constant cocycle z on Gal(ℚ̄/ℚ) for a character χ, the open subgroup of the g
with z(g) = 0. -/
noncomputable def zeroSubgroup := OpenSubgroup.mk (cocycleKer χ hz.2.1) (hz.1 _)

lemma not_cycloGalGroup_le_zeroSubgroup γ (hγ : z γ = 0) (h : ((χ γ).1 - 1) • z ≠ 0) f [NeZero f] :
  ¬cycloGalGroup f ≤ zeroSubgroup hz :=
  fun H ↦ h (funext (by simpa [*] using sah hz.2.1 γ · (H (by simp [mul_right_comm]))))

omit [PadicIntegerRing O l] in
lemma finite_vanishingCocycles [Finite M] (h : ∀ g : cycloGalGroup (N * l ^ n), ∀ {y : M},
  (χ g).1 • y = y) (hs : ↑(cycloGalGroup N) ∩ inertiaAbove (placesDividing ℚ l)ᶜ ⊆ s) :
  Finite (vanishingCocycles χ M s) := have := discreteTopology_bot
  let : TopologicalSpace M := ⊥; let := MulAction.compHom M χ; (selmerZ1.finite_unramified_cocycles
      (.of (charRep ..) (continuousSMul_iff_stabilizer_isOpen.2 fun _ ↦ Subgroup.isOpen_mono
      (h ⟨·, ·⟩) Fact.out).1) ((finite_natCast_mem N).union (placesDividing ℚ l).toFinite)).subset
      fun _ ⟨a, b, _⟩ ↦ ⟨⟨a.continuous, b⟩, by simp_all [inertiaAbove, Set.subset_def]; grind
      [IsPlaceOver.valuation_natCast_eq_one_iff, cycCharMod_of_mem_inertiaGroup]⟩

/-- For B above l and a ≡ 1 mod N prime to l, some element of the inertia group of B has value
a^e under the character cyc^e·ψ. -/
lemma exists_inertia_cycPowDirichlet_eq (ha : l.Coprime a) (h1 : a ≡ 1 [MOD N]) (h : B l < 1) e :
  ∃ i ∈ inertiaGroup _ B, (cycPowDirichlet l
  e ψ i).1 = a ^ e := (exists_inertia_cycChar_eq h ha).imp fun _ i ↦ by simp [cycPowDirichlet, i,
  mem_ker.1 (mem_cycloGalGroup_of_inertia i.1 ((N.coprime_ordCompl Fact.out out).valuation_eq_one h)
  (N.ordProj_mul_ordCompl_eq_self l) (Units.ext (by simp [cycCharMod_prime_pow_eq, i,
  (natCast_eq_natCast_iff ..).2 (h1.of_dvd _), N.ordProj_dvd])))]

include ha h1 hB hφ hx in
/-- Artin reciprocity over K = ℚ(ζ_{Nm}). Let x in `component` have mx = 0, φ be a Frobenius
at B above a prime q ≡ 1 mod Nm, a ≡ 1 mod N prime to l, y in K^×. Suppose at each place off
lq, x kills the decomposition group or y/r^m is a unit for some r fixed by inertia over K.
Then the ord_B(σ_u y) are integers and ∑_u ord_B(σ_u y)u^eψ(u) kills 2(a^e−1)x(φ), where σ_u
raises ζ_{Nm} to the power u ∈ (ℤ/Nm)^×. -/
lemma artin_law_component (hq' : q ≡ 1 [MOD N * m]) (hM : ∀ g, m • x g = 0) {y} (hy : ∀ g :
  cycloGalGroup (N * m), galUnitsRep g y = y) (H : ∀ A, A.valuation (l : Ω) = 1 → A.valuation
  q = 1 → (∃ r, A.valuation (y - m • r).toMul = 1 ∧ ∀ i ∈ inertiaGroup (cycloGalGroup (N * m)) A,
  galUnitsRep i r = r) ∨ ∀ g ∈ decompGroup _ A, x g = 0) {s : _ → _} (hs : ∀ u,
  cycCharMod Ω (N * m) (s u) = u) : ∃ k : _ → ℤ, (∀ u, ordRat ℚ B (galUnitsRep (s u) y) = k u) ∧
  (∑ u, k u * (u.1.val ^ e * ψ u.1.val)) • (2 * (a ^ e - 1) : O) • x φ = 0 := by
  set d : O := 2 * _; let G := cycloGalGroup (N * m)
  obtain ⟨⟨v, ⟨⟨⟩⟩, -, R⟩, D, ⟨Y, Z⟩, y, ⟨⟩⟩ := @exists_rat_place_of_prime q Fact.out,
    decompGroup_le_cycloGalGroup hB hq', hx.2, (ofBase_bijective G).2 ⟨y, hy⟩
  have b u := (R B hB).smul (s u)⁻¹
  choose w hw _ using (b · |>.exists_above (L := fixedFieldOf G))
  have T u := ((b u).ramification_in_tower G (hw u)).1 (decompGroup_le_cycloGalGroup
    (b u).valuation_q_lt_one hq')
  refine ⟨_, fun u ↦ by simpa [T, ← (b u).ordRat_smul (s u)]
    using! (hw u).ordRat_ofBase (Γ := G) y, eq_zero_of_forall_hom_eq_zero fun lam ↦ ?_⟩
  let χ : QZChar G := ⟨_, (hx.1.comp (lam <| d • ·)).continuous.comp continuous_subtype_val,
    (by simp [*, cycPowDirichlet_smul_eq_self ·.2])⟩
  have L (A : ClosurePlace) := (A.valuation_le_one l).eq_or_lt.imp_right fun h g (_ : g.1
      ∈ decompGroup _ A) ↦ show χ.1 g = 0 by
    obtain ⟨δ, ⟨⟩, _⟩ := exists_inertia_cycPowDirichlet_eq (ψ := ψ) ha h1 h e
    have := sah Y δ⁻¹ g (Z _ (.inr ⟨by simp [mul_comm], .inr ⟨A, by simp_all [mul_comm, mul_mem]⟩⟩))
    simp_all [χ, d, mul_smul, sub_smul, cycPowDirichlet_smul_eq_self g.2]
  have U {A v} h g hg := (L A).elim ((by simp [χ, ·]) ∘ Z g.1 ∘ (.inr ⟨cycCharMod_eq_one_of_dvd ⟨_,
    rfl⟩ g.2, .inl ⟨v, (IsPlaceOver.valuation_natCast_eq_one_iff h).1 ·, _, h, hg⟩⟩)) (· g hg.1)
  simpa [sum_smul, χ, (· ∘ ·), ↓cocycle_conj_eq_smul Y, cycPowDirichlet_smul_eq_self (D hφ.1),
    smul_comm d, *, ← zsmul_eq_mul, cycPowDirichlet_smul zmod_eq_natCast_val (hM _)] using
    sum_ord_smul_frob_eq_zero (by
    ext; simp [χ, ← map_nsmul, smul_comm, *]) (char_artinMap_principalIdele_eq_one χ y fun c h ↦ by
    simpa [χ, d, *, two_mul, add_smul,
      cycPowDirichlet_smul_eq_self c.2] using congr(lam ((_ : O) • x (c *
    $h.mul_self)))) (fun u t e ↦ (IsPlaceOver.exists_smul G (hw t) (e ▸ hw u)).rec fun _ a ↦ by
    erw [eq_inv_smul_iff, smul_smul, smul_smul] at a
    simpa [mem_ker.1, mul_inv_eq_one, *] using D a) (s := (⟨_, (normal_ker _).1 _ (D hφ.1) <| s⁻¹
    ·⟩)) (⟨hw ·, by simpa [T] using! hφ.conj _, U (b _)⟩) fun t k ↦ ((L _).elim (H _ ·
    (eq_of_le_of_not_lt (by simp) (R _ · |>.exists_smul Gal(Ω/ℚ) (R B hB) |>.rec fun _ e ↦ k ⟨_, (hw
    _).unique (by simpa [← e, smul_smul] using! t.isPlaceOver_placeOver.smul (⟨_,
    (eq_iff _).1 (hs _).symm⟩ : G))⟩)) |>.symm.imp_left (by aesop)) .inl).imp
    ((t.isPlaceOver_placeOver.artinAt_trivial_iff_decompGroup_le χ).2 · _) (⟨·,
    U t.isPlaceOver_placeOver.isPlaceOver_below⟩)

include ha h1 hB hφ hx in
/-- Reciprocity mod l, for O local with the totient φ(Nl) a unit. Let l kill x in `component`
and a cyc^{e+1}ψ-cocycle κ in a finite O-module that vanishes on inertia over ℚ(μ_N) off l
and a finite set T of primes; let x kill the decomposition groups above the primes of T
other than q, a prime ≡ 1 mod Nl. If 2(a^e − 1)x(φ) ≠ 0 for a Frobenius φ at B above q and
some a ≡ 1 mod N prime to l, then κ vanishes on inertia at B. -/
lemma reciprocity_mod_ell [Finite M] (hN : IsUnit ((N * l).totient : O)) (hq' : q ≡ 1 [MOD N * l])
    (hM : l • x = 0) {κ T} (hκ :
  κ ∈ vanishingCocycles (cycPowDirichlet l (e + 1) ψ) M (inertiaOff N l T)) (hK : ∀ g, l • κ g = 0)
  (hτ : τ ∈ inertiaGroup _ B) (H : ∀ A, A.valuation (q : Ω) = 1 → (∀ r ∈ T, ¬A.valuation r < 1) ∨
  ∀ g ∈ decompGroup _ A, x g = 0) (h0 : (2 * (a ^ e - 1) : O) • x φ ≠ 0) : κ τ = 0 := by
  obtain ⟨_, ⟨π, _⟩, v, hv, _⟩ := @AddCommGroup.zmodModule l (O ∙ κ τ) _ (by simp
    [mem_span_singleton, smul_comm, *]), (DiscreteUnits.ofNeZero (q : Ω) out).exists_nsmul (ne l),
    exists_isPlaceOver_prime hB
  choose s hs using cycCharMod_surjective (N * l)
  obtain ⟨t, b, j, _⟩ := mem_ker.1 (decompGroup_le_cycloGalGroup hB hq' hτ.1),
    Module.finBasis (ZMod l) (O ∙ κ τ), ((rootPowHom Ω l).2.2 (galUnitsRep τ π - π)).2
    (DiscreteUnits.ext (by simp [smul_sub, ← map_nsmul, *]))
  choose L hL using fun i ↦ by simpa using (exists_extend
    (O ∙ κ τ).subtype.toAddMonoidHom ((rootPowHom Ω l).1.comp (b.coord i)) (by aesop_cat))
  choose r hr using (show ∃ r, ∀ g : cycloGalGroup (N * l), L · _ =
    galUnitsRep g r - r from hilbert90_unitsRep ⟨_,
    (hκ.1.comp _).continuous.comp continuous_subtype_val, fun g _ ↦ by erw [cycCharMod_eq_one_iff.1
    g.2] <;> simp [mul_smul, ← map_nsmul, hK, hκ.2.1, cycPowDirichlet_smul_eq_self g.2]⟩)
  choose m hm R using fun i ↦ artin_law_component ha h1 hB hφ hx hq' (congrFun hM) (y :=
    l • r i) (by simp [hK, ← add_eq_of_eq_sub (hr ..), ← map_nsmul]) (fun A a b ↦
    (H A b).imp_left (⟨r i, by simp, fun g c ↦ by simp [← sub_eq_zero, ← hr,
    hκ.2.2 g ⟨A, ⟨cycCharMod_eq_one_of_dvd ⟨_, rfl⟩ g.2, a, c⟩, ·⟩]⟩)) hs
  have F u : (u.1.val ^ e * ψ u.1.val) • b.equivFun.symm (m · u * j) = κ τ := by
    obtain ⟨n, k⟩ := congr($(hs u).1).trans zmod_eq_natCast_val,
      cocycle_conj_eq_smul hκ.2.1 (cycPowDirichlet_smul_eq_self t (hK (s⁻¹ u)⁻¹)).1
    erw [b.equivFun.symm_apply_eq (y := u.1.val • ⟨_, mem_span_singleton.2 ⟨_, k.symm⟩⟩).2
      (funext fun i ↦ eq_of_mem_principalUnits
      (hq'.of_mul_left.coprime_of_modEq_one.valuation_eq_one hB) ?_), ← Nat.cast_smul_eq_nsmul O,
      smul_smul, mul_right_comm, ← pow_succ, ← cycPowDirichlet_smul (l := l) n (hK _), k]
    simp [smul_smul, ← Units.val_mul]
    simpa
      [smul_smul, *, hr _ ⟨_, _⟩, ← zsmul_eq_mul, smul_sub, ↓map_nsmul, ← hL, ← cycCharMod_eq_of_dvd
      _ n, sub_sub_sub_comm, map_cycCharMod_mul] using hτ.sub_nsmul_mem_principalUnits (u :=
      m i u • π - _) (m := l) (by simp [↓← hv.ordRat_eq_zero_iff, smul_comm, *, smul_sub, ← hm])
  obtain ⟨y, n, o⟩ := mem_smul_span_singleton.1 (sum_mem fun i _ ↦
    (IsLocalRing.maximalIdeal O).smul_mem_smul (h0 <| ·.smul_eq_zero.1 (R i)) (j • b i).2)
  rw [← (by_contra ((sub_mem_iff_right _ n).1 · hN)).smul_eq_zero]
  simpa [smul_sum, sum_smul, sub_smul, sum_comm (γ := _ˣ), *, ← zsmul_eq_mul,
    Nat.cast_smul_eq_nsmul, smul_comm (_ : O)] using congr(∑ u, $(F u))

attribute [local simp↓] nsmul_quot_eq_zero

lemma exists_frob_notMem m [NeZero m] (U : {U : OpenSubgroup Gal(Ω/ℚ) // ¬cycloGalGroup m ≤ U}) (V :
  _ := U) : ∃ q : Nat.Primes, q ≡ 1 [MOD m] ∧ ∃ A σ, A (q : Ω) < 1 ∧ IsFrob A q σ ∧ σ ∉ U.1 ∧
  σ ∉ V.1 := (chebotarev (isOpen_ker_cycCharMod.1.sdiff (U.1.isClosed.union V.1.isClosed))
  (Set.not_subset.1 (SubgroupClass.subset_union.1 · |>.rec U.2 V.2)) (finite_natCast_mem _)).rec
  fun v ⟨hv, p, B, hB, σ, H, F, _⟩ ↦ ⟨⟨_, p⟩, (F.mem_ker_cycCharMod_iff
  (hB.valuation_natCast_eq_one_iff.2 hv)).1 H.1, B, σ, hB.valuation_q_lt_one, by aesop⟩

variable {O : Type} [CommRing O] {N l e X ν : ℕ} [NeZero N] [L :
  Fact l.Prime] [PadicIntegerRing O l] {ψ : DirichletCharacter O N} (h :
  IsStickelbergerBound N e X) (hc : cycPowDirichlet l e ψ cmConj = -1) (he : e ≠ 0) (n : ℕ) {a : ℕ}

include h hc he

/-- Assume `PadicIntegerRing` O l, e > 0, cyc^e·ψ odd and `IsStickelbergerBound` N e X. For a ≡ 1
mod N prime to l, ∑ m_a(x/M)x^eψ(x) over the units 0 ≤ x < M = Nlⁿ divides (a^{e+1} − 1)X in O/lⁿ
(m_a = `floorDiff` a). -/
lemma sum_floorDiff_dvd (t : a ≡ 1 [MOD N]) (r : l.Coprime a) :
  ((∑ x : (ZMod (N * l ^ n))ˣ, floorDiff a (ofZMod _
  x.1) * (x.1.val ^ e * ψ x.1.val) : O) : QuotSpan (l ^ n : O)) ∣ ((a ^ (e + 1) - 1) * X : O) := by
  have o y := by simpa [cycPowDirichlet, isComplexConj_cmConj.cycChar_eq_neg_one,
    isComplexConj_cmConj.cycCharMod_eq_neg_one, mul_assoc, ← map_mul] using congr($hc * -ψ (-y))
  obtain ⟨⟨w, W⟩, H, G, _⟩ := h.2 a t O ψ (by simp [← o]), show (l : QuotSpan (l ^ n : O)) ^ n = 0
    from mk_singleton_self _, one_sub_dvd_one_sub_pow (l ^ e * ψ l : QuotSpan (l ^ n : O)) n
  cases' n with n; use 0; grind
  obtain ⟨⟨x, E⟩, ⟨y, F⟩, v, e, rfl⟩ := W _ (r.pow_left n.succ), W _ (r.pow_left n),
    pow_succ' l n ▸ mul_left_comm N l _, he.pos.dest
  rw [← sum_of_injOn (s := univ.disjSum (Finset.range (N * l ^ n))) _ (((ZMod.val_injective _).comp
    Units.val_injective).sumElim (mul_right_injective₀ (ne l)) fun u y k ↦ L.1.ne_one
    (Nat.eq_one_of_dvd_coprimes (val_coe_unit_coprime u) ⟨y, k⟩ ⟨_, v⟩)).injOn (by
    simp [Set.MapsTo, val_lt]; simp [v, pos]) (fun t d k ↦ by simp [ψ.map_nonunit fun i ↦ k ⟨.inl
    (unitOfCoprime t (.mul_right ((isUnit_iff_coprime ..).1 i) (L.1.coprime_pow_of_not_dvd fun ⟨y,
    e⟩ ↦ k ⟨.inr y, by simp_all [pos]⟩))), by simpa [Nat.mod_eq_iff_lt, ne] using d⟩])
    (by tauto)] at E
  have := congr(G * ↑($E - l ^ (1 + e) * ψ l * $F))
  use w * G; simp only [floorDiff, ↓← _root_.map_neg, ofZMod_apply, fracRep_mk, mul_div,
    Nat.mod_eq_of_lt, val_lt, Int.fract_div_natCast_eq_div_natCast_mod]; norm_cast
  simp [-natCast_val, mul_left_comm a, v, Nat.mul_div_mul_left, pos, two_mul, add_mul, sub_mul] at *
  nth_rw 2 [← neg_bijective.sum_comp]
  simp [← o, ← mul_assoc, ← mul_pow, @ringChar.dvd (QuotSpan (l ^ n.succ : O)) _ (N * l ^ n.succ)
    (by simp [H]), mul_sum, mul_sub, sum_mul, mul_add] at *; ring_nf at *; grind

/-- Stickelberger annihilator. Let O satisfy `PadicIntegerRing` O l, e ≥ 1, c a complex conjugation
with (cyc^eψ)(c) = −1, and let X satisfy `IsStickelbergerBound` N e X. Then 4X² kills every cocycle
in `component` (values in O/l^ν).

Known result: Stickelberger annihilation and Kolyvagin–Rubin bound for odd twisted components. -/
lemma nsmul_component_eq_zero {z} (hz : z ∈ component l e ψ ν) : (4 * X * X) • z = 0 := by
  by_contra
  obtain ⟨⟨a, t, r, b, rfl⟩, p, P, B, σ, D, F, h0 : _ ≠ _, -⟩ := h.1 l L.1,
    exists_frob_notMem (N * l ^ ν) ⟨_, not_cycloGalGroup_le_zeroSubgroup (nsmul_mem hz (2 * X * X))
    cmConj (by simp [hz.2.2]) (by simp [*, sub_smul]; grind) _⟩
  have hJ := ((exists_jacobi_family D a).choose_spec P (x := ofZMod (N * l ^ ν) ·) (by
    simp [↓natCast_self, ← map_nsmul]))
  obtain ⟨⟨⟩, ⟨⟩⟩ :=
    artin_law_component r t D F hz P (by simp) (by simpa using ((hJ 1).2.1 · 1)) (fun _ _ _ ↦
    .inl ⟨0, by simp [*]⟩) (surjInv_eq (cycCharMod_surjective _)), sum_floorDiff_dvd h hc he ν t r
  cases a <;> simp_all [(hJ 1).2.1 _ _ zmod_eq_natCast_val, surjInv_eq, ← map_nsmul,
    Algebra.smul_def, map_ofNat]; grind

open _root_.Nat

/-- Kolyvagin–Rubin bound. Under the hypotheses of `nsmul_component_eq_zero` (these already make O
local and each O/lⁿ finite), with X ≠ 0 and l > N + e + 3, there are v_l(X) + 1 Galois elements such
that a cocycle in `component` vanishing at all of them is zero.

Known result: Stickelberger annihilation and Kolyvagin–Rubin bound for odd twisted components. -/
lemma exists_detecting_points_component (hX : X ≠ 0) (hl : N + e + 3 < l) : ∃ γ :
    Fin (X.factorization l + 1) → _, ∀ x ∈ component l e ψ ν, (∀ i, x (γ i) = 0) → x = 0 := by
  obtain ⟨⟨b, ha⟩, o, _, _, op⟩ := exists_isPrimitiveRoot (ZMod l) (l - 1),
    N.coprime_of_lt_prime out
    (by lia) L.1, N.totient_le, pos (φ N),
    (@valuation_comap_intQpBar_lt_one · · (IsAlgClosed.lift (R := ℚ)).1)
  by_contra! C; obtain ⟨a, E, t⟩ := chineseRemainder o b.val 1
  cases by simpa [← natCast_eq_natCast_iff] using E
  set m := _ + 1; let Z := {x ∈ component l e ψ ν | x ≠ 0 ∧ l • x = 0}
  have R := ((isUnit_iff_coprime ..).1 (ha.isUnit (by omega))).symm
  obtain ⟨⟨γ, -, g⟩, M, _, ⟨⟨u₂, u₃⟩, u₄⟩, u⟩ := exists_inertia_cycPowDirichlet_eq (ψ :=
    ψ) R t (op l L) e.succ, mul_dvd_mul_left N (dvd_pow_self l (ne m)),
    (⟨by grind⟩ : NeZero a), by simpa [map_ofNat] using
    (IsUnit.of_map PadicInt.toZMod ((2 : ℕ) * φ (N * l) * (a ^ e - 1) * (a ^ e.succ - 1) : ℤ_[l])
    (by simp (disch := omega) [-cast_ofNat, natCast_eq_zero_iff, not_dvd_of_pos_of_lt,
    totient_mul o.symm, totient_prime L.1, ha.pow_ne_one_of_pos_of_lt])).map (algebraMap _ O)
  let Y (T := ∅) :=
    vanishingCocycles (cycPowDirichlet l e.succ ψ) (QuotSpan (l ^ m : O)) (inertiaOff N l T)
  cases (⟨Set.Finite.sep (finite_vanishingCocycles
    (cycPowDirichlet_smul_eq_self ·.2 (nsmul_quot_eq_zero ..) |>.2) (by grind)) _,
    finite_vanishingCocycles (cycPowDirichlet_smul_eq_self ·.2 (nsmul_quot_eq_zero ..) |>.1)
    fun _ ↦ by simp [inertiaOff, inertiaAbove]; grind
    [placesDividing, IsPlaceOver.valuation_natCast_eq_one_iff]⟩ : Finite Z ∧ Finite Y)
  have s (x : Z) :=
    not_cycloGalGroup_le_zeroSubgroup x.2.1 cmConj (by simp [x.2.1.2.2]) (by norm_num [*, x.2.2])
  choose q K G using fun w : {y : Y | ¬cycloGalGroup (a * (N * l ^ m)) ≤ zeroSubgroup y.2} × Z ↦
    exists_frob_notMem _ ⟨_, w.1.2⟩ ⟨_, s w.2 _⟩
  let v r (x : Z) := ∀ A, A (r : Ω) < 1 → ∀ g ∈ decompGroup _ A, x.1 g = 0
  let P (r : Primes) := r ≡ 1 [MOD N * l]
  have I {r A i} (k : P r) d (j : i ∈ inertiaGroup _ A) : _ ∧ _ ∧ _ := ⟨decompGroup_le_cycloGalGroup
    d k.of_mul_right j.1, k.of_mul_left.coprime_of_modEq_one.valuation_eq_one d, j⟩
  have W {r A} (k : P r) d : ∃ σ, IsFrob A r σ ∧ ∀ x, x.1 σ = 0 → v r x :=
    (exists_rat_place_of_prime r.2).rec fun _ ⟨⟨e, _⟩, _, w⟩ ↦ ((w A d).exists_isFrob _).imp fun σ
    f ↦ ⟨e ▸ f, fun ⟨x, X, _, h⟩ z B b ↦ have a := w B b; ((w A d).exists_smul _ a).rec fun ρ o ↦
      a.decompGroup_le (o ▸ f.conj ρ) (zeroSubgroup X).2 (X.2.2 · <| .inr <| I k b · |>.imp_right
      (.inl ⟨_, a.valuation_natCast_eq_one_iff.1 ·.1, _, a, ‹_›⟩)) ((cocycle_conj_eq_smul
    X.2.1 (cycPowDirichlet_smul_eq_self (decompGroup_le_cycloGalGroup d k f.1)
      (congrFun h _)).2).trans (by simpa))⟩
  choose! σ _ V using fun r k ↦ @W r _ k (op r ⟨r.2⟩)
  let J T := (∀ r ∈ T, P r) ∧ ∀ y ∈ Y T, l • y = 0 → y ∈ Y
  have ex T (j : J T) (h : #T ≤ m) : ∃ z, ∀ q, P q → ¬v q z → q ∉ T ∧ J (insert q T) := .imp (fun z
    (hz : ∀ r ∈ T, _) q k n ↦ ⟨(hz q).mt n, by grind, fun y Z o ↦ j.2 y (.imp_right (.imp_right
    fun u τ ⟨A, i, H⟩ ↦ _root_.by_cases (W k · |>.rec fun σ f ↦ reciprocity_mod_ell R t ‹_› f.1
    z.2.1 u₃ k z.2.2.2 Z (congrFun o) i.2.2 (by grind) (n ∘ f.2 _ ∘ by simp [*])) (u τ ⟨A, i, by
    simpa [·, -not_lt]⟩)) Z) o⟩) ((C (σ T.toList[·]!)).rec fun x ⟨X, e, n⟩ ↦
    (@exists_not_and_succ_of_not_zero_of_exists (l ^ · • x = 0) (by simpa) ⟨ν, by ext; simp⟩).rec
    fun k _ ↦ ⟨⟨_, nsmul_mem X _, by rwa [← mul_nsmul]⟩, fun r i ↦ V r (j.1 r i) _ (by simp [
    by simpa [i] using e ⟨_, (List.idxOf_lt_length_iff.2 (mem_toList.2 i)).trans_le (by simpa)⟩])⟩)
  obtain ⟨⟨z, hz⟩, Q, b⟩ := ex ∅ (by tauto) bot_le, (Set.finite_range q).exists_finset
  have := of_pos (Q.prod_pos fun q _ ↦ q.2.pos)
  obtain ⟨p, hp, B, τ, D, f, h0, -⟩ := exists_frob_notMem (N * l ^ m * Q.prod (↑)) ⟨_, s z _⟩
  choose κ E Z U F using exists_kolyvagin_cocycles (ψ := ψ) e a γ (b · |>.1 · |>.rec fun w e ↦
    e ▸ K w) hp D
  have j := (hz p (hp.of_dvd (M.mul_right _)) (h0 <| · B D _ f.1)).2
  have H := u.smul_eq_zero.1 (g ▸ E fun τ i ↦ by simpa using ((@decreasingInduction m
    (fun i _ ↦ ∀ S ⊆ Q, #S ≤ i → J (insert p S) → l ^ i • κ S ∈ Y) (fun i _ H S T c j ↦ (ex _ j
    (by grw [card_insert_le]; omega)).rec fun w h ↦ j.2 _ (nsmul_mem (Z S T) _) (by_contra fun o ↦
    (G ⟨⟨⟨_, H S T c.step j⟩, not_cycloGalGroup_le_zeroSubgroup _ γ (by simp [*]) (by simpa [*,
    pow_succ', mul_smul] using o) _⟩, w⟩).rec fun A hσ ↦ hσ.elim fun σ hs ↦
    have d := hs.1
    have f := hs.2.1
    have y := hs.2.2.1
    have x := hs.2.2.2
    (h _ ((K _).of_dvd (M.mul_left
    _)) (x <| · A d σ f.1)).rec fun n j ↦ (F S T _ (by simp [b]) (n ∘ mem_insert_of_mem) A σ f
    d).rec fun τ ⟨i, e⟩ ↦ y (congr(l ^ _ • $e).symm.trans ((H _ (by simp [*, insert_subset]) (by grw
    [card_insert_le, c]) (by rwa [insert_comm])).2.2 τ ⟨A, I (j.1 _ (by simp)) d i, nofun⟩))))
    (by simp [Pi.smul_def, ← Pi.zero_def]) 0 bot_le ∅ nofun le_rfl j).2.2 τ ⟨B, I (j.1 _ (by simp))
    D i, nofun⟩)) ▸ sum_floorDiff_dvd (X.ordProj_mul_ordCompl_eq_self l ▸ h) hc he _ t R
  simp [↓zero_dvd_iff, ↓eq_zero_iff_dvd, ↓u.dvd_mul_left, m, pow_add, ne, mul_dvd_mul_iff_left] at H
  simpa [↓← cast_smul_eq_nsmul O, (X.coprime_ordCompl L.1 hX).cast.isUnit_of_dvd H] using z.2.2
