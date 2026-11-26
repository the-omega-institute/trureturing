import GRH.Lib.General.Geometry.LocalTerms
import GRH.Lib.Cohomology.Etale.BijectiveComparisons
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! Part of: Descent of torsion étale cohomology along v-covers; excision, transfer, limits (known
result; see Lib.Cohomology.Etale.ContinuityAtlas).

This file: Dense subfunctors form a Grothendieck topology; Mayer–Vietoris short exact sequence.
Composition of pull-backs; an equivalence can be checked over a dense subfunctor. Idempotent
partitions and Zariski-local subfunctors are dense for additive coefficients on comparable rings. -/

open CategoryTheory Limits Subfunctor IsCohomEquiv Comparison Types biprod ShortComplex IsPushout
variable {C} [Category C] {F} {Y E : C ⥤ Type 1} {U V : Subfunctor Y} {g : E ⟶ Y}

lemma mono_of_app_injective : (∀ A, Function.Injective (g A)) → Mono g := by
  simp [g.mono_iff_mono_app, mono_iff_injective]

/-- Mayer–Vietoris: for subfunctors U, V of Y, the sequence 0 → Z[U∩V] → Z[U] ⊕ Z[V] → Z[U∪V] →
0, with maps x ↦ (x,−x) and (x,y) ↦ x+y, is short exact. -/
lemma mayer_vietoris_shortExact : ∃ w,
  ShortExact ⟨lift (freeAb.map ((U ⊓ V).homOfLe inf_le_left)) (-freeAb.map (homOfLe inf_le_right)),
  desc (freeAb.map (homOfLe le_sup_left)) (freeAb.map (homOfLe le_sup_right)), w⟩ := by
  delta freeAb; apply (⟨_, .mk' ·.exact_shortComplex inferInstance (epi_shortComplex_g ‹_›)⟩)
    ((of_forall_isPushout_app fun _ ↦ isPushout_of_bicartSq ⟨rfl, rfl⟩).map _)

lemma isCohomEquiv_iff_range [hg : Mono g] : range g = U → (IsCohomEquiv F (freeAb.map g) ↔
  IsCohomEquiv F (freeAb.map U.ι)) := by grind [toRange_ι, comp_iff, of_isIso]

namespace IsCohomDense

attribute [local simp] toFunctor fibreProd fibreProd.snd

/-- If the subfunctor U of Y is dense for F, then the inclusion U → Y is an equivalence: it
induces bijections H^n(Y,F) → H^n(U,F) for all n. -/
lemma isCohomEquiv (h : IsCohomDense F U) : IsCohomEquiv F (freeAb.map U.ι) :=
  (isBijective_of_fibres (𝟙 _) .of_id_snd (h · · |>
  (isCohomEquiv_iff_range (hg := isPullback_fibreProd.mono_fst_of_mono) (by aesop)).2 |>.bij)).eqv

/-- If the subfunctor U of Y is dense for F, then its preimage under any map p: E → Y is a dense
subfunctor of E for F. -/
lemma preimage (h : IsCohomDense F U) p : @IsCohomDense C _ E F (U.preimage p) := fun _ ↦
  (pointMap_comp · p ▸ h _ _ :)

/-- A subfunctor U of Y that is all of Y is dense for F. -/
lemma of_top_le (h : ⊤ ≤ U := by tauto) : IsCohomDense F U := top_unique h ▸ fun _ _ ↦
  of_isIso (freeAb.map (ι ⊤))

/-- Let U, V be subfunctors of Y. If V is dense in Y for F and U ∩ V, the preimage of U in V, is
dense in V, then U is dense in Y. -/
lemma trans (h : IsCohomDense F V) (k : IsCohomDense F (U.preimage V.ι)) : IsCohomDense F U :=
  fun _ y ↦ by
  have := (k.preimage (fromPreimage ..)).isCohomEquiv.comp_iff.2 (h _ y)
  rwa [← (h.preimage (ι _ ≫ pointMap y)).isCohomEquiv.comp_iff, ← freeAb.map_comp,
    isCohomEquiv_iff_range] at * <;> aesop

/-- If the subfunctor U of Y is dense for F and V is a subfunctor of Y containing U, then V is
dense for F. -/
lemma mono (h : IsCohomDense F U) (hU : U ≤ V) : IsCohomDense F V :=
  h.trans (of_top_le (fun _ ↦ hU · ·.2))

lemma of_preimage_le (h : IsCohomDense F U) p {W} : U.preimage p ≤ W → @IsCohomDense C _ E F W :=
  (h.preimage p).mono

/-- If the subfunctors U and V of Y are both dense for F, then so is their intersection U ∩ V. -/
lemma inf (h : IsCohomDense F U) (k : IsCohomDense F V) : IsCohomDense F (U ⊓ V) :=
  h.trans (k.of_preimage_le _ fun _ ↦ (⟨·.2, ·⟩))

end IsCohomDense

variable {C : _} [Category C] {F : AbFunctor C} {Y : _} {n X K W}

lemma H.map_map (u : X ⟶ Y) (v : Y ⟶ K) x : map F (freeAb.map u) n (map F (freeAb.map v) n x) =
  map F (freeAb.map (u ≫ v)) n x := by simp [map]

lemma IsCohomDense.isCohomEquiv_of_fromPreimage {u : X ⟶ Y} (d : IsCohomDense F W) (h :
  IsCohomEquiv F (freeAb.map (W.fromPreimage u))) : IsCohomEquiv F (freeAb.map u) := by grind
  [h.comp_iff.2 d.isCohomEquiv, W.fromPreimage_ι, (d.preimage u).isCohomEquiv.comp_iff]

open Function Ideal IsCohomDense RingHom H

attribute [local simp] bijective_iff_existsUnique ExistsUnique subsingleton_of_zero_eq_one

variable {C : _} [Category C] {Y : _} {ι} {F : _} {A} (hF : @HasPartitions C _ ι F) (e : ι A)

/-- If β: F → G is bijective at every object A with Y(A) nonempty, then H^n(Y,F) → H^n(Y,G) is
bijective for every n. -/
lemma H.push_bijective_of_points {G} β (h : ∀ A, Y A → Bijective (β A)) n : Bijective (@push C _
    (freeAb Y) F G β n) :=
  pull_id_eq_push β ▸ freeAb.3 Y ▸ HasUnivPoints.isBijective (⟨·, ·, 𝟙 _, by aesop⟩) n

/-- Let U be a subfunctor of Hom(X,−) and z: X → L a member of U. If every member of U factors
uniquely through z, then z represents U: the map Hom(L,D) → U(D) is bijective for every D. -/
lemma pointMap_bijective_of_existsUnique {L} (U : Subfunctor (reprBy A)) (z : U.toFunctor L) (h :
  ∀ D y, .up y ∈
  U D → ∃! a, z.1.1 ≫ a = y) : AllBijective (pointMap z ·) := fun D ↦ .of_existsUnique _
  ((Equiv.ulift.existsUnique_congr fun _ ↦ Subtype.ext_iff.trans ULift.ext_iff).2 <| h D _ ·.2)

/-- Let f: E → B be a map to a commutative ring with `IsComparableRing` f, and g an element
outside a maximal ideal m of B. Then some idempotent e of E has f(e) ∉ m and g ∣ f(e). -/
lemma exists_idempotent_dvd_of_notMem {E B} [Mul E] [CommRing B] {f : E → B} (c :
  IsComparableRing f) {m g} (M : IsMaximal m)
  (N : g ∉ m) : ∃ e, f e ∉ m ∧ IsIdempotentElem e ∧ g ∣ f e := let ⟨b, d, h, _⟩ := M.exists_inv N
  (c g d).imp fun e ⟨he, ⟨a, _⟩, H⟩ ↦ ⟨(add_mem (mem_of_dvd _ H h) ∘ mul_mem_right g _).mt
    (by grind), he, a + b * f e, by grind⟩

/-- For a functor ι from C to commutative rings and e in ι(A), the subfunctor of h_A of
morphisms f: A → B with ι(f)(e) = 0. -/
abbrev elemKillingMaps : Subfunctor (reprBy A) :=
  ⟨fun _ ↦ {f | ι.map f.1 e = 0}, by delta reprBy reprFunctor; simp_all⟩

include hF

/-- Let F satisfy `HasPartitions` for the rings ι(A). If ι(B) is the zero ring whenever Y(B)
is non-empty, then H^n(Y,F) = 0 for all n. -/
lemma HasPartitions.eq_zero_of_zero_ring (h : ∀ B, Y B → (0 : ι B) = 1) n (x : H (freeAb Y) F n) :
  x = 0 := (push_bijective_of_points 0 (fun B y
  ↦ @bijective_of_subsingleton _ ⟨by simpa [h B y] using hF.2 (𝟙 B) (𝟙 B)⟩ _) n).1
  (by simp [H.push])

/-- Let F satisfy `HasPartitions` for the rings ι(A). For an idempotent e of ι(A), the maps
out of A that kill e or kill 1 − e form a dense subfunctor of h_A for F. -/
lemma HasPartitions.isCohomDense_partition (he : IsIdempotentElem e) :
  IsCohomDense F (elemKillingMaps e ⊔ elemKillingMaps (1 - e)) := fun A ⟨k⟩ ↦ by
  convert (fun e (he : IsIdempotentElem e) ↦
    (?_ : IsCohomEquiv F (freeAb.map (elemKillingMaps e ⊔ elemKillingMaps (1 - e)).ι))) _
    (he.map (ι.map k).hom); any_goals ext; simp; erw [ι.map_comp_apply]
  by_cases e = 1 ∨ e = 0; use (of_top_le (by aesop)).isCohomEquiv
  obtain ⟨⟨_, π, a, c, s, i⟩, _, ρ, b, d, t, j⟩ := hF.1 _ _ he (by tauto), hF.1 _ _ he.one_sub (by
    grind); cases projective_and_eval_bijective F _
    (pointMap_bijective_of_existsUnique (elemKillingMaps _) ⟨_, a⟩ c)
  cases projective_and_eval_bijective F _ (pointMap_bijective_of_existsUnique (elemKillingMaps _)
    ⟨_, b⟩ d); exact (isBijective_reprBy_iff.2 ⟨.of_comp_left (f := fun w ↦
    (w _ (.of ⟨_, .inl a⟩), w _ (.of ⟨_, .inr b⟩))) (by convert hF.2 π ρ ⟨fun x y
    _ ↦ by rcases @i (x - y), @j (x - y); grind [he.eq, mem_span_singleton', mem_ker], (s.prodMap
    t).forall.2 fun (x, y) ↦ ⟨x + e * (y - x), by grind⟩⟩ <;> apply homOfValue_app) fun _ _ _ ↦
    mayer_vietoris_shortExact.2.3.1 _ _ (by apply biprod.hom_ext' <;> apply Bijective.injective ‹_›
    <;> simp <;> injections), fun _ ↦ (isCohomEquiv_quotient_of_acyclic mayer_vietoris_shortExact.2
    (hF.eq_zero_of_zero_ring (by simp_all)) _).1.subsingleton⟩).eqv

/-- Let F satisfy `HasPartitions` for ι and let η: ι → κ be injective. If any a, b ∈ κ(A) have
an idempotent e ∈ ι(A) with a ∣ η(e)b and b ∣ (1 − η(e))a, then F satisfies Zariski descent
`HasZariskiDescent` for κ. -/
lemma HasPartitions.hasZariskiDescent {κ} (η : ι ⟶ κ) (z : ∀ A x, η A x = 0 → x = 0) (c : ∀ A,
  IsComparableRing (η A)) : HasZariskiDescent κ F := fun Y U h A y ↦
  isCohomEquiv (.trans ((eq_top_iff_one (.ofLinearComb {a | IsCohomDense F (elemKillingMaps a ⊔
  U.preimage (pointMap y))} ⟨0, of_top_le (by aesop)⟩ fun _ i _ j _ _ ↦ (i.inf j).mono fun _ _ ↦ by
  clear * -; aesop)).1 (ne_top_iff_exists_maximal.not_right.2 fun ⟨m, l, o⟩ ↦ (h A y m l).elim
  fun g ⟨N, h⟩ ↦ (exists_idempotent_dvd_of_notMem (c _) l N).elim fun e ⟨k, i, d⟩ ↦
  k (o ((hF.isCohomDense_partition e i).mono fun B f ↦
  .imp (by simpa using congrArg (η B) ·) fun k ↦ h _ _ (isUnit_of_dvd_unit (map_dvd _ d) (by simp
  [← η.naturality_apply, ← (sub_mem_ker_iff _).1 k])))))) fun B f ↦ f.2.elim (fun k
  n ↦ have s D (x : reprBy B D) := (z D 1 (by simpa using (elemKillingMaps 1).2 x.1 k)).symm; by
    simp [hF.eq_zero_of_zero_ring s, hF.eq_zero_of_zero_ring
      (s · ∘ Subfunctor.ι _ _)]) (isCohomEquiv <| of_top_le fun _ _ _ ↦ Subfunctor.map _ _ ·))
