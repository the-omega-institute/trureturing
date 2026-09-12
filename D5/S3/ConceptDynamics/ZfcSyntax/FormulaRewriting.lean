/- GID: D5/S3/ConceptDynamics/ZfcSyntax/FormulaRewriting
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/ZfcSyntax/FormulaRewriting
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: General formula rewriting, occurrence origins, support congruence, universal closure and language compatibility. -/

module

public import D5.S3.ConceptDynamics.ZfcFiniteCollections.Finset
public import D5.S3.ConceptDynamics.ZfcTermRewriting.RewFour
public import D5.S3.ConceptDynamics.ZfcSyntax.FormulaTwo

/- Source: FormalizedFormalLogic/Foundation@30a16ffa93d79d73ab4d02427fa00f50e039bf29
   Foundation/FirstOrder/Basic/Syntax/Rew.lean.
   Copyright and attribution remain with the original Foundation contributors.
   Apache-2.0 license and original notices:
   Library/ConceptDynamics/foundation2026firstorder.md.
   Modifications: selected original commands in one formula owner; local action
   helpers and atom equations; consumer-local embedding normalization at binders.
   Retirement: directly reuse an equivalent interface when the repository's pinned
   Mathlib supplies it and the faithful carrier bridge elaborates. -/

@[expose] public section
namespace LO.FirstOrder.Semiformula

def rewAux ⦃n₁ n₂ : ℕ⦄ (ω : Rew L ξ₁ n₁ ξ₂ n₂) : Semiformula L ξ₁ n₁ → Semiformula L ξ₂ n₂
  |        ⊤ => ⊤
  |        ⊥ => ⊥
  |  rel r v => rel r (ω ∘ v)
  | nrel r v => nrel r (ω ∘ v)
  |    φ ⋏ ψ => rewAux ω φ ⋏ rewAux ω ψ
  |    φ ⋎ ψ => rewAux ω φ ⋎ rewAux ω ψ
  |     ∀¹ φ => ∀¹ rewAux ω.q φ
  |     ∃¹ φ => ∃¹ rewAux ω.q φ

private lemma rewAux_neg (ω : Rew L ξ₁ n₁ ξ₂ n₂) (φ : Semiformula L ξ₁ n₁) :
    rewAux ω (∼φ) = ∼rewAux ω φ :=
  by
    induction φ using Semiformula.rec' generalizing n₂ with
    | hverum | hfalsum | hrel | hnrel => rfl
    | hand φ ψ ihφ ihψ =>
      change rewAux ω (∼φ) ⋎ rewAux ω (∼ψ) = ∼rewAux ω φ ⋎ ∼rewAux ω ψ
      exact congrArg₂ (· ⋎ ·) (ihφ ω) (ihψ ω)
    | hor φ ψ ihφ ihψ =>
      change rewAux ω (∼φ) ⋏ rewAux ω (∼ψ) = ∼rewAux ω φ ⋏ ∼rewAux ω ψ
      exact congrArg₂ (· ⋏ ·) (ihφ ω) (ihψ ω)
    | hall φ ih =>
      change ∃¹ rewAux ω.q (∼φ) = ∃¹ ∼rewAux ω.q φ
      exact congrArg (∃¹ ·) (ih ω.q)
    | hexs φ ih =>
      change ∀¹ rewAux ω.q (∼φ) = ∀¹ ∼rewAux ω.q φ
      exact congrArg (∀¹ ·) (ih ω.q)

def rew (ω : Rew L ξ₁ n₁ ξ₂ n₂) : Semiformula L ξ₁ n₁ →ˡᶜ Semiformula L ξ₂ n₂ where
  toTr := rewAux ω
  map_top' := by rfl
  map_bot' := by rfl
  map_neg' := by exact rewAux_neg ω
  map_and' := fun φ ψ ↦ rfl
  map_or' := fun φ ψ ↦ rfl
  map_imply' := fun φ ψ ↦ by
    change rewAux ω (∼φ) ⋎ rewAux ω ψ = ∼rewAux ω φ ⋎ rewAux ω ψ
    rw [rewAux_neg]

instance : Rewriting L ξ (Semiformula L ξ) ζ (Semiformula L ζ) where
  app := rew
  app_all (_ _) := rfl
  app_exs (_ _) := rfl

@[local simp] private lemma rew_rel (ω : Rew L ξ₁ n₁ ξ₂ n₂) {k} (r : L.Rel k) (v : Fin k → Semiterm L ξ₁ n₁) : ω ▹ rel r v = rel r fun i ↦ ω (v i) := rfl

@[local simp] private lemma rew_nrel (ω : Rew L ξ₁ n₁ ξ₂ n₂) {k} (r : L.Rel k) (v : Fin k → Semiterm L ξ₁ n₁) : ω ▹ nrel r v = nrel r fun i ↦ ω (v i) := rfl

private lemma map_inj {b : Fin n₁ → Fin n₂} {f : ξ₁ → ξ₂}
    (hb : Function.Injective b) (hf : Function.Injective f) :
    Function.Injective fun φ : Semiformula L ξ₁ n₁ ↦ @Rew.map L ξ₁ ξ₂ n₁ n₂ b f ▹ φ
  | rel r v => fun φ ↦
    match φ with
    | rel s w => by
      simp -implicitDefEqProofs only [rew_rel, rel.injEq, and_imp]
      rintro rfl; simp only [heq_eq_eq, true_and]; rintro rfl h; simp only [true_and]
      funext i; exact Rew.map_inj hb hf (congr_fun h i)
    | nrel _ _ | ⊤ | ⊥ | _ ⋏ _ | _ ⋎ _ | ∀¹ _ | ∃¹ _ => by simp
  | nrel r v => fun φ ↦
    match φ with
    | nrel s w => by
      simp -implicitDefEqProofs only [rew_nrel, nrel.injEq, and_imp]
      rintro rfl; simp only [heq_eq_eq, true_and]; rintro rfl h; simp only [true_and]
      funext i; exact Rew.map_inj hb hf (congr_fun h i)
     | rel _ _ | ⊤ | ⊥ | _ ⋏ _ | _ ⋎ _ | ∀¹ _ | ∃¹ _ => by simp
  | ⊤ => by intro φ; cases φ using cases' <;> simp
  | ⊥ => by intro φ; cases φ using cases' <;> simp
  | φ ⋏ ψ => fun χ ↦
    match χ with
    | _ ⋏ _ => by
      simp only [LogicalConnective.HomClass.map_and, and_inj, and_imp]
      intro hp hq; exact ⟨map_inj hb hf hp, map_inj hb hf hq⟩
    | rel _ _ | nrel _ _ | ⊤ | ⊥ | _ ⋎ _ | ∀¹ _ | ∃¹ _ => by simp
  | φ ⋎ ψ => fun χ ↦
    match χ with
    | _ ⋎ _ => by
      simp only [LogicalConnective.HomClass.map_or, or_inj, and_imp]
      intro hp hq; exact ⟨map_inj hb hf hp, map_inj hb hf hq⟩
    | rel _ _ | nrel _ _ | ⊤ | ⊥ | _ ⋏ _ | ∀¹ _ | ∃¹ _ => by simp
  | ∀¹ φ => fun ψ ↦
    match ψ with
    | ∀¹ _ => by
      simp only [Rewriting.app_all, Rew.q_map, Nat.succ_eq_add_one, all_inj]
      exact fun h ↦ map_inj (b := 0 :> Fin.succ ∘ b)
        (Matrix.injective_vecCons ((Fin.succ_injective _).comp hb) (fun _ ↦ (Fin.succ_ne_zero _).symm)) hf h
    | rel _ _ | nrel _ _ | ⊤ | ⊥ | _ ⋏ _ | _ ⋎ _ | ∃¹ _ => by simp
  | ∃¹ φ => fun ψ ↦
    match ψ with
    | ∃¹ _ => by
      simp only [Rewriting.app_exs, Rew.q_map, Nat.succ_eq_add_one, exs_inj]
      exact fun h ↦ map_inj (b := 0 :> Fin.succ ∘ b)
        (Matrix.injective_vecCons ((Fin.succ_injective _).comp hb) (fun _ ↦ (Fin.succ_ne_zero _).symm)) hf h
    | rel _ _ | nrel _ _ | ⊤ | ⊥ | _ ⋏ _ | _ ⋎ _ | ∀¹ _ => by simp

instance : ReflectiveRewriting L ξ (Semiformula L ξ) where
  id_app (φ) := by induction φ using rec' <;> simp [*]

instance : TransitiveRewriting L ξ₁ (Semiformula L ξ₁) ξ₂ (Semiformula L ξ₂) ξ₃ (Semiformula L ξ₃) where
  comp_app {n₁ n₂ n₃ ω₁₂ ω₂₃ φ} := by
    induction φ using rec' generalizing n₂ n₃ <;> simp [Rew.comp_app, Rew.q_comp, *]

instance : InjMapRewriting L ξ (Semiformula L ξ) ζ (Semiformula L ζ) where
  smul_map_injective := map_inj

lemma fvar?_rew [DecidableEq ξ₁] [DecidableEq ξ₂]
    {φ : Semiformula L ξ₁ n₁} {ω : Rew L ξ₁ n₁ ξ₂ n₂}
    {x} (h : (ω ▹ φ).FVar? x) :
    (∃ i : Fin n₁, (ω #i).FVar? x) ∨ (∃ z : ξ₁, φ.FVar? z ∧ (ω &z).FVar? x) := by
  induction φ using rec' generalizing n₂
  case hverum => simp [FVar?] at h
  case hfalsum => simp [FVar?] at h
  case hrel n k r v =>
    have : ∃ i, (ω (v i)).FVar? x := by simpa -implicitDefEqProofs only [rew_rel, fvar?_rel] using h
    rcases this with ⟨i, hi⟩
    rcases Semiterm.fvar?_rew hi with (h | ⟨z, hi, hz⟩)
    · left; exact h
    · right; exact ⟨z, by simpa using ⟨i, hi⟩, hz⟩
  case hnrel n k r v =>
    have : ∃ i, (ω (v i)).FVar? x := by simpa -implicitDefEqProofs only [rew_nrel, fvar?_nrel] using h
    rcases this with ⟨i, hi⟩
    rcases Semiterm.fvar?_rew hi with (h | ⟨z, hi, hz⟩)
    · left; exact h
    · right; exact ⟨z, by simpa using ⟨i, hi⟩, hz⟩
  case hand n φ ψ ihp ihq =>
    have : (ω ▹ φ).FVar? x ∨ (ω ▹ ψ).FVar? x := by simpa using h
    rcases this with (h | h)
    · rcases ihp h with (h | ⟨z, hi, hz⟩)
      · exact .inl h
      · exact .inr ⟨z, by simp [hi], hz⟩
    · rcases ihq h with (h | ⟨z, hi, hz⟩)
      · exact .inl h
      · exact .inr ⟨z, by simp [hi], hz⟩
  case hor n φ ψ ihp ihq =>
    have : (ω ▹ φ).FVar? x ∨ (ω ▹ ψ).FVar? x := by simpa using h
    rcases this with (h | h)
    · rcases ihp h with (h | ⟨z, hi, hz⟩)
      · exact .inl h
      · exact .inr ⟨z, by simp [hi], hz⟩
    · rcases ihq h with (h | ⟨z, hi, hz⟩)
      · exact .inl h
      · exact .inr ⟨z, by simp [hi], hz⟩
  case hall n φ ihp =>
    have : (Rew.bind (#0 :> fun i ↦ Rew.bShift (ω #i)) (fun z ↦ Rew.bShift (ω &z)) ▹ φ).FVar? x := h
    rcases ihp this with (⟨z, hz⟩ | ⟨z, hz⟩)
    · cases z using Fin.cases
      case zero => simp at hz
      case succ i =>
        have : (ω #i).FVar? x := by simpa using hz
        exact .inl ⟨i, this⟩
    · have : φ.FVar? z ∧ (ω &z).FVar? x := by simpa using hz
      exact .inr ⟨z, this⟩
  case hexs n φ ihp =>
    have : (Rew.bind (#0 :> fun i ↦ Rew.bShift (ω #i)) (fun z ↦ Rew.bShift (ω &z)) ▹ φ).FVar? x := h
    rcases ihp this with (⟨z, hz⟩ | ⟨z, hz⟩)
    · cases z using Fin.cases
      case zero => simp at hz
      case succ i =>
        have : (ω #i).FVar? x := by simpa using hz
        left; exact ⟨i, this⟩
    · have : φ.FVar? z ∧ (ω &z).FVar? x := by simpa using hz
      right; exact ⟨z, this⟩

lemma rew_eq_of_funEqOn [DecidableEq ξ₁] {ω₁ ω₂ : Rew L ξ₁ n₁ ξ₂ n₂} {φ : Semiformula L ξ₁ n₁}
  (hb : ∀ x, ω₁ #x = ω₂ #x) (hf : Function.funEqOn φ.FVar? (ω₁ ∘ Semiterm.fvar) (ω₂ ∘ Semiterm.fvar)) :
    ω₁ ▹ φ = ω₂ ▹ φ := by
  induction φ using rec' generalizing n₂
  case hverum => simp
  case hfalsum => simp
  case hrel =>
    simp -implicitDefEqProofs only [rew_rel, rel.injEq, heq_eq_eq, true_and]
    funext i
    exact Semiterm.rew_eq_of_funEqOn _ _ _ hb
      (hf.of_subset fun x hx ↦ fvar?_rel.mpr ⟨i, hx⟩)
  case hnrel =>
    simp -implicitDefEqProofs only [rew_nrel, nrel.injEq, heq_eq_eq, true_and]
    funext i
    exact Semiterm.rew_eq_of_funEqOn _ _ _ hb
      (hf.of_subset fun x hx ↦ fvar?_nrel.mpr ⟨i, hx⟩)
  case hand ihp ihq =>
    simp only [LogicalConnective.HomClass.map_and, and_inj]
    exact ⟨ihp hb (hf.of_subset fun x hx ↦ by simp [hx]), ihq hb (hf.of_subset fun x hx ↦ by simp [hx])⟩
  case hor ihp ihq =>
    simp only [LogicalConnective.HomClass.map_or, or_inj]
    exact ⟨ihp hb (hf.of_subset fun x hx ↦ by simp [hx]), ihq hb (hf.of_subset fun x hx ↦ by simp [hx])⟩
  case hall ih =>
    simp only [Rewriting.app_all, all_inj]
    exact ih (fun x ↦ by cases x using Fin.cases <;> simp [hb]) (fun x hx ↦ by simpa using congr_arg _ (hf x hx))
  case hexs ih =>
    simp only [Rewriting.app_exs, exs_inj]
    exact ih (fun x ↦ by cases x using Fin.cases <;> simp [hb]) (fun x hx ↦ by simpa using congr_arg _ (hf x hx))

private lemma not_fvar?_fixitr_fvSup (φ : Proposition L) : ¬(Rew.fixitr 0 φ.fvSup ▹ φ).FVar? x := by
  rw [Rew.eq_bind (Rew.fixitr 0 φ.fvSup)]
  simp -congrConsts only [Function.comp_def, Rew.fixitr_bvar, Rew.fixitr_fvar, Fin.natAdd_mk, zero_add]
  intro h
  rcases fvar?_rew h with (⟨z, hz⟩ | ⟨z, hz, hx⟩)
  · simp -congrConsts at hz
  · have : z < φ.fvSup := lt_fvSup_of_fvar? hz
    simp [this] at hx

def univCl' (φ : Proposition L) : Proposition L := ∀¹* (@Rew.fixitr L 0 φ.fvSup ▹ φ)

@[simp] lemma fvarList_univCl' (φ : Proposition L) : φ.univCl'.freeVariables = ∅ := by
  ext x
  suffices x ∉ φ.univCl'.freeVariables by simpa
  change x ∉ (∀¹* (@Rew.fixitr L 0 φ.fvSup ▹ φ)).freeVariables
  simpa using not_fvar?_fixitr_fvSup φ

def toEmpty [DecidableEq ξ] {n : ℕ} : (φ : Semiformula L ξ n) → φ.freeVariables = ∅ → Semisentence L n
  |  rel R v, h => rel R fun i ↦ (v i).toEmpty (Finset.biUnion_eq_empty.mp h i (Finset.mem_univ i))
  | nrel R v, h => nrel R fun i ↦ (v i).toEmpty (Finset.biUnion_eq_empty.mp h i (Finset.mem_univ i))
  |        ⊤, _ => ⊤
  |        ⊥, _ => ⊥
  |    φ ⋏ ψ, h =>
    φ.toEmpty (Finset.union_eq_empty.mp h).1 ⋏ ψ.toEmpty (Finset.union_eq_empty.mp h).2
  |    φ ⋎ ψ, h =>
    φ.toEmpty (Finset.union_eq_empty.mp h).1 ⋎ ψ.toEmpty (Finset.union_eq_empty.mp h).2
  |     ∀¹ φ, h => ∀¹ φ.toEmpty h
  |     ∃¹ φ, h => ∃¹ φ.toEmpty h

@[simp] lemma emb_toEmpty [DecidableEq ξ] (φ : Semiformula L ξ n) (hp : φ.freeVariables = ∅) : Rewriting.emb (φ.toEmpty hp) = φ := by
  induction φ using rec' with
  | hall φ ih =>
    dsimp only [toEmpty]
    simp -congrConsts only [Rewriting.emb, Rewriting.app_all]
    congr 1
    calc
      _ = (Rew.emb : Rew L Empty _ ξ _) ▹ φ.toEmpty hp := Rewriting.smul_ext' (by
        rw [Rew.emb, Rew.q_map]
        apply Rew.ext
        · intro i
          cases i using Fin.cases <;> simp -congrConsts [Rew.emb, Function.comp_def]
        · intro x; exact x.elim)
      _ = φ := ih hp
  | hexs φ ih =>
    dsimp only [toEmpty]
    simp -congrConsts only [Rewriting.emb, Rewriting.app_exs]
    congr 1
    calc
      _ = (Rew.emb : Rew L Empty _ ξ _) ▹ φ.toEmpty hp := Rewriting.smul_ext' (by
        rw [Rew.emb, Rew.q_map]
        apply Rew.ext
        · intro i
          cases i using Fin.cases <;> simp -congrConsts [Rew.emb, Function.comp_def]
        · intro x; exact x.elim)
      _ = φ := ih hp
  | _ =>
    dsimp only [toEmpty]
    simp -congrConsts -implicitDefEqProofs [*]

def univCl (φ : Proposition L) : Sentence L := φ.univCl'.toEmpty (fvarList_univCl' φ)

section
variable {L₁ : Language.{u₁}} {L₂ : Language.{u₂}} {Φ : L₁ →ᵥ L₂}

lemma lMap_bind (b : Fin n₁ → Semiterm L₁ ξ₂ n₂) (e : ξ₁ → Semiterm L₁ ξ₂ n₂) (φ : Semiformula L₁ ξ₁ n₁) :
    lMap Φ (Rew.bind b e ▹ φ) = Rew.bind (Semiterm.lMap Φ ∘ b) (Semiterm.lMap Φ ∘ e) ▹ (lMap Φ φ) := by
  induction φ using rec' generalizing ξ₂ n₂ <;>
  simp [*, lMap_rel, lMap_nrel, Semiterm.lMap_bind, Rew.q_bind, Matrix.comp_vecCons', Semiterm.lMap_bShift, Function.comp_def]

end

end LO.FirstOrder.Semiformula
end
