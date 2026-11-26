import GRH.Lib.ClassField.Places.SelmerDefs
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! Part of: Crystalline losses above ℓ are affordable (see New.Selmer.RibetElement).

This file: Cocycles obeying relations among u(g)-1, extension by Artin-Rees; blocks of a lift. -/

noncomputable section


open Matrix LinearMap Module Submodule Finsupp Ideal
variable {O X G σ d} [CommRing O] [Group G] [Fintype σ] [Fintype d] (u : X → G →* Matrix σ σ O)
  (ρ : G →* Matrix d d O) [Finite X] [IsNoetherianRing O]

/-- The cocycles c: G → (O/a)^d for ρ, continuous or not, with Σθ(g)c(g) = 0 for every finitely
supported θ: G → O such that Σθ(g)(u_x(g) − 1) = 0 for all x. -/
def obeyingCocycles (a : O) := obeying (cocycleRels ρ) (QuotSpan a) ⊓
  ⨅ θ ∈ (linearCombination O fun g ↦ (u · g - 1)).ker, ((bilinearCombination O O).flip θ).ker

/-- By Artin–Rees: a cocycle c mod a that obeys the relations among the u_x(g) − 1 is, for some k,
the value at (u(g) − 1) + a^k v (any v) of an equivariant map defined on a subrepresentation; Y is
its graph. -/
lemma obeyingCocycles.exists_graph_subrepresentation {a c} (h : c ∈ obeyingCocycles u ρ a) : ∃ k,
  ∃ Y : Subrepresentation (.prod (actionRep O _ (.pi u)) (actionRep O _ ρ)),
  (·.1.1 : Y.1 → _).Injective ∧ ∀ g v, ((u · g - 1) + a ^ k • v, c g) ∈ Y := by
  let L := linearCombination O fun g ↦ (u · g - 1)
  have ⟨k, hk⟩ := (span {a}).exists_pow_inf_eq_pow_smul L.range
  simp [span_singleton_pow, ideal_span_singleton_smul, obeyingCocycles,
    mem_obeying_cocycleRels] at *
  let N := (L.prod (linearCombination O c)).coprod (a ^ k.succ • inl ..)
  refine ⟨k.succ, ⟨N.range, fun g _ ⟨x, e⟩ ↦ e ▸ ⟨_, .trans (DFunLike.congr_fun (?_ : N ∘ₗ prodMap
    (lsum O fun h ↦ lsingle (g * h) - lsingle g) (mulLeft O (u · g)) = _) x) (comp_apply ..)⟩⟩,
    .of_ker (fst .. ∘ₗ N.range.subtype) fun ⟨_, ⟨θ, v⟩, rfl⟩ e ↦ Subtype.ext (Prod.ext e ?_),
    (⟨⟨.single · 1, ·⟩, by aesop⟩)⟩
  ext <;> simp [N, L, h, mul_sub]
  obtain ⟨_, ⟨-, η, rfl⟩, e⟩ := (hk _ k.le_succ).le
    ⟨⟨v, ⟨⟩, eq_neg_of_add_eq_zero_right e⟩, by simp⟩
  simpa [N, funext_iff, smul_quot_eq_zero_of_dvd] using h.2 (a • η + θ) (by aesop)

/-- The index sets of the blocks of a row plus string: r for the row, one point for each of the
t characters. -/
def RowBlockIndex (r : Type) {t} : Option (Fin t) → Type | none => r | _ => Unit

variable {t ℓ} [ThePrime ℓ] {E} [Field E] [EmbeddedNumberField E] {O :
  CoeffRing ℓ} (T : Gal(Ω/E) →* Matrix d d O) (i)

instance : Fintype (@RowBlockIndex d t i) := i.rec ‹_› fun _ ↦ PUnit.fintype

/-- Family of block representations of Gal(Ω/E) over O: T for the distinguished block and the
character cyc^{-e} for the block e<t. -/
def blockRep : ∀ i, Gal(Ω/E) →* Matrix (@RowBlockIndex d t i) (RowBlockIndex d i) O
  | none => T | .some e => tateTwist ℓ E _ e
