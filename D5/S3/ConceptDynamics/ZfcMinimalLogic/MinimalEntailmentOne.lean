/- GID: D5/S3/ConceptDynamics/ZfcMinimalLogic/MinimalEntailmentOne
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/ZfcMinimalLogic/MinimalEntailmentOne
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Propositional.Entailment.Minimal for first-order set definition elimination. -/
module

public import D5.S3.ConceptDynamics.ZfcEntailment.EntailmentTwo
public import D5.S3.ConceptDynamics.ZfcFiniteCollections.Finset

/- Source: FormalizedFormalLogic/Foundation@30a16ffa93d79d73ab4d02427fa00f50e039bf29
   Foundation/Propositional/Entailment/Minimal.lean, original lines 1-320.
   Modifications: source-command excerpt; canonical header, reduced imports, and capacity scopes.
   Retained proofs and required notices preserve attribution. Apache-2.0 license:
   Library/ConceptDynamics/foundation2026firstorder.md.
   Retirement: direct Mathlib reference when the repository pin supplies a
   proved-equivalent interface and its faithful bridge elaborates. -/

@[expose] public section

namespace LO.Axioms

variable {F : Type*} [LogicalConnective F]
variable (φ ψ χ : F)

protected abbrev NegEquiv [LogicalNeutral F] := ∼φ 🡘 (φ 🡒 ⊥)

protected abbrev Verum [LogicalNeutral F] : F := ⊤

protected abbrev ImplyK := φ 🡒 ψ 🡒 φ

protected abbrev ImplyS := (φ 🡒 ψ 🡒 χ) 🡒 (φ 🡒 ψ) 🡒 φ 🡒 χ

protected abbrev AndElim₁ := φ ⋏ ψ 🡒 φ

protected abbrev AndElim₂ := φ ⋏ ψ 🡒 ψ

protected abbrev AndInst := φ 🡒 ψ 🡒 φ ⋏ ψ

protected abbrev OrInst₁ := φ 🡒 φ ⋎ ψ

protected abbrev OrInst₂ := ψ 🡒 φ ⋎ ψ

protected abbrev OrElim := (φ 🡒 χ) 🡒 (ψ 🡒 χ) 🡒 (φ ⋎ ψ 🡒 χ)

end LO.Axioms

namespace LO.Entailment

-- def cast (e : φ = ψ) (b : 𝓢 ⊢! φ) : 𝓢 ⊢! ψ := e ▸ b
-- lemma cast! (e : φ = ψ) (b : 𝓢 ⊢ φ) : 𝓢 ⊢ ψ := ⟨cast e b.some⟩

section

variable {S F : Type*} [LogicalConnective F] [Entailment S F]
variable {𝓢 : S} {φ ψ χ : F}

class ModusPonens (𝓢 : S) where
  mdp {φ ψ : F} : 𝓢 ⊢! φ 🡒 ψ → 𝓢 ⊢! φ → 𝓢 ⊢! ψ

alias mdp := ModusPonens.mdp
infixl:90 "⨀" => mdp

lemma mdp! [ModusPonens 𝓢] : 𝓢 ⊢ φ 🡒 ψ → 𝓢 ⊢ φ → 𝓢 ⊢ ψ := by
  rintro ⟨hpq⟩ ⟨hp⟩;
  exact ⟨hpq ⨀ hp⟩
infixl:90 "⨀" => mdp!

/--
  Negation `∼φ` is equivalent to `φ 🡒 ⊥` on **system**.

  This is weaker asssumption than _"introducing `∼φ` as an abbreviation of `φ 🡒 ⊥`" (`NegAbbrev`)_.
-/
class NegationEquiv [LogicalNeutral F] (𝓢 : S) where
  negEquiv {φ : F} : 𝓢 ⊢! Axioms.NegEquiv φ
export NegationEquiv (negEquiv)

class HasAxiomVerum [LogicalNeutral F] (𝓢 : S) where
  verum : 𝓢 ⊢! Axioms.Verum

def verum [LogicalNeutral F] [HasAxiomVerum 𝓢] : 𝓢 ⊢! ⊤ := HasAxiomVerum.verum

class HasAxiomImplyK (𝓢 : S)  where
  implyK {φ ψ : F} : 𝓢 ⊢! Axioms.ImplyK φ ψ
export HasAxiomImplyK (implyK)

def C_of_conseq [ModusPonens 𝓢] [HasAxiomImplyK 𝓢] (h : 𝓢 ⊢! φ) : 𝓢 ⊢! ψ 🡒 φ := implyK ⨀ h

class HasAxiomImplyS (𝓢 : S)  where
  implyS {φ ψ χ : F} : 𝓢 ⊢! Axioms.ImplyS φ ψ χ
export HasAxiomImplyS (implyS)

class HasAxiomAndElim (𝓢 : S)  where
  and₁ {φ ψ : F} : 𝓢 ⊢! Axioms.AndElim₁ φ ψ
  and₂ {φ ψ : F} : 𝓢 ⊢! Axioms.AndElim₂ φ ψ
export HasAxiomAndElim (and₁ and₂)

def K_left [ModusPonens 𝓢] [HasAxiomAndElim 𝓢] (d : 𝓢 ⊢! φ ⋏ ψ) : 𝓢 ⊢! φ := and₁ ⨀ d
@[grind ->] lemma K!_left [ModusPonens 𝓢] [HasAxiomAndElim 𝓢] (d : 𝓢 ⊢ φ ⋏ ψ) : 𝓢 ⊢ φ := ⟨K_left d.some⟩

def K_right [ModusPonens 𝓢] [HasAxiomAndElim 𝓢] (d : 𝓢 ⊢! φ ⋏ ψ) : 𝓢 ⊢! ψ := and₂ ⨀ d
@[grind ->] lemma K!_right [ModusPonens 𝓢] [HasAxiomAndElim 𝓢] (d : 𝓢 ⊢ φ ⋏ ψ) : 𝓢 ⊢ ψ := ⟨K_right d.some⟩

class HasAxiomAndInst (𝓢 : S) where
  and₃ {φ ψ : F} : 𝓢 ⊢! Axioms.AndInst φ ψ
export HasAxiomAndInst (and₃)

def K_intro [ModusPonens 𝓢] [HasAxiomAndInst 𝓢] (d₁ : 𝓢 ⊢! φ) (d₂: 𝓢 ⊢! ψ) : 𝓢 ⊢! φ ⋏ ψ := and₃ ⨀ d₁ ⨀ d₂

class HasAxiomOrInst (𝓢 : S) where
  or₁ {φ ψ : F} : 𝓢 ⊢! Axioms.OrInst₁ φ ψ
  or₂ {φ ψ : F} : 𝓢 ⊢! Axioms.OrInst₂ φ ψ
export HasAxiomOrInst (or₁ or₂)

class HasAxiomOrElim (𝓢 : S) where
  or₃ {φ ψ χ : F} : 𝓢 ⊢! Axioms.OrElim φ ψ χ
export HasAxiomOrElim (or₃)

def of_C_of_C_of_A [HasAxiomOrElim 𝓢] [ModusPonens 𝓢] (d₁ : 𝓢 ⊢! φ 🡒 χ) (d₂ : 𝓢 ⊢! ψ 🡒 χ) (d₃ : 𝓢 ⊢! φ ⋎ ψ) : 𝓢 ⊢! χ := or₃ ⨀ d₁ ⨀ d₂ ⨀ d₃

protected class Minimal [LogicalNeutral F] (𝓢 : S) extends
              ModusPonens 𝓢,
              NegationEquiv 𝓢,
              HasAxiomVerum 𝓢,
              HasAxiomImplyK 𝓢, HasAxiomImplyS 𝓢,
              HasAxiomAndElim 𝓢, HasAxiomAndInst 𝓢,
              HasAxiomOrInst 𝓢, HasAxiomOrElim 𝓢

end

section

variable {S F : Type*} [LogicalConnective F] [Entailment S F]
variable {𝓢 : S} [ModusPonens 𝓢] {φ ψ χ : F}

def CO_of_N [LogicalNeutral F] [HasAxiomAndElim 𝓢] [NegationEquiv 𝓢] : 𝓢 ⊢! ∼φ → 𝓢 ⊢! φ 🡒 ⊥ := λ h => (K_left negEquiv) ⨀ h
def N_of_CO [LogicalNeutral F] [HasAxiomAndElim 𝓢] [NegationEquiv 𝓢] : 𝓢 ⊢! φ 🡒 ⊥ → 𝓢 ⊢! ∼φ := λ h => (K_right negEquiv) ⨀ h
@[grind =] lemma N!_iff_CO! [LogicalNeutral F] [HasAxiomAndElim 𝓢] [NegationEquiv 𝓢] : 𝓢 ⊢ ∼φ ↔ 𝓢 ⊢ φ 🡒 ⊥ := ⟨λ ⟨h⟩ => ⟨CO_of_N h⟩, λ ⟨h⟩ => ⟨N_of_CO h⟩⟩

def E_intro [HasAxiomAndInst 𝓢] (b₁ : 𝓢 ⊢! φ 🡒 ψ) (b₂ : 𝓢 ⊢! ψ 🡒 φ) : 𝓢 ⊢! φ 🡘 ψ := K_intro b₁ b₂

@[grind →] lemma iff_of_E! [HasAxiomAndInst 𝓢] [HasAxiomAndElim 𝓢] (h : 𝓢 ⊢ φ 🡘 ψ) : 𝓢 ⊢ φ ↔ 𝓢 ⊢ ψ := ⟨fun hp ↦ K!_left h ⨀ hp, fun hq ↦ K!_right h ⨀ hq⟩

def C_id [HasAxiomImplyK 𝓢] [HasAxiomImplyS 𝓢] {φ : F} : 𝓢 ⊢! φ 🡒 φ := implyS (φ := φ) (ψ := (φ 🡒 φ)) (χ := φ) ⨀ implyK ⨀ implyK

def E_Id [HasAxiomAndInst 𝓢] [HasAxiomImplyK 𝓢] [HasAxiomImplyS 𝓢] {φ : F} : 𝓢 ⊢! φ 🡘 φ := K_intro C_id C_id

def mdp₁ [HasAxiomImplyS 𝓢] (bqr : 𝓢 ⊢! φ 🡒 ψ 🡒 χ) (bq : 𝓢 ⊢! φ 🡒 ψ) : 𝓢 ⊢! φ 🡒 χ := implyS ⨀ bqr ⨀ bq
@[grind →] lemma mdp₁! [HasAxiomImplyS 𝓢] (hqr : 𝓢 ⊢ φ 🡒 ψ 🡒 χ) (hq : 𝓢 ⊢ φ 🡒 ψ) : 𝓢 ⊢ φ 🡒 χ := ⟨mdp₁ hqr.some hq.some⟩

infixl:90 "⨀₁" => mdp₁
infixl:90 "⨀₁" => mdp₁!

def mdp₂ [HasAxiomImplyK 𝓢] [HasAxiomImplyS 𝓢] (bqr : 𝓢 ⊢! φ 🡒 ψ 🡒 χ 🡒 s) (bq : 𝓢 ⊢! φ 🡒 ψ 🡒 χ) : 𝓢 ⊢! φ 🡒 ψ 🡒 s := C_of_conseq (implyS) ⨀₁ bqr ⨀₁ bq
@[grind →] lemma mdp₂! [HasAxiomImplyK 𝓢] [HasAxiomImplyS 𝓢] (hqr : 𝓢 ⊢ φ 🡒 ψ 🡒 χ 🡒 s) (hq : 𝓢 ⊢ φ 🡒 ψ 🡒 χ) : 𝓢 ⊢ φ 🡒 ψ 🡒 s := ⟨mdp₂ hqr.some hq.some⟩

infixl:90 "⨀₂" => mdp₂
infixl:90 "⨀₂" => mdp₂!

def mdp₃ [HasAxiomImplyK 𝓢] [HasAxiomImplyS 𝓢] (bqr : 𝓢 ⊢! φ 🡒 ψ 🡒 χ 🡒 s 🡒 t) (bq : 𝓢 ⊢! φ 🡒 ψ 🡒 χ 🡒 s) : 𝓢 ⊢! φ 🡒 ψ 🡒 χ 🡒 t := (C_of_conseq <| C_of_conseq <| implyS) ⨀₂ bqr ⨀₂ bq
@[grind →] lemma mdp₃! [HasAxiomImplyK 𝓢] [HasAxiomImplyS 𝓢] (hqr : 𝓢 ⊢ φ 🡒 ψ 🡒 χ 🡒 s 🡒 t) (hq : 𝓢 ⊢ φ 🡒 ψ 🡒 χ 🡒 s) : 𝓢 ⊢ φ 🡒 ψ 🡒 χ 🡒 t := ⟨mdp₃ hqr.some hq.some⟩

infixl:90 "⨀₃" => mdp₃
infixl:90 "⨀₃" => mdp₃!

def C_trans [HasAxiomImplyK 𝓢] [HasAxiomImplyS 𝓢] (bpq : 𝓢 ⊢! φ 🡒 ψ) (bqr : 𝓢 ⊢! ψ 🡒 χ) : 𝓢 ⊢! φ 🡒 χ := implyS ⨀ C_of_conseq bqr ⨀ bpq

def E_trans [HasAxiomAndInst 𝓢] [HasAxiomAndElim 𝓢] [HasAxiomImplyK 𝓢] [HasAxiomImplyS 𝓢] (h₁ : 𝓢 ⊢! φ 🡘 ψ) (h₂ : 𝓢 ⊢! ψ 🡘 χ) : 𝓢 ⊢! φ 🡘 χ := by
  apply E_intro;
  . exact C_trans (K_left h₁) (K_left h₂);
  . exact C_trans (K_right h₂) (K_right h₁);

def CCCC [HasAxiomAndElim 𝓢] [HasAxiomImplyK 𝓢] [HasAxiomImplyS 𝓢] : 𝓢 ⊢! φ 🡒 ψ 🡒 χ 🡒 φ := C_trans implyK implyK

def CK_of_C_of_C [HasAxiomAndInst 𝓢] [HasAxiomAndElim 𝓢] [HasAxiomImplyK 𝓢] [HasAxiomImplyS 𝓢] (bq : 𝓢 ⊢! φ 🡒 ψ) (br : 𝓢 ⊢! φ 🡒 χ)
  : 𝓢 ⊢! φ 🡒 ψ ⋏ χ := C_of_conseq and₃ ⨀₁ bq ⨀₁ br

def CKK [HasAxiomAndInst 𝓢] [HasAxiomAndElim 𝓢] [HasAxiomImplyK 𝓢] [HasAxiomImplyS 𝓢] : 𝓢 ⊢! φ ⋏ ψ 🡒 ψ ⋏ φ := CK_of_C_of_C and₂ and₁

def CEE [HasAxiomAndInst 𝓢] [HasAxiomAndElim 𝓢] [HasAxiomImplyK 𝓢] [HasAxiomImplyS 𝓢] : 𝓢 ⊢! (φ 🡘 ψ) 🡒 (ψ 🡘 φ) := CKK

def E_symm [HasAxiomAndInst 𝓢] [HasAxiomAndElim 𝓢] [HasAxiomImplyK 𝓢] [HasAxiomImplyS 𝓢] (h : 𝓢 ⊢! φ 🡘 ψ) : 𝓢 ⊢! ψ 🡘 φ := CEE ⨀ h

def ECKCC [HasAxiomAndInst 𝓢] [HasAxiomAndElim 𝓢] [HasAxiomImplyK 𝓢] [HasAxiomImplyS 𝓢] : 𝓢 ⊢! (φ ⋏ ψ 🡒 χ) 🡘 (φ 🡒 ψ 🡒 χ) := by
  let b₁ : 𝓢 ⊢! (φ ⋏ ψ 🡒 χ) 🡒 φ 🡒 ψ 🡒 χ := CCCC ⨀₃ C_of_conseq (ψ := φ ⋏ ψ 🡒 χ) and₃
  let b₂ : 𝓢 ⊢! (φ 🡒 ψ 🡒 χ) 🡒 φ ⋏ ψ 🡒 χ := implyK ⨀₂ (C_of_conseq (ψ := φ 🡒 ψ 🡒 χ) and₁) ⨀₂ (C_of_conseq (ψ := φ 🡒 ψ 🡒 χ) and₂);
  exact E_intro b₁ b₂

def CC_of_CK [HasAxiomAndInst 𝓢] [HasAxiomAndElim 𝓢] [HasAxiomImplyK 𝓢] [HasAxiomImplyS 𝓢] (d : 𝓢 ⊢! φ ⋏ ψ 🡒 χ) : 𝓢 ⊢! φ 🡒 ψ 🡒 χ := (K_left $ ECKCC) ⨀ d
def CK_of_CC [HasAxiomAndInst 𝓢] [HasAxiomAndElim 𝓢] [HasAxiomImplyK 𝓢] [HasAxiomImplyS 𝓢] (d : 𝓢 ⊢! φ 🡒 ψ 🡒 χ) : 𝓢 ⊢! φ ⋏ ψ 🡒 χ := (K_right $ ECKCC) ⨀ d

end

section

variable {S F : Type*} [LogicalConnective F] [LogicalNeutral F] [Entailment S F]
variable {𝓢 : S} [Entailment.Minimal 𝓢] {φ ψ χ : F}

end
end Entailment
end LO
end
