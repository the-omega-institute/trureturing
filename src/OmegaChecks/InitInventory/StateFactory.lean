module
public import Init.ShareCommon

namespace OmegaChecks.InitBoundaries.FactoryCarriers
open ShareCommon

/-- Fix the map carrier to the supplied pointed type for every key and value type. -/
public def constantMap (M : Type) (empty : M) : StateFactoryBuilder where
  Map _ _ _ _ := M
  mkMap _ := empty
  mapFind? _ _ := none
  mapInsert m _ _ := m
  Set _ _ _ := Unit
  mkSet _ := ()
  setFind? _ _ := none
  setInsert _ _ := ()

private theorem noPredicateInjection {U : Type} (encode : (U → Prop) → U)
    (injective : ∀ p q, encode p = encode q → p = q) : False := by
  let diagonal (x : U) := ∀ p : U → Prop, encode p = x → ¬ p x
  have rejects : ¬ diagonal (encode diagonal) := fun h => h diagonal rfl h
  apply rejects
  intro p eq hp
  exact rejects (injective p diagonal eq ▸ hp)

/-- The total space of map values indexed by small factory references is itself small.
Recovering even an injection for each supplied map carrier would put all its predicates inside it. -/
public theorem noCarrierEmbedding (pack : type_of% @StateFactory.mk) (unpack : type_of% @StateFactory.get)
    (recover : ∀ (M : Type) (empty : M), ∃ encode : M → (unpack (pack (constantMap M empty))).Map,
      ∀ a b, encode a = encode b → a = b) : False := by
  let carrier (factory : StateFactory) := (unpack factory).Map
  let U := Sigma carrier
  let predicate := U → Prop
  let empty : predicate := fun _ => False
  let factory := pack (constantMap predicate empty)
  obtain ⟨encode, injective⟩ := recover predicate empty
  apply noPredicateInjection (fun p : predicate => (⟨factory, encode p⟩ : U))
  intro p q eq
  apply injective
  exact eq_of_heq (Sigma.mk.inj eq).2

end OmegaChecks.InitBoundaries.FactoryCarriers
