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

private def carrierOf(builder : StateFactoryBuilder) : StateFactoryImpl where
  Map := builder.Map Nat Nat
  Set := Unit
  mkState _ := (@builder.mkMap Nat Nat _ _ 0, ())
  mapFind? _ _ := none
  mapInsert m _ _ := m
  setFind? _ _ := none
  setInsert s _ := s

/-- The lifted carrier equality required by the pinned factory reader would encode every pointed
small type into the fibers of a small family, contradicting the predicate diagonal. -/
public theorem noGetCast (h : ULift.{2} (PLift StateFactory) = ULift.{2} (PLift StateFactoryImpl)) : False := by
  let encode (x : StateFactoryImpl) : StateFactory := (cast h.symm ⟨⟨x⟩⟩).down.down
  let decode (x : StateFactory) : StateFactoryImpl := (cast h ⟨⟨x⟩⟩).down.down
  have inv (x : StateFactoryImpl) : decode (encode x) = x := by
    change (cast h (cast h.symm ⟨⟨x⟩⟩)).down.down = x
    rw [cast_cast]
    rfl
  apply noCarrierEmbedding (fun b => encode (carrierOf b)) decode
  intro M empty
  rw [inv]
  refine ⟨fun (x : M) => x, ?_⟩
  intro a b e
  exact e

end OmegaChecks.InitBoundaries.FactoryCarriers
