import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Multiset.Defs
import Mathlib.Data.Multiset.Pi
import Mathlib.Data.Multiset.ZeroCons
import LeanInformationAuditInterface.Contract.Catalog
import D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation
import Reg.Support.LegacyCausalCoordinates
import Reg.Support.LegacyFiniteTransport

set_option backward.isDefEq.respectTransparency.types false

namespace Reg.Catalogs.SharedInformationRoot.SealedCatalog
open LeanInformationAudit

noncomputable def state_0 : Sum Reg.Support.LegacyCausalCoordinates.ICData Reg.Support.LegacyCausalCoordinates.OIData :=
  @Sum.inr Reg.Support.LegacyCausalCoordinates.ICData Reg.Support.LegacyCausalCoordinates.OIData
    (@Prod.mk Bool (Prod (Prod Bool Bool) (Prod Bool Bool)) Bool.true
      (@Prod.mk (Prod Bool Bool) (Prod Bool Bool) (@Prod.mk Bool Bool Bool.true Bool.true)
        (@Prod.mk Bool Bool Bool.true Bool.true)))

noncomputable def state_1 : Sum Reg.Support.LegacyCausalCoordinates.ICData Reg.Support.LegacyCausalCoordinates.OIData :=
  @Sum.inr Reg.Support.LegacyCausalCoordinates.ICData Reg.Support.LegacyCausalCoordinates.OIData
    (@Prod.mk Bool (Prod (Prod Bool Bool) (Prod Bool Bool)) Bool.true
      (@Prod.mk (Prod Bool Bool) (Prod Bool Bool) (@Prod.mk Bool Bool Bool.true Bool.true)
        (@Prod.mk Bool Bool Bool.true Bool.false)))

noncomputable def state_2 : Sum Reg.Support.LegacyCausalCoordinates.ICData Reg.Support.LegacyCausalCoordinates.OIData :=
  @Sum.inr Reg.Support.LegacyCausalCoordinates.ICData Reg.Support.LegacyCausalCoordinates.OIData
    (@Prod.mk Bool (Prod (Prod Bool Bool) (Prod Bool Bool)) Bool.true
      (@Prod.mk (Prod Bool Bool) (Prod Bool Bool) (@Prod.mk Bool Bool Bool.true Bool.true)
        (@Prod.mk Bool Bool Bool.false Bool.true)))

noncomputable def state_3 : Sum Reg.Support.LegacyCausalCoordinates.ICData Reg.Support.LegacyCausalCoordinates.OIData :=
  @Sum.inr Reg.Support.LegacyCausalCoordinates.ICData Reg.Support.LegacyCausalCoordinates.OIData
    (@Prod.mk Bool (Prod (Prod Bool Bool) (Prod Bool Bool)) Bool.true
      (@Prod.mk (Prod Bool Bool) (Prod Bool Bool) (@Prod.mk Bool Bool Bool.true Bool.true)
        (@Prod.mk Bool Bool Bool.false Bool.false)))

noncomputable def state_4 : Sum Reg.Support.LegacyCausalCoordinates.ICData Reg.Support.LegacyCausalCoordinates.OIData :=
  @Sum.inr Reg.Support.LegacyCausalCoordinates.ICData Reg.Support.LegacyCausalCoordinates.OIData
    (@Prod.mk Bool (Prod (Prod Bool Bool) (Prod Bool Bool)) Bool.true
      (@Prod.mk (Prod Bool Bool) (Prod Bool Bool) (@Prod.mk Bool Bool Bool.true Bool.false)
        (@Prod.mk Bool Bool Bool.true Bool.true)))

noncomputable def state_5 : Sum Reg.Support.LegacyCausalCoordinates.ICData Reg.Support.LegacyCausalCoordinates.OIData :=
  @Sum.inr Reg.Support.LegacyCausalCoordinates.ICData Reg.Support.LegacyCausalCoordinates.OIData
    (@Prod.mk Bool (Prod (Prod Bool Bool) (Prod Bool Bool)) Bool.true
      (@Prod.mk (Prod Bool Bool) (Prod Bool Bool) (@Prod.mk Bool Bool Bool.true Bool.false)
        (@Prod.mk Bool Bool Bool.true Bool.false)))

noncomputable def state_6 : Sum Reg.Support.LegacyCausalCoordinates.ICData Reg.Support.LegacyCausalCoordinates.OIData :=
  @Sum.inr Reg.Support.LegacyCausalCoordinates.ICData Reg.Support.LegacyCausalCoordinates.OIData
    (@Prod.mk Bool (Prod (Prod Bool Bool) (Prod Bool Bool)) Bool.true
      (@Prod.mk (Prod Bool Bool) (Prod Bool Bool) (@Prod.mk Bool Bool Bool.true Bool.false)
        (@Prod.mk Bool Bool Bool.false Bool.true)))

noncomputable def state_7 : Sum Reg.Support.LegacyCausalCoordinates.ICData Reg.Support.LegacyCausalCoordinates.OIData :=
  @Sum.inr Reg.Support.LegacyCausalCoordinates.ICData Reg.Support.LegacyCausalCoordinates.OIData
    (@Prod.mk Bool (Prod (Prod Bool Bool) (Prod Bool Bool)) Bool.true
      (@Prod.mk (Prod Bool Bool) (Prod Bool Bool) (@Prod.mk Bool Bool Bool.true Bool.false)
        (@Prod.mk Bool Bool Bool.false Bool.false)))

noncomputable def state_8 : Sum Reg.Support.LegacyCausalCoordinates.ICData Reg.Support.LegacyCausalCoordinates.OIData :=
  @Sum.inr Reg.Support.LegacyCausalCoordinates.ICData Reg.Support.LegacyCausalCoordinates.OIData
    (@Prod.mk Bool (Prod (Prod Bool Bool) (Prod Bool Bool)) Bool.true
      (@Prod.mk (Prod Bool Bool) (Prod Bool Bool) (@Prod.mk Bool Bool Bool.false Bool.true)
        (@Prod.mk Bool Bool Bool.true Bool.true)))

noncomputable def state_9 : Sum Reg.Support.LegacyCausalCoordinates.ICData Reg.Support.LegacyCausalCoordinates.OIData :=
  @Sum.inr Reg.Support.LegacyCausalCoordinates.ICData Reg.Support.LegacyCausalCoordinates.OIData
    (@Prod.mk Bool (Prod (Prod Bool Bool) (Prod Bool Bool)) Bool.true
      (@Prod.mk (Prod Bool Bool) (Prod Bool Bool) (@Prod.mk Bool Bool Bool.false Bool.true)
        (@Prod.mk Bool Bool Bool.true Bool.false)))

noncomputable def state_10 : Sum Reg.Support.LegacyCausalCoordinates.ICData Reg.Support.LegacyCausalCoordinates.OIData :=
  @Sum.inr Reg.Support.LegacyCausalCoordinates.ICData Reg.Support.LegacyCausalCoordinates.OIData
    (@Prod.mk Bool (Prod (Prod Bool Bool) (Prod Bool Bool)) Bool.true
      (@Prod.mk (Prod Bool Bool) (Prod Bool Bool) (@Prod.mk Bool Bool Bool.false Bool.true)
        (@Prod.mk Bool Bool Bool.false Bool.true)))

noncomputable def state_11 : Sum Reg.Support.LegacyCausalCoordinates.ICData Reg.Support.LegacyCausalCoordinates.OIData :=
  @Sum.inr Reg.Support.LegacyCausalCoordinates.ICData Reg.Support.LegacyCausalCoordinates.OIData
    (@Prod.mk Bool (Prod (Prod Bool Bool) (Prod Bool Bool)) Bool.true
      (@Prod.mk (Prod Bool Bool) (Prod Bool Bool) (@Prod.mk Bool Bool Bool.false Bool.true)
        (@Prod.mk Bool Bool Bool.false Bool.false)))

noncomputable def state_12 : Sum Reg.Support.LegacyCausalCoordinates.ICData Reg.Support.LegacyCausalCoordinates.OIData :=
  @Sum.inr Reg.Support.LegacyCausalCoordinates.ICData Reg.Support.LegacyCausalCoordinates.OIData
    (@Prod.mk Bool (Prod (Prod Bool Bool) (Prod Bool Bool)) Bool.true
      (@Prod.mk (Prod Bool Bool) (Prod Bool Bool) (@Prod.mk Bool Bool Bool.false Bool.false)
        (@Prod.mk Bool Bool Bool.true Bool.true)))

noncomputable def state_13 : Sum Reg.Support.LegacyCausalCoordinates.ICData Reg.Support.LegacyCausalCoordinates.OIData :=
  @Sum.inr Reg.Support.LegacyCausalCoordinates.ICData Reg.Support.LegacyCausalCoordinates.OIData
    (@Prod.mk Bool (Prod (Prod Bool Bool) (Prod Bool Bool)) Bool.true
      (@Prod.mk (Prod Bool Bool) (Prod Bool Bool) (@Prod.mk Bool Bool Bool.false Bool.false)
        (@Prod.mk Bool Bool Bool.true Bool.false)))

noncomputable def state_14 : Sum Reg.Support.LegacyCausalCoordinates.ICData Reg.Support.LegacyCausalCoordinates.OIData :=
  @Sum.inr Reg.Support.LegacyCausalCoordinates.ICData Reg.Support.LegacyCausalCoordinates.OIData
    (@Prod.mk Bool (Prod (Prod Bool Bool) (Prod Bool Bool)) Bool.true
      (@Prod.mk (Prod Bool Bool) (Prod Bool Bool) (@Prod.mk Bool Bool Bool.false Bool.false)
        (@Prod.mk Bool Bool Bool.false Bool.true)))

noncomputable def state_15 : Sum Reg.Support.LegacyCausalCoordinates.ICData Reg.Support.LegacyCausalCoordinates.OIData :=
  @Sum.inr Reg.Support.LegacyCausalCoordinates.ICData Reg.Support.LegacyCausalCoordinates.OIData
    (@Prod.mk Bool (Prod (Prod Bool Bool) (Prod Bool Bool)) Bool.true
      (@Prod.mk (Prod Bool Bool) (Prod Bool Bool) (@Prod.mk Bool Bool Bool.false Bool.false)
        (@Prod.mk Bool Bool Bool.false Bool.false)))

noncomputable def state_16 : Sum Reg.Support.LegacyCausalCoordinates.ICData Reg.Support.LegacyCausalCoordinates.OIData :=
  @Sum.inr Reg.Support.LegacyCausalCoordinates.ICData Reg.Support.LegacyCausalCoordinates.OIData
    (@Prod.mk Bool (Prod (Prod Bool Bool) (Prod Bool Bool)) Bool.false
      (@Prod.mk (Prod Bool Bool) (Prod Bool Bool) (@Prod.mk Bool Bool Bool.true Bool.true)
        (@Prod.mk Bool Bool Bool.true Bool.true)))

noncomputable def state_17 : Sum Reg.Support.LegacyCausalCoordinates.ICData Reg.Support.LegacyCausalCoordinates.OIData :=
  @Sum.inr Reg.Support.LegacyCausalCoordinates.ICData Reg.Support.LegacyCausalCoordinates.OIData
    (@Prod.mk Bool (Prod (Prod Bool Bool) (Prod Bool Bool)) Bool.false
      (@Prod.mk (Prod Bool Bool) (Prod Bool Bool) (@Prod.mk Bool Bool Bool.true Bool.true)
        (@Prod.mk Bool Bool Bool.true Bool.false)))

noncomputable def state_18 : Sum Reg.Support.LegacyCausalCoordinates.ICData Reg.Support.LegacyCausalCoordinates.OIData :=
  @Sum.inr Reg.Support.LegacyCausalCoordinates.ICData Reg.Support.LegacyCausalCoordinates.OIData
    (@Prod.mk Bool (Prod (Prod Bool Bool) (Prod Bool Bool)) Bool.false
      (@Prod.mk (Prod Bool Bool) (Prod Bool Bool) (@Prod.mk Bool Bool Bool.true Bool.true)
        (@Prod.mk Bool Bool Bool.false Bool.true)))

noncomputable def state_19 : Sum Reg.Support.LegacyCausalCoordinates.ICData Reg.Support.LegacyCausalCoordinates.OIData :=
  @Sum.inr Reg.Support.LegacyCausalCoordinates.ICData Reg.Support.LegacyCausalCoordinates.OIData
    (@Prod.mk Bool (Prod (Prod Bool Bool) (Prod Bool Bool)) Bool.false
      (@Prod.mk (Prod Bool Bool) (Prod Bool Bool) (@Prod.mk Bool Bool Bool.true Bool.true)
        (@Prod.mk Bool Bool Bool.false Bool.false)))

noncomputable def state_20 : Sum Reg.Support.LegacyCausalCoordinates.ICData Reg.Support.LegacyCausalCoordinates.OIData :=
  @Sum.inr Reg.Support.LegacyCausalCoordinates.ICData Reg.Support.LegacyCausalCoordinates.OIData
    (@Prod.mk Bool (Prod (Prod Bool Bool) (Prod Bool Bool)) Bool.false
      (@Prod.mk (Prod Bool Bool) (Prod Bool Bool) (@Prod.mk Bool Bool Bool.true Bool.false)
        (@Prod.mk Bool Bool Bool.true Bool.true)))

noncomputable def state_21 : Sum Reg.Support.LegacyCausalCoordinates.ICData Reg.Support.LegacyCausalCoordinates.OIData :=
  @Sum.inr Reg.Support.LegacyCausalCoordinates.ICData Reg.Support.LegacyCausalCoordinates.OIData
    (@Prod.mk Bool (Prod (Prod Bool Bool) (Prod Bool Bool)) Bool.false
      (@Prod.mk (Prod Bool Bool) (Prod Bool Bool) (@Prod.mk Bool Bool Bool.true Bool.false)
        (@Prod.mk Bool Bool Bool.true Bool.false)))

noncomputable def state_22 : Sum Reg.Support.LegacyCausalCoordinates.ICData Reg.Support.LegacyCausalCoordinates.OIData :=
  @Sum.inr Reg.Support.LegacyCausalCoordinates.ICData Reg.Support.LegacyCausalCoordinates.OIData
    (@Prod.mk Bool (Prod (Prod Bool Bool) (Prod Bool Bool)) Bool.false
      (@Prod.mk (Prod Bool Bool) (Prod Bool Bool) (@Prod.mk Bool Bool Bool.true Bool.false)
        (@Prod.mk Bool Bool Bool.false Bool.true)))

noncomputable def state_23 : Sum Reg.Support.LegacyCausalCoordinates.ICData Reg.Support.LegacyCausalCoordinates.OIData :=
  @Sum.inr Reg.Support.LegacyCausalCoordinates.ICData Reg.Support.LegacyCausalCoordinates.OIData
    (@Prod.mk Bool (Prod (Prod Bool Bool) (Prod Bool Bool)) Bool.false
      (@Prod.mk (Prod Bool Bool) (Prod Bool Bool) (@Prod.mk Bool Bool Bool.true Bool.false)
        (@Prod.mk Bool Bool Bool.false Bool.false)))

noncomputable def state_24 : Sum Reg.Support.LegacyCausalCoordinates.ICData Reg.Support.LegacyCausalCoordinates.OIData :=
  @Sum.inr Reg.Support.LegacyCausalCoordinates.ICData Reg.Support.LegacyCausalCoordinates.OIData
    (@Prod.mk Bool (Prod (Prod Bool Bool) (Prod Bool Bool)) Bool.false
      (@Prod.mk (Prod Bool Bool) (Prod Bool Bool) (@Prod.mk Bool Bool Bool.false Bool.true)
        (@Prod.mk Bool Bool Bool.true Bool.true)))

noncomputable def state_25 : Sum Reg.Support.LegacyCausalCoordinates.ICData Reg.Support.LegacyCausalCoordinates.OIData :=
  @Sum.inr Reg.Support.LegacyCausalCoordinates.ICData Reg.Support.LegacyCausalCoordinates.OIData
    (@Prod.mk Bool (Prod (Prod Bool Bool) (Prod Bool Bool)) Bool.false
      (@Prod.mk (Prod Bool Bool) (Prod Bool Bool) (@Prod.mk Bool Bool Bool.false Bool.true)
        (@Prod.mk Bool Bool Bool.true Bool.false)))

noncomputable def state_26 : Sum Reg.Support.LegacyCausalCoordinates.ICData Reg.Support.LegacyCausalCoordinates.OIData :=
  @Sum.inr Reg.Support.LegacyCausalCoordinates.ICData Reg.Support.LegacyCausalCoordinates.OIData
    (@Prod.mk Bool (Prod (Prod Bool Bool) (Prod Bool Bool)) Bool.false
      (@Prod.mk (Prod Bool Bool) (Prod Bool Bool) (@Prod.mk Bool Bool Bool.false Bool.true)
        (@Prod.mk Bool Bool Bool.false Bool.true)))

noncomputable def state_27 : Sum Reg.Support.LegacyCausalCoordinates.ICData Reg.Support.LegacyCausalCoordinates.OIData :=
  @Sum.inr Reg.Support.LegacyCausalCoordinates.ICData Reg.Support.LegacyCausalCoordinates.OIData
    (@Prod.mk Bool (Prod (Prod Bool Bool) (Prod Bool Bool)) Bool.false
      (@Prod.mk (Prod Bool Bool) (Prod Bool Bool) (@Prod.mk Bool Bool Bool.false Bool.true)
        (@Prod.mk Bool Bool Bool.false Bool.false)))

noncomputable def state_28 : Sum Reg.Support.LegacyCausalCoordinates.ICData Reg.Support.LegacyCausalCoordinates.OIData :=
  @Sum.inr Reg.Support.LegacyCausalCoordinates.ICData Reg.Support.LegacyCausalCoordinates.OIData
    (@Prod.mk Bool (Prod (Prod Bool Bool) (Prod Bool Bool)) Bool.false
      (@Prod.mk (Prod Bool Bool) (Prod Bool Bool) (@Prod.mk Bool Bool Bool.false Bool.false)
        (@Prod.mk Bool Bool Bool.true Bool.true)))

noncomputable def state_29 : Sum Reg.Support.LegacyCausalCoordinates.ICData Reg.Support.LegacyCausalCoordinates.OIData :=
  @Sum.inr Reg.Support.LegacyCausalCoordinates.ICData Reg.Support.LegacyCausalCoordinates.OIData
    (@Prod.mk Bool (Prod (Prod Bool Bool) (Prod Bool Bool)) Bool.false
      (@Prod.mk (Prod Bool Bool) (Prod Bool Bool) (@Prod.mk Bool Bool Bool.false Bool.false)
        (@Prod.mk Bool Bool Bool.true Bool.false)))

noncomputable def state_30 : Sum Reg.Support.LegacyCausalCoordinates.ICData Reg.Support.LegacyCausalCoordinates.OIData :=
  @Sum.inr Reg.Support.LegacyCausalCoordinates.ICData Reg.Support.LegacyCausalCoordinates.OIData
    (@Prod.mk Bool (Prod (Prod Bool Bool) (Prod Bool Bool)) Bool.false
      (@Prod.mk (Prod Bool Bool) (Prod Bool Bool) (@Prod.mk Bool Bool Bool.false Bool.false)
        (@Prod.mk Bool Bool Bool.false Bool.true)))

noncomputable def state_31 : Sum Reg.Support.LegacyCausalCoordinates.ICData Reg.Support.LegacyCausalCoordinates.OIData :=
  @Sum.inr Reg.Support.LegacyCausalCoordinates.ICData Reg.Support.LegacyCausalCoordinates.OIData
    (@Prod.mk Bool (Prod (Prod Bool Bool) (Prod Bool Bool)) Bool.false
      (@Prod.mk (Prod Bool Bool) (Prod Bool Bool) (@Prod.mk Bool Bool Bool.false Bool.false)
        (@Prod.mk Bool Bool Bool.false Bool.false)))

noncomputable def state_32 : Prod Reg.Support.LegacyFiniteTransport.Three
  (Prod Reg.Support.LegacyFiniteTransport.Three Reg.Support.LegacyFiniteTransport.Three) :=
  @Prod.mk Reg.Support.LegacyFiniteTransport.Three
    (Prod Reg.Support.LegacyFiniteTransport.Three Reg.Support.LegacyFiniteTransport.Three) (@Sum.inl Bool Unit Bool.true)
    (@Prod.mk Reg.Support.LegacyFiniteTransport.Three Reg.Support.LegacyFiniteTransport.Three
      (@Sum.inl Bool Unit Bool.true) (@Sum.inl Bool Unit Bool.true))

noncomputable def state_33 : Prod Reg.Support.LegacyFiniteTransport.Three
  (Prod Reg.Support.LegacyFiniteTransport.Three Reg.Support.LegacyFiniteTransport.Three) :=
  @Prod.mk Reg.Support.LegacyFiniteTransport.Three
    (Prod Reg.Support.LegacyFiniteTransport.Three Reg.Support.LegacyFiniteTransport.Three) (@Sum.inl Bool Unit Bool.true)
    (@Prod.mk Reg.Support.LegacyFiniteTransport.Three Reg.Support.LegacyFiniteTransport.Three
      (@Sum.inl Bool Unit Bool.true) (@Sum.inl Bool Unit Bool.false))

noncomputable def state_34 : Prod Reg.Support.LegacyFiniteTransport.Three
  (Prod Reg.Support.LegacyFiniteTransport.Three Reg.Support.LegacyFiniteTransport.Three) :=
  @Prod.mk Reg.Support.LegacyFiniteTransport.Three
    (Prod Reg.Support.LegacyFiniteTransport.Three Reg.Support.LegacyFiniteTransport.Three) (@Sum.inl Bool Unit Bool.true)
    (@Prod.mk Reg.Support.LegacyFiniteTransport.Three Reg.Support.LegacyFiniteTransport.Three
      (@Sum.inl Bool Unit Bool.true) (@Sum.inr Bool Unit PUnit.unit))

noncomputable def state_35 : Prod Reg.Support.LegacyFiniteTransport.Three
  (Prod Reg.Support.LegacyFiniteTransport.Three Reg.Support.LegacyFiniteTransport.Three) :=
  @Prod.mk Reg.Support.LegacyFiniteTransport.Three
    (Prod Reg.Support.LegacyFiniteTransport.Three Reg.Support.LegacyFiniteTransport.Three) (@Sum.inl Bool Unit Bool.true)
    (@Prod.mk Reg.Support.LegacyFiniteTransport.Three Reg.Support.LegacyFiniteTransport.Three
      (@Sum.inl Bool Unit Bool.false) (@Sum.inl Bool Unit Bool.true))

noncomputable def state_36 : Prod Reg.Support.LegacyFiniteTransport.Three
  (Prod Reg.Support.LegacyFiniteTransport.Three Reg.Support.LegacyFiniteTransport.Three) :=
  @Prod.mk Reg.Support.LegacyFiniteTransport.Three
    (Prod Reg.Support.LegacyFiniteTransport.Three Reg.Support.LegacyFiniteTransport.Three) (@Sum.inl Bool Unit Bool.true)
    (@Prod.mk Reg.Support.LegacyFiniteTransport.Three Reg.Support.LegacyFiniteTransport.Three
      (@Sum.inl Bool Unit Bool.false) (@Sum.inl Bool Unit Bool.false))

noncomputable def state_37 : Prod Reg.Support.LegacyFiniteTransport.Three
  (Prod Reg.Support.LegacyFiniteTransport.Three Reg.Support.LegacyFiniteTransport.Three) :=
  @Prod.mk Reg.Support.LegacyFiniteTransport.Three
    (Prod Reg.Support.LegacyFiniteTransport.Three Reg.Support.LegacyFiniteTransport.Three) (@Sum.inl Bool Unit Bool.true)
    (@Prod.mk Reg.Support.LegacyFiniteTransport.Three Reg.Support.LegacyFiniteTransport.Three
      (@Sum.inl Bool Unit Bool.false) (@Sum.inr Bool Unit PUnit.unit))

noncomputable def state_38 : Prod Reg.Support.LegacyFiniteTransport.Three
  (Prod Reg.Support.LegacyFiniteTransport.Three Reg.Support.LegacyFiniteTransport.Three) :=
  @Prod.mk Reg.Support.LegacyFiniteTransport.Three
    (Prod Reg.Support.LegacyFiniteTransport.Three Reg.Support.LegacyFiniteTransport.Three) (@Sum.inl Bool Unit Bool.true)
    (@Prod.mk Reg.Support.LegacyFiniteTransport.Three Reg.Support.LegacyFiniteTransport.Three
      (@Sum.inr Bool Unit PUnit.unit) (@Sum.inl Bool Unit Bool.true))

noncomputable def state_39 : Prod Reg.Support.LegacyFiniteTransport.Three
  (Prod Reg.Support.LegacyFiniteTransport.Three Reg.Support.LegacyFiniteTransport.Three) :=
  @Prod.mk Reg.Support.LegacyFiniteTransport.Three
    (Prod Reg.Support.LegacyFiniteTransport.Three Reg.Support.LegacyFiniteTransport.Three) (@Sum.inl Bool Unit Bool.true)
    (@Prod.mk Reg.Support.LegacyFiniteTransport.Three Reg.Support.LegacyFiniteTransport.Three
      (@Sum.inr Bool Unit PUnit.unit) (@Sum.inl Bool Unit Bool.false))

noncomputable def state_40 : Prod Reg.Support.LegacyFiniteTransport.Three
  (Prod Reg.Support.LegacyFiniteTransport.Three Reg.Support.LegacyFiniteTransport.Three) :=
  @Prod.mk Reg.Support.LegacyFiniteTransport.Three
    (Prod Reg.Support.LegacyFiniteTransport.Three Reg.Support.LegacyFiniteTransport.Three) (@Sum.inl Bool Unit Bool.true)
    (@Prod.mk Reg.Support.LegacyFiniteTransport.Three Reg.Support.LegacyFiniteTransport.Three
      (@Sum.inr Bool Unit PUnit.unit) (@Sum.inr Bool Unit PUnit.unit))

noncomputable def state_41 : Prod Reg.Support.LegacyFiniteTransport.Three
  (Prod Reg.Support.LegacyFiniteTransport.Three Reg.Support.LegacyFiniteTransport.Three) :=
  @Prod.mk Reg.Support.LegacyFiniteTransport.Three
    (Prod Reg.Support.LegacyFiniteTransport.Three Reg.Support.LegacyFiniteTransport.Three) (@Sum.inl Bool Unit Bool.false)
    (@Prod.mk Reg.Support.LegacyFiniteTransport.Three Reg.Support.LegacyFiniteTransport.Three
      (@Sum.inl Bool Unit Bool.true) (@Sum.inl Bool Unit Bool.true))

noncomputable def state_42 : Prod Reg.Support.LegacyFiniteTransport.Three
  (Prod Reg.Support.LegacyFiniteTransport.Three Reg.Support.LegacyFiniteTransport.Three) :=
  @Prod.mk Reg.Support.LegacyFiniteTransport.Three
    (Prod Reg.Support.LegacyFiniteTransport.Three Reg.Support.LegacyFiniteTransport.Three) (@Sum.inl Bool Unit Bool.false)
    (@Prod.mk Reg.Support.LegacyFiniteTransport.Three Reg.Support.LegacyFiniteTransport.Three
      (@Sum.inl Bool Unit Bool.true) (@Sum.inl Bool Unit Bool.false))

noncomputable def state_43 : Prod Reg.Support.LegacyFiniteTransport.Three
  (Prod Reg.Support.LegacyFiniteTransport.Three Reg.Support.LegacyFiniteTransport.Three) :=
  @Prod.mk Reg.Support.LegacyFiniteTransport.Three
    (Prod Reg.Support.LegacyFiniteTransport.Three Reg.Support.LegacyFiniteTransport.Three) (@Sum.inl Bool Unit Bool.false)
    (@Prod.mk Reg.Support.LegacyFiniteTransport.Three Reg.Support.LegacyFiniteTransport.Three
      (@Sum.inl Bool Unit Bool.true) (@Sum.inr Bool Unit PUnit.unit))

noncomputable def state_44 : Prod Reg.Support.LegacyFiniteTransport.Three
  (Prod Reg.Support.LegacyFiniteTransport.Three Reg.Support.LegacyFiniteTransport.Three) :=
  @Prod.mk Reg.Support.LegacyFiniteTransport.Three
    (Prod Reg.Support.LegacyFiniteTransport.Three Reg.Support.LegacyFiniteTransport.Three) (@Sum.inl Bool Unit Bool.false)
    (@Prod.mk Reg.Support.LegacyFiniteTransport.Three Reg.Support.LegacyFiniteTransport.Three
      (@Sum.inl Bool Unit Bool.false) (@Sum.inl Bool Unit Bool.true))

noncomputable def state_45 : Prod Reg.Support.LegacyFiniteTransport.Three
  (Prod Reg.Support.LegacyFiniteTransport.Three Reg.Support.LegacyFiniteTransport.Three) :=
  @Prod.mk Reg.Support.LegacyFiniteTransport.Three
    (Prod Reg.Support.LegacyFiniteTransport.Three Reg.Support.LegacyFiniteTransport.Three) (@Sum.inl Bool Unit Bool.false)
    (@Prod.mk Reg.Support.LegacyFiniteTransport.Three Reg.Support.LegacyFiniteTransport.Three
      (@Sum.inl Bool Unit Bool.false) (@Sum.inl Bool Unit Bool.false))

noncomputable def state_46 : Prod Reg.Support.LegacyFiniteTransport.Three
  (Prod Reg.Support.LegacyFiniteTransport.Three Reg.Support.LegacyFiniteTransport.Three) :=
  @Prod.mk Reg.Support.LegacyFiniteTransport.Three
    (Prod Reg.Support.LegacyFiniteTransport.Three Reg.Support.LegacyFiniteTransport.Three) (@Sum.inl Bool Unit Bool.false)
    (@Prod.mk Reg.Support.LegacyFiniteTransport.Three Reg.Support.LegacyFiniteTransport.Three
      (@Sum.inl Bool Unit Bool.false) (@Sum.inr Bool Unit PUnit.unit))

noncomputable def state_47 : Prod Reg.Support.LegacyFiniteTransport.Three
  (Prod Reg.Support.LegacyFiniteTransport.Three Reg.Support.LegacyFiniteTransport.Three) :=
  @Prod.mk Reg.Support.LegacyFiniteTransport.Three
    (Prod Reg.Support.LegacyFiniteTransport.Three Reg.Support.LegacyFiniteTransport.Three) (@Sum.inl Bool Unit Bool.false)
    (@Prod.mk Reg.Support.LegacyFiniteTransport.Three Reg.Support.LegacyFiniteTransport.Three
      (@Sum.inr Bool Unit PUnit.unit) (@Sum.inl Bool Unit Bool.true))

noncomputable def state_48 : Prod Reg.Support.LegacyFiniteTransport.Three
  (Prod Reg.Support.LegacyFiniteTransport.Three Reg.Support.LegacyFiniteTransport.Three) :=
  @Prod.mk Reg.Support.LegacyFiniteTransport.Three
    (Prod Reg.Support.LegacyFiniteTransport.Three Reg.Support.LegacyFiniteTransport.Three) (@Sum.inl Bool Unit Bool.false)
    (@Prod.mk Reg.Support.LegacyFiniteTransport.Three Reg.Support.LegacyFiniteTransport.Three
      (@Sum.inr Bool Unit PUnit.unit) (@Sum.inl Bool Unit Bool.false))

noncomputable def state_49 : Prod Reg.Support.LegacyFiniteTransport.Three
  (Prod Reg.Support.LegacyFiniteTransport.Three Reg.Support.LegacyFiniteTransport.Three) :=
  @Prod.mk Reg.Support.LegacyFiniteTransport.Three
    (Prod Reg.Support.LegacyFiniteTransport.Three Reg.Support.LegacyFiniteTransport.Three) (@Sum.inl Bool Unit Bool.false)
    (@Prod.mk Reg.Support.LegacyFiniteTransport.Three Reg.Support.LegacyFiniteTransport.Three
      (@Sum.inr Bool Unit PUnit.unit) (@Sum.inr Bool Unit PUnit.unit))

noncomputable def state_50 : Prod Reg.Support.LegacyFiniteTransport.Three
  (Prod Reg.Support.LegacyFiniteTransport.Three Reg.Support.LegacyFiniteTransport.Three) :=
  @Prod.mk Reg.Support.LegacyFiniteTransport.Three
    (Prod Reg.Support.LegacyFiniteTransport.Three Reg.Support.LegacyFiniteTransport.Three) (@Sum.inr Bool Unit PUnit.unit)
    (@Prod.mk Reg.Support.LegacyFiniteTransport.Three Reg.Support.LegacyFiniteTransport.Three
      (@Sum.inl Bool Unit Bool.true) (@Sum.inl Bool Unit Bool.true))

noncomputable def state_51 : Prod Reg.Support.LegacyFiniteTransport.Three
  (Prod Reg.Support.LegacyFiniteTransport.Three Reg.Support.LegacyFiniteTransport.Three) :=
  @Prod.mk Reg.Support.LegacyFiniteTransport.Three
    (Prod Reg.Support.LegacyFiniteTransport.Three Reg.Support.LegacyFiniteTransport.Three) (@Sum.inr Bool Unit PUnit.unit)
    (@Prod.mk Reg.Support.LegacyFiniteTransport.Three Reg.Support.LegacyFiniteTransport.Three
      (@Sum.inl Bool Unit Bool.true) (@Sum.inl Bool Unit Bool.false))

noncomputable def state_52 : Prod Reg.Support.LegacyFiniteTransport.Three
  (Prod Reg.Support.LegacyFiniteTransport.Three Reg.Support.LegacyFiniteTransport.Three) :=
  @Prod.mk Reg.Support.LegacyFiniteTransport.Three
    (Prod Reg.Support.LegacyFiniteTransport.Three Reg.Support.LegacyFiniteTransport.Three) (@Sum.inr Bool Unit PUnit.unit)
    (@Prod.mk Reg.Support.LegacyFiniteTransport.Three Reg.Support.LegacyFiniteTransport.Three
      (@Sum.inl Bool Unit Bool.true) (@Sum.inr Bool Unit PUnit.unit))

noncomputable def state_53 : Prod Reg.Support.LegacyFiniteTransport.Three
  (Prod Reg.Support.LegacyFiniteTransport.Three Reg.Support.LegacyFiniteTransport.Three) :=
  @Prod.mk Reg.Support.LegacyFiniteTransport.Three
    (Prod Reg.Support.LegacyFiniteTransport.Three Reg.Support.LegacyFiniteTransport.Three) (@Sum.inr Bool Unit PUnit.unit)
    (@Prod.mk Reg.Support.LegacyFiniteTransport.Three Reg.Support.LegacyFiniteTransport.Three
      (@Sum.inl Bool Unit Bool.false) (@Sum.inl Bool Unit Bool.true))

noncomputable def state_54 : Prod Reg.Support.LegacyFiniteTransport.Three
  (Prod Reg.Support.LegacyFiniteTransport.Three Reg.Support.LegacyFiniteTransport.Three) :=
  @Prod.mk Reg.Support.LegacyFiniteTransport.Three
    (Prod Reg.Support.LegacyFiniteTransport.Three Reg.Support.LegacyFiniteTransport.Three) (@Sum.inr Bool Unit PUnit.unit)
    (@Prod.mk Reg.Support.LegacyFiniteTransport.Three Reg.Support.LegacyFiniteTransport.Three
      (@Sum.inl Bool Unit Bool.false) (@Sum.inl Bool Unit Bool.false))

noncomputable def state_55 : Prod Reg.Support.LegacyFiniteTransport.Three
  (Prod Reg.Support.LegacyFiniteTransport.Three Reg.Support.LegacyFiniteTransport.Three) :=
  @Prod.mk Reg.Support.LegacyFiniteTransport.Three
    (Prod Reg.Support.LegacyFiniteTransport.Three Reg.Support.LegacyFiniteTransport.Three) (@Sum.inr Bool Unit PUnit.unit)
    (@Prod.mk Reg.Support.LegacyFiniteTransport.Three Reg.Support.LegacyFiniteTransport.Three
      (@Sum.inl Bool Unit Bool.false) (@Sum.inr Bool Unit PUnit.unit))

noncomputable def state_56 : Prod Reg.Support.LegacyFiniteTransport.Three
  (Prod Reg.Support.LegacyFiniteTransport.Three Reg.Support.LegacyFiniteTransport.Three) :=
  @Prod.mk Reg.Support.LegacyFiniteTransport.Three
    (Prod Reg.Support.LegacyFiniteTransport.Three Reg.Support.LegacyFiniteTransport.Three) (@Sum.inr Bool Unit PUnit.unit)
    (@Prod.mk Reg.Support.LegacyFiniteTransport.Three Reg.Support.LegacyFiniteTransport.Three
      (@Sum.inr Bool Unit PUnit.unit) (@Sum.inl Bool Unit Bool.true))

noncomputable def state_57 : Prod Reg.Support.LegacyFiniteTransport.Three
  (Prod Reg.Support.LegacyFiniteTransport.Three Reg.Support.LegacyFiniteTransport.Three) :=
  @Prod.mk Reg.Support.LegacyFiniteTransport.Three
    (Prod Reg.Support.LegacyFiniteTransport.Three Reg.Support.LegacyFiniteTransport.Three) (@Sum.inr Bool Unit PUnit.unit)
    (@Prod.mk Reg.Support.LegacyFiniteTransport.Three Reg.Support.LegacyFiniteTransport.Three
      (@Sum.inr Bool Unit PUnit.unit) (@Sum.inl Bool Unit Bool.false))

noncomputable def state_58 : Prod Reg.Support.LegacyFiniteTransport.Three
  (Prod Reg.Support.LegacyFiniteTransport.Three Reg.Support.LegacyFiniteTransport.Three) :=
  @Prod.mk Reg.Support.LegacyFiniteTransport.Three
    (Prod Reg.Support.LegacyFiniteTransport.Three Reg.Support.LegacyFiniteTransport.Three) (@Sum.inr Bool Unit PUnit.unit)
    (@Prod.mk Reg.Support.LegacyFiniteTransport.Three Reg.Support.LegacyFiniteTransport.Three
      (@Sum.inr Bool Unit PUnit.unit) (@Sum.inr Bool Unit PUnit.unit))

noncomputable def state_59 : D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.DeterministicBoolSCM :=
  { direction := D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.CausalDirection.xCausesY,
    root := fun a =>
      @Decidable.rec (@Eq Bool a Bool.true) (fun x => (fun a => Bool) a)
        (fun h =>
          @Decidable.rec (@Eq Bool a Bool.false) (fun x => (fun a => Bool) a)
            (fun h_1 =>
              False.rec
                (fun x =>
                  (fun a a_1 => (fun a => Bool) a) a
                    (@Multiset.Pi.cons._proof_1 Bool (@Quotient.mk (List Bool) (List.isSetoid Bool) (@List.nil Bool))
                      Bool.false a
                      (@Multiset.Pi.cons._proof_1 Bool
                        (@Quotient.mk (List Bool) (List.isSetoid Bool) (@List.cons Bool Bool.false (@List.nil Bool)))
                        Bool.true a (@Finset.mem_univ Bool Bool.fintype a) h)
                      h_1))
                (@List.Mem.casesOn Bool a
                  (fun a_1 x =>
                    @Eq (List Bool) (@List.nil Bool) a_1 →
                      @HEq
                          (@Membership.mem Bool (Multiset Bool) (@Multiset.instMembership Bool)
                            (@OfNat.ofNat (Multiset Bool) (nat_lit 0)
                              (@Zero.toOfNat0 (Multiset Bool) (@Multiset.instZero Bool)))
                            a)
                          (@Multiset.Pi.cons._proof_1 Bool
                            (@Quotient.mk (List Bool) (List.isSetoid Bool) (@List.nil Bool)) Bool.false a
                            (@Multiset.Pi.cons._proof_1 Bool
                              (@Quotient.mk (List Bool) (List.isSetoid Bool)
                                (@List.cons Bool Bool.false (@List.nil Bool)))
                              Bool.true a (@Finset.mem_univ Bool Bool.fintype a) h)
                            h_1)
                          (@List.Mem Bool a a_1) x →
                        False)
                  (@List.nil Bool)
                  (@Multiset.Pi.cons._proof_1 Bool (@Quotient.mk (List Bool) (List.isSetoid Bool) (@List.nil Bool))
                    Bool.false a
                    (@Multiset.Pi.cons._proof_1 Bool
                      (@Quotient.mk (List Bool) (List.isSetoid Bool) (@List.cons Bool Bool.false (@List.nil Bool)))
                      Bool.true a (@Finset.mem_univ Bool Bool.fintype a) h)
                    h_1)
                  (fun as h_2 =>
                    @False.elim
                      (@HEq
                          (@Membership.mem Bool (Multiset Bool) (@Multiset.instMembership Bool)
                            (@OfNat.ofNat (Multiset Bool) (nat_lit 0)
                              (@Zero.toOfNat0 (Multiset Bool) (@Multiset.instZero Bool)))
                            a)
                          (@Multiset.Pi.cons._proof_1 Bool
                            (@Quotient.mk (List Bool) (List.isSetoid Bool) (@List.nil Bool)) Bool.false a
                            (@Multiset.Pi.cons._proof_1 Bool
                              (@Quotient.mk (List Bool) (List.isSetoid Bool)
                                (@List.cons Bool Bool.false (@List.nil Bool)))
                              Bool.true a (@Finset.mem_univ Bool Bool.fintype a) h)
                            h_1)
                          (@List.Mem Bool a (@List.cons Bool a as)) (@List.Mem.head Bool a as) →
                        False)
                      (@noConfusion_of_Nat (List Bool) (@List.ctorIdx Bool) (@List.nil Bool) (@List.cons Bool a as) h_2))
                  (fun b {as} a_1 h_2 =>
                    @False.elim
                      (@HEq
                          (@Membership.mem Bool (Multiset Bool) (@Multiset.instMembership Bool)
                            (@OfNat.ofNat (Multiset Bool) (nat_lit 0)
                              (@Zero.toOfNat0 (Multiset Bool) (@Multiset.instZero Bool)))
                            a)
                          (@Multiset.Pi.cons._proof_1 Bool
                            (@Quotient.mk (List Bool) (List.isSetoid Bool) (@List.nil Bool)) Bool.false a
                            (@Multiset.Pi.cons._proof_1 Bool
                              (@Quotient.mk (List Bool) (List.isSetoid Bool)
                                (@List.cons Bool Bool.false (@List.nil Bool)))
                              Bool.true a (@Finset.mem_univ Bool Bool.fintype a) h)
                            h_1)
                          (@List.Mem Bool a (@List.cons Bool b as)) (@List.Mem.tail Bool a b as a_1) →
                        False)
                      (@noConfusion_of_Nat (List Bool) (@List.ctorIdx Bool) (@List.nil Bool) (@List.cons Bool b as) h_2))
                  (@Eq.refl (List Bool) (@List.nil Bool))
                  (@HEq.refl
                    (@Membership.mem Bool (Multiset Bool) (@Multiset.instMembership Bool)
                      (@OfNat.ofNat (Multiset Bool) (nat_lit 0)
                        (@Zero.toOfNat0 (Multiset Bool) (@Multiset.instZero Bool)))
                      a)
                    (@Multiset.Pi.cons._proof_1 Bool (@Quotient.mk (List Bool) (List.isSetoid Bool) (@List.nil Bool))
                      Bool.false a
                      (@Multiset.Pi.cons._proof_1 Bool
                        (@Quotient.mk (List Bool) (List.isSetoid Bool) (@List.cons Bool Bool.false (@List.nil Bool)))
                        Bool.true a (@Finset.mem_univ Bool Bool.fintype a) h)
                      h_1))))
            (fun h => @Eq.rec Bool Bool.false (fun x x_1 => (fun a => Bool) x) Bool.true a (@Eq.symm Bool a Bool.false h))
            (@Bool.rec (fun x => (fun a b => Decidable (@Eq Bool a b)) x Bool.false)
              (@Decidable.isTrue (@Eq Bool Bool.false Bool.false) (@rfl Bool Bool.false))
              (@Decidable.isFalse (@Eq Bool Bool.true Bool.false) fun h => @Bool.noConfusion False Bool.true Bool.false h)
              a))
        (fun h => @Eq.rec Bool Bool.true (fun x x_1 => (fun a => Bool) x) Bool.true a (@Eq.symm Bool a Bool.true h))
        (@Bool.rec (fun x => (fun a b => Decidable (@Eq Bool a b)) x Bool.true)
          (@Decidable.isFalse (@Eq Bool Bool.false Bool.true) fun h => @Bool.noConfusion False Bool.false Bool.true h)
          (@Decidable.isTrue (@Eq Bool Bool.true Bool.true) (@rfl Bool Bool.true)) a),
    child := fun a =>
      @Decidable.rec (@Eq Bool a Bool.true) (fun x => (fun a => Bool) a)
        (fun h =>
          @Decidable.rec (@Eq Bool a Bool.false) (fun x => (fun a => Bool) a)
            (fun h_1 =>
              False.rec
                (fun x =>
                  (fun a a_1 => (fun a => Bool) a) a
                    (@Multiset.Pi.cons._proof_1 Bool (@Quotient.mk (List Bool) (List.isSetoid Bool) (@List.nil Bool))
                      Bool.false a
                      (@Multiset.Pi.cons._proof_1 Bool
                        (@Quotient.mk (List Bool) (List.isSetoid Bool) (@List.cons Bool Bool.false (@List.nil Bool)))
                        Bool.true a (@Finset.mem_univ Bool Bool.fintype a) h)
                      h_1))
                (@List.Mem.casesOn Bool a
                  (fun a_1 x =>
                    @Eq (List Bool) (@List.nil Bool) a_1 →
                      @HEq
                          (@Membership.mem Bool (Multiset Bool) (@Multiset.instMembership Bool)
                            (@OfNat.ofNat (Multiset Bool) (nat_lit 0)
                              (@Zero.toOfNat0 (Multiset Bool) (@Multiset.instZero Bool)))
                            a)
                          (@Multiset.Pi.cons._proof_1 Bool
                            (@Quotient.mk (List Bool) (List.isSetoid Bool) (@List.nil Bool)) Bool.false a
                            (@Multiset.Pi.cons._proof_1 Bool
                              (@Quotient.mk (List Bool) (List.isSetoid Bool)
                                (@List.cons Bool Bool.false (@List.nil Bool)))
                              Bool.true a (@Finset.mem_univ Bool Bool.fintype a) h)
                            h_1)
                          (@List.Mem Bool a a_1) x →
                        False)
                  (@List.nil Bool)
                  (@Multiset.Pi.cons._proof_1 Bool (@Quotient.mk (List Bool) (List.isSetoid Bool) (@List.nil Bool))
                    Bool.false a
                    (@Multiset.Pi.cons._proof_1 Bool
                      (@Quotient.mk (List Bool) (List.isSetoid Bool) (@List.cons Bool Bool.false (@List.nil Bool)))
                      Bool.true a (@Finset.mem_univ Bool Bool.fintype a) h)
                    h_1)
                  (fun as h_2 =>
                    @False.elim
                      (@HEq
                          (@Membership.mem Bool (Multiset Bool) (@Multiset.instMembership Bool)
                            (@OfNat.ofNat (Multiset Bool) (nat_lit 0)
                              (@Zero.toOfNat0 (Multiset Bool) (@Multiset.instZero Bool)))
                            a)
                          (@Multiset.Pi.cons._proof_1 Bool
                            (@Quotient.mk (List Bool) (List.isSetoid Bool) (@List.nil Bool)) Bool.false a
                            (@Multiset.Pi.cons._proof_1 Bool
                              (@Quotient.mk (List Bool) (List.isSetoid Bool)
                                (@List.cons Bool Bool.false (@List.nil Bool)))
                              Bool.true a (@Finset.mem_univ Bool Bool.fintype a) h)
                            h_1)
                          (@List.Mem Bool a (@List.cons Bool a as)) (@List.Mem.head Bool a as) →
                        False)
                      (@noConfusion_of_Nat (List Bool) (@List.ctorIdx Bool) (@List.nil Bool) (@List.cons Bool a as) h_2))
                  (fun b {as} a_1 h_2 =>
                    @False.elim
                      (@HEq
                          (@Membership.mem Bool (Multiset Bool) (@Multiset.instMembership Bool)
                            (@OfNat.ofNat (Multiset Bool) (nat_lit 0)
                              (@Zero.toOfNat0 (Multiset Bool) (@Multiset.instZero Bool)))
                            a)
                          (@Multiset.Pi.cons._proof_1 Bool
                            (@Quotient.mk (List Bool) (List.isSetoid Bool) (@List.nil Bool)) Bool.false a
                            (@Multiset.Pi.cons._proof_1 Bool
                              (@Quotient.mk (List Bool) (List.isSetoid Bool)
                                (@List.cons Bool Bool.false (@List.nil Bool)))
                              Bool.true a (@Finset.mem_univ Bool Bool.fintype a) h)
                            h_1)
                          (@List.Mem Bool a (@List.cons Bool b as)) (@List.Mem.tail Bool a b as a_1) →
                        False)
                      (@noConfusion_of_Nat (List Bool) (@List.ctorIdx Bool) (@List.nil Bool) (@List.cons Bool b as) h_2))
                  (@Eq.refl (List Bool) (@List.nil Bool))
                  (@HEq.refl
                    (@Membership.mem Bool (Multiset Bool) (@Multiset.instMembership Bool)
                      (@OfNat.ofNat (Multiset Bool) (nat_lit 0)
                        (@Zero.toOfNat0 (Multiset Bool) (@Multiset.instZero Bool)))
                      a)
                    (@Multiset.Pi.cons._proof_1 Bool (@Quotient.mk (List Bool) (List.isSetoid Bool) (@List.nil Bool))
                      Bool.false a
                      (@Multiset.Pi.cons._proof_1 Bool
                        (@Quotient.mk (List Bool) (List.isSetoid Bool) (@List.cons Bool Bool.false (@List.nil Bool)))
                        Bool.true a (@Finset.mem_univ Bool Bool.fintype a) h)
                      h_1))))
            (fun h => @Eq.rec Bool Bool.false (fun x x_1 => (fun a => Bool) x) Bool.true a (@Eq.symm Bool a Bool.false h))
            (@Bool.rec (fun x => (fun a b => Decidable (@Eq Bool a b)) x Bool.false)
              (@Decidable.isTrue (@Eq Bool Bool.false Bool.false) (@rfl Bool Bool.false))
              (@Decidable.isFalse (@Eq Bool Bool.true Bool.false) fun h => @Bool.noConfusion False Bool.true Bool.false h)
              a))
        (fun h => @Eq.rec Bool Bool.true (fun x x_1 => (fun a => Bool) x) Bool.true a (@Eq.symm Bool a Bool.true h))
        (@Bool.rec (fun x => (fun a b => Decidable (@Eq Bool a b)) x Bool.true)
          (@Decidable.isFalse (@Eq Bool Bool.false Bool.true) fun h => @Bool.noConfusion False Bool.false Bool.true h)
          (@Decidable.isTrue (@Eq Bool Bool.true Bool.true) (@rfl Bool Bool.true)) a) }

noncomputable def state_60 : D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.DeterministicBoolSCM :=
  { direction := D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.CausalDirection.xCausesY,
    root := fun a =>
      @Decidable.rec (@Eq Bool a Bool.true) (fun x => (fun a => Bool) a)
        (fun h =>
          @Decidable.rec (@Eq Bool a Bool.false) (fun x => (fun a => Bool) a)
            (fun h_1 =>
              False.rec
                (fun x =>
                  (fun a a_1 => (fun a => Bool) a) a
                    (@Multiset.Pi.cons._proof_1 Bool (@Quotient.mk (List Bool) (List.isSetoid Bool) (@List.nil Bool))
                      Bool.false a
                      (@Multiset.Pi.cons._proof_1 Bool
                        (@Quotient.mk (List Bool) (List.isSetoid Bool) (@List.cons Bool Bool.false (@List.nil Bool)))
                        Bool.true a (@Finset.mem_univ Bool Bool.fintype a) h)
                      h_1))
                (@List.Mem.casesOn Bool a
                  (fun a_1 x =>
                    @Eq (List Bool) (@List.nil Bool) a_1 →
                      @HEq
                          (@Membership.mem Bool (Multiset Bool) (@Multiset.instMembership Bool)
                            (@OfNat.ofNat (Multiset Bool) (nat_lit 0)
                              (@Zero.toOfNat0 (Multiset Bool) (@Multiset.instZero Bool)))
                            a)
                          (@Multiset.Pi.cons._proof_1 Bool
                            (@Quotient.mk (List Bool) (List.isSetoid Bool) (@List.nil Bool)) Bool.false a
                            (@Multiset.Pi.cons._proof_1 Bool
                              (@Quotient.mk (List Bool) (List.isSetoid Bool)
                                (@List.cons Bool Bool.false (@List.nil Bool)))
                              Bool.true a (@Finset.mem_univ Bool Bool.fintype a) h)
                            h_1)
                          (@List.Mem Bool a a_1) x →
                        False)
                  (@List.nil Bool)
                  (@Multiset.Pi.cons._proof_1 Bool (@Quotient.mk (List Bool) (List.isSetoid Bool) (@List.nil Bool))
                    Bool.false a
                    (@Multiset.Pi.cons._proof_1 Bool
                      (@Quotient.mk (List Bool) (List.isSetoid Bool) (@List.cons Bool Bool.false (@List.nil Bool)))
                      Bool.true a (@Finset.mem_univ Bool Bool.fintype a) h)
                    h_1)
                  (fun as h_2 =>
                    @False.elim
                      (@HEq
                          (@Membership.mem Bool (Multiset Bool) (@Multiset.instMembership Bool)
                            (@OfNat.ofNat (Multiset Bool) (nat_lit 0)
                              (@Zero.toOfNat0 (Multiset Bool) (@Multiset.instZero Bool)))
                            a)
                          (@Multiset.Pi.cons._proof_1 Bool
                            (@Quotient.mk (List Bool) (List.isSetoid Bool) (@List.nil Bool)) Bool.false a
                            (@Multiset.Pi.cons._proof_1 Bool
                              (@Quotient.mk (List Bool) (List.isSetoid Bool)
                                (@List.cons Bool Bool.false (@List.nil Bool)))
                              Bool.true a (@Finset.mem_univ Bool Bool.fintype a) h)
                            h_1)
                          (@List.Mem Bool a (@List.cons Bool a as)) (@List.Mem.head Bool a as) →
                        False)
                      (@noConfusion_of_Nat (List Bool) (@List.ctorIdx Bool) (@List.nil Bool) (@List.cons Bool a as) h_2))
                  (fun b {as} a_1 h_2 =>
                    @False.elim
                      (@HEq
                          (@Membership.mem Bool (Multiset Bool) (@Multiset.instMembership Bool)
                            (@OfNat.ofNat (Multiset Bool) (nat_lit 0)
                              (@Zero.toOfNat0 (Multiset Bool) (@Multiset.instZero Bool)))
                            a)
                          (@Multiset.Pi.cons._proof_1 Bool
                            (@Quotient.mk (List Bool) (List.isSetoid Bool) (@List.nil Bool)) Bool.false a
                            (@Multiset.Pi.cons._proof_1 Bool
                              (@Quotient.mk (List Bool) (List.isSetoid Bool)
                                (@List.cons Bool Bool.false (@List.nil Bool)))
                              Bool.true a (@Finset.mem_univ Bool Bool.fintype a) h)
                            h_1)
                          (@List.Mem Bool a (@List.cons Bool b as)) (@List.Mem.tail Bool a b as a_1) →
                        False)
                      (@noConfusion_of_Nat (List Bool) (@List.ctorIdx Bool) (@List.nil Bool) (@List.cons Bool b as) h_2))
                  (@Eq.refl (List Bool) (@List.nil Bool))
                  (@HEq.refl
                    (@Membership.mem Bool (Multiset Bool) (@Multiset.instMembership Bool)
                      (@OfNat.ofNat (Multiset Bool) (nat_lit 0)
                        (@Zero.toOfNat0 (Multiset Bool) (@Multiset.instZero Bool)))
                      a)
                    (@Multiset.Pi.cons._proof_1 Bool (@Quotient.mk (List Bool) (List.isSetoid Bool) (@List.nil Bool))
                      Bool.false a
                      (@Multiset.Pi.cons._proof_1 Bool
                        (@Quotient.mk (List Bool) (List.isSetoid Bool) (@List.cons Bool Bool.false (@List.nil Bool)))
                        Bool.true a (@Finset.mem_univ Bool Bool.fintype a) h)
                      h_1))))
            (fun h => @Eq.rec Bool Bool.false (fun x x_1 => (fun a => Bool) x) Bool.true a (@Eq.symm Bool a Bool.false h))
            (@Bool.rec (fun x => (fun a b => Decidable (@Eq Bool a b)) x Bool.false)
              (@Decidable.isTrue (@Eq Bool Bool.false Bool.false) (@rfl Bool Bool.false))
              (@Decidable.isFalse (@Eq Bool Bool.true Bool.false) fun h => @Bool.noConfusion False Bool.true Bool.false h)
              a))
        (fun h => @Eq.rec Bool Bool.true (fun x x_1 => (fun a => Bool) x) Bool.true a (@Eq.symm Bool a Bool.true h))
        (@Bool.rec (fun x => (fun a b => Decidable (@Eq Bool a b)) x Bool.true)
          (@Decidable.isFalse (@Eq Bool Bool.false Bool.true) fun h => @Bool.noConfusion False Bool.false Bool.true h)
          (@Decidable.isTrue (@Eq Bool Bool.true Bool.true) (@rfl Bool Bool.true)) a),
    child := fun a =>
      @Decidable.rec (@Eq Bool a Bool.true) (fun x => (fun a => Bool) a)
        (fun h =>
          @Decidable.rec (@Eq Bool a Bool.false) (fun x => (fun a => Bool) a)
            (fun h_1 =>
              False.rec
                (fun x =>
                  (fun a a_1 => (fun a => Bool) a) a
                    (@Multiset.Pi.cons._proof_1 Bool (@Quotient.mk (List Bool) (List.isSetoid Bool) (@List.nil Bool))
                      Bool.false a
                      (@Multiset.Pi.cons._proof_1 Bool
                        (@Quotient.mk (List Bool) (List.isSetoid Bool) (@List.cons Bool Bool.false (@List.nil Bool)))
                        Bool.true a (@Finset.mem_univ Bool Bool.fintype a) h)
                      h_1))
                (@List.Mem.casesOn Bool a
                  (fun a_1 x =>
                    @Eq (List Bool) (@List.nil Bool) a_1 →
                      @HEq
                          (@Membership.mem Bool (Multiset Bool) (@Multiset.instMembership Bool)
                            (@OfNat.ofNat (Multiset Bool) (nat_lit 0)
                              (@Zero.toOfNat0 (Multiset Bool) (@Multiset.instZero Bool)))
                            a)
                          (@Multiset.Pi.cons._proof_1 Bool
                            (@Quotient.mk (List Bool) (List.isSetoid Bool) (@List.nil Bool)) Bool.false a
                            (@Multiset.Pi.cons._proof_1 Bool
                              (@Quotient.mk (List Bool) (List.isSetoid Bool)
                                (@List.cons Bool Bool.false (@List.nil Bool)))
                              Bool.true a (@Finset.mem_univ Bool Bool.fintype a) h)
                            h_1)
                          (@List.Mem Bool a a_1) x →
                        False)
                  (@List.nil Bool)
                  (@Multiset.Pi.cons._proof_1 Bool (@Quotient.mk (List Bool) (List.isSetoid Bool) (@List.nil Bool))
                    Bool.false a
                    (@Multiset.Pi.cons._proof_1 Bool
                      (@Quotient.mk (List Bool) (List.isSetoid Bool) (@List.cons Bool Bool.false (@List.nil Bool)))
                      Bool.true a (@Finset.mem_univ Bool Bool.fintype a) h)
                    h_1)
                  (fun as h_2 =>
                    @False.elim
                      (@HEq
                          (@Membership.mem Bool (Multiset Bool) (@Multiset.instMembership Bool)
                            (@OfNat.ofNat (Multiset Bool) (nat_lit 0)
                              (@Zero.toOfNat0 (Multiset Bool) (@Multiset.instZero Bool)))
                            a)
                          (@Multiset.Pi.cons._proof_1 Bool
                            (@Quotient.mk (List Bool) (List.isSetoid Bool) (@List.nil Bool)) Bool.false a
                            (@Multiset.Pi.cons._proof_1 Bool
                              (@Quotient.mk (List Bool) (List.isSetoid Bool)
                                (@List.cons Bool Bool.false (@List.nil Bool)))
                              Bool.true a (@Finset.mem_univ Bool Bool.fintype a) h)
                            h_1)
                          (@List.Mem Bool a (@List.cons Bool a as)) (@List.Mem.head Bool a as) →
                        False)
                      (@noConfusion_of_Nat (List Bool) (@List.ctorIdx Bool) (@List.nil Bool) (@List.cons Bool a as) h_2))
                  (fun b {as} a_1 h_2 =>
                    @False.elim
                      (@HEq
                          (@Membership.mem Bool (Multiset Bool) (@Multiset.instMembership Bool)
                            (@OfNat.ofNat (Multiset Bool) (nat_lit 0)
                              (@Zero.toOfNat0 (Multiset Bool) (@Multiset.instZero Bool)))
                            a)
                          (@Multiset.Pi.cons._proof_1 Bool
                            (@Quotient.mk (List Bool) (List.isSetoid Bool) (@List.nil Bool)) Bool.false a
                            (@Multiset.Pi.cons._proof_1 Bool
                              (@Quotient.mk (List Bool) (List.isSetoid Bool)
                                (@List.cons Bool Bool.false (@List.nil Bool)))
                              Bool.true a (@Finset.mem_univ Bool Bool.fintype a) h)
                            h_1)
                          (@List.Mem Bool a (@List.cons Bool b as)) (@List.Mem.tail Bool a b as a_1) →
                        False)
                      (@noConfusion_of_Nat (List Bool) (@List.ctorIdx Bool) (@List.nil Bool) (@List.cons Bool b as) h_2))
                  (@Eq.refl (List Bool) (@List.nil Bool))
                  (@HEq.refl
                    (@Membership.mem Bool (Multiset Bool) (@Multiset.instMembership Bool)
                      (@OfNat.ofNat (Multiset Bool) (nat_lit 0)
                        (@Zero.toOfNat0 (Multiset Bool) (@Multiset.instZero Bool)))
                      a)
                    (@Multiset.Pi.cons._proof_1 Bool (@Quotient.mk (List Bool) (List.isSetoid Bool) (@List.nil Bool))
                      Bool.false a
                      (@Multiset.Pi.cons._proof_1 Bool
                        (@Quotient.mk (List Bool) (List.isSetoid Bool) (@List.cons Bool Bool.false (@List.nil Bool)))
                        Bool.true a (@Finset.mem_univ Bool Bool.fintype a) h)
                      h_1))))
            (fun h =>
              @Eq.rec Bool Bool.false (fun x x_1 => (fun a => Bool) x) Bool.false a (@Eq.symm Bool a Bool.false h))
            (@Bool.rec (fun x => (fun a b => Decidable (@Eq Bool a b)) x Bool.false)
              (@Decidable.isTrue (@Eq Bool Bool.false Bool.false) (@rfl Bool Bool.false))
              (@Decidable.isFalse (@Eq Bool Bool.true Bool.false) fun h => @Bool.noConfusion False Bool.true Bool.false h)
              a))
        (fun h => @Eq.rec Bool Bool.true (fun x x_1 => (fun a => Bool) x) Bool.true a (@Eq.symm Bool a Bool.true h))
        (@Bool.rec (fun x => (fun a b => Decidable (@Eq Bool a b)) x Bool.true)
          (@Decidable.isFalse (@Eq Bool Bool.false Bool.true) fun h => @Bool.noConfusion False Bool.false Bool.true h)
          (@Decidable.isTrue (@Eq Bool Bool.true Bool.true) (@rfl Bool Bool.true)) a) }

end Reg.Catalogs.SharedInformationRoot.SealedCatalog
