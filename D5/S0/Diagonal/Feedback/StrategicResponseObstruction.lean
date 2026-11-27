/- GID: D5/S0/Diagonal/Feedback/StrategicResponseObstruction
   generality: G
   mirror-B: D5/B/S0/Diagonal/Feedback/StrategicResponseObstruction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A fixed-point-free response defeats every universally correct predictor. -/

module
prelude
public import OmegaInit.Core

namespace D5.S0.Diagonal.Feedback.StrategicResponseObstruction

open Omega

/-- If every predictor induces a state whose response is a fixed-point-free transform of
its prediction, no predictor is correct at every state. -/
public theorem strategic_response_precludes_universal_predictor
    {X : Type u} {Y : Type v} (twist : Y → Y) (response : (X → Y) → X → Y)
    (fixedPointFree : ∀ y, Not (Eq (twist y) y))
    (strategic : ∀ predictor : X → Y, Omega.Exists (fun state : X =>
      Eq (response predictor state) (twist (predictor state)))) :
    Not (Omega.Exists (fun predictor : X → Y => ∀ state : X,
      Eq (response predictor state) (predictor state))) :=
  fun universal =>
    universal.elim (fun predictor correct =>
      (strategic predictor).elim (fun state responseAtState =>
        fixedPointFree (predictor state) (responseAtState.symm.trans (correct state))))

end D5.S0.Diagonal.Feedback.StrategicResponseObstruction
