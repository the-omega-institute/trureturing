/- GID: D5/S0/Diagonal/Feedback/StrategicResponseObstruction
   generality: G
   mirror-B: D5/B/S0/Diagonal/Feedback/StrategicResponseObstruction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A fixed-point-free response defeats every universally correct predictor. -/

import Mathlib.Logic.Function.Defs

/- Library-search audit trail (2026-08-16):
   * D5 searches found diagonal escape and fixed-point theorems, but no theorem for an
     arbitrary response depending on a predictor and state.
   * Loogle returned no exact match for the response hypothesis and universal-correctness
     conclusion. LeanSearch's `/api/search` endpoint returned HTTP 404.
   * Pinned Mathlib supplies `Function.IsFixedPt`, used below instead of a local duplicate,
     but no theorem with the full strategic-response statement. -/

namespace D5.S0.Diagonal.Feedback.StrategicResponseObstruction

/-- If every predictor induces a state whose response is a fixed-point-free transform of
its prediction, no predictor is correct at every state. -/
theorem strategic_response_precludes_universal_predictor
    {X Y : Type*} (twist : Y -> Y) (response : (X -> Y) -> X -> Y)
    (hfixed : forall y, ¬ Function.IsFixedPt twist y)
    (hstrategic : forall predictor : X -> Y, exists state : X,
      response predictor state = twist (predictor state)) :
    ¬ exists predictor : X -> Y, forall state : X,
      response predictor state = predictor state := by
  rintro ⟨predictor, hcorrect⟩
  obtain ⟨state, hresponse⟩ := hstrategic predictor
  exact hfixed (predictor state) (hresponse.symm.trans (hcorrect state))

#print axioms strategic_response_precludes_universal_predictor

end D5.S0.Diagonal.Feedback.StrategicResponseObstruction
