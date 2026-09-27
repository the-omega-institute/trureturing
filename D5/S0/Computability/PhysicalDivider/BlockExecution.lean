/- GID: D5/S0/Computability/PhysicalDivider/BlockExecution
   generality: G
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Configuration embedding of a bit-block operation into the divider program. -/

import D5.S0.Computability.PhysicalDivider.CallProgram
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace D5.S0.Computability.PhysicalDivider
open Turing

def liftBlockCfg (k : ActiveTape) (next : Continuation)
    (tapes : ActiveTape → Tape Bool) (c : BlockCfg) : PhysicalCfg :=
  ⟨.block k c.control next, Function.update tapes k c.tape⟩

end D5.S0.Computability.PhysicalDivider
