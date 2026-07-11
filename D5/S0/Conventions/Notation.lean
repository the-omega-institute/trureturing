/- GID: D5/S0/Conventions/Notation
   generality: I
   mirror-B: D5/B/S0/Conventions/Notation
   mirror-E: none(waiver:notation-only)
   anchors: [GICT-v3.6-I.1-definitions-1.1-1.2]
   digest: Scoped notation names the golden ring, generator, conjugation, and norm. -/

import D5.S0.Carrier.Units
import D5.S0.Conventions.WDigits

namespace D5.S0.Conventions

open D5.S0.Carrier

scoped[Golden] notation "𝒪φ" => GoldenInt
scoped[Golden] notation "φ" => phi
scoped[Golden] notation "σφ" => conjEquiv
scoped[Golden] notation "Nφ" => normMonoidHom

open scoped Golden

theorem notation_phi_relation : (φ : 𝒪φ) ^ 2 = φ + 1 := phi_sq

theorem notation_norm_phi : Nφ (φ : 𝒪φ) = -1 := norm_phi

end D5.S0.Conventions
