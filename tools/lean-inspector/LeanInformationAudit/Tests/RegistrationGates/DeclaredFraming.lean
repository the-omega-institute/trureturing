import LeanInformationAudit.Tests.RegistrationGates.IndexWork.Selected

namespace LeanInformationAudit.Tests.DeclaredFraming
open Lean Meta TemplateAudit

private def report (label : String) (ok : Bool) : MetaM Unit :=
  (if ok then logInfo else logError) m!"[{if ok then "PASS" else "FAIL"}] {label}"

run_meta do
  let env ← getEnv
  let name := `DTRIndex.A.selected
  let .ok selected := selectedPlan env name | throwError "setup: imported enrollment absent"
  let .ok bytes := planEncoding selected | throwError "setup: imported payload unavailable"
  let frame : TemplatePlanFrame := { key := name.toString.toUTF8, payload := bytes, identity := Sha256.hex bytes }
  let imported := ({} : TemplateIndex).addFrame frame env selected.enrollmentOwner
  report "imported_summary_roundtrip" ((imported.lookup name (pure () : Id Unit)).isOk &&
    imported.decodeAttempts == 1 && imported.decodedAllocationBytes ≤ 32 * bytes.size)
  report "selective_import_within_cap_accepted" ((selectedPlan env name).isOk)
  report "bounded_summary_roundtrip" (match PlanDecoder.decode bytes (32 * bytes.size) with
    | .ok (decoded, _) => (planEncoding decoded).toOption == some bytes
    | .error _ => false)
  let oversizedBytes := bytes ++ ByteArray.mk (Array.replicate 65536 32)
  let oversized := { frame with payload := oversizedBytes, identity := Sha256.hex oversizedBytes }
  let oversizedResult := ({} : TemplateIndex).addFrame oversized env selected.enrollmentOwner
  report "oversized_frame_before_decode" (oversizedResult.error == some "incomplete_closure:E8.import_framing" &&
    oversizedResult.decodeAttempts == 0)
  let capResult := ({ bytes := 8388608 : TemplateIndex }).addFrame frame env selected.enrollmentOwner
  report "import_summary_byte_cap_enforced" (capResult.error == some "incomplete_closure:E8.import_bytes" &&
    capResult.decodeAttempts == 0)
  let corrupt := { frame with payload := bytes ++ ByteArray.mk #[0] }
  let corruptResult := ({} : TemplateIndex).addFrame corrupt env selected.enrollmentOwner
  let badEncodingBytes := "99999:truncated".toUTF8
  let badEncoding := { frame with payload := badEncodingBytes, identity := Sha256.hex badEncodingBytes }
  let malformed := ({} : TemplateIndex).addFrame badEncoding env selected.enrollmentOwner
  report "malformed_frame_rejected" (corruptResult.error == some "incomplete_closure:E7.import_identity" &&
    malformed.error == some "incomplete_closure:E7.import_encoding")
  let ownerResult := ({} : TemplateIndex).addFrame frame env `WrongOwner
  report "wrong_import_owner_rejected" (ownerResult.error == some "incomplete_closure:E7.import_owner")
  report "decoder_allocation_cap" (match PlanDecoder.decode bytes 1 with
    | .error "incomplete_closure:E8.import_allocation" => true
    | _ => false)
  let stopped := corruptResult.addFrame badEncoding env selected.enrollmentOwner
  report "import_stream_stops_after_error" (stopped.error == corruptResult.error &&
    stopped.decodeAttempts == corruptResult.decodeAttempts)
  let metadata : MData := ⟨[
    (`text, .ofString "α\n\u0000β"), (`flag, .ofBool false), (`counter, .ofInt (-71)),
    (`key, .ofName `DTR.meta), (`syntax, .ofSyntax (.node .none `fixture #[
      .missing, .atom (.synthetic ⟨2⟩ ⟨3⟩ true) "text",
      .ident (.original ⟨"abc", ⟨0⟩, ⟨1⟩⟩ ⟨1⟩ ⟨"abc", ⟨2⟩, ⟨3⟩⟩ ⟨2⟩)
        ⟨"abc", ⟨0⟩, ⟨3⟩⟩ `DTR.fixture [.namespace `DTR, .decl `DTR.fixture ["field"]]]))]⟩
  let raw := Expr.mdata metadata (.letE `binder (mkConst ``Nat) (mkNatLit 17)
    (.lam `x (mkConst ``Nat) (.app (.const `fixture [.max (.param `u) (.succ .zero)]) (.bvar 0)) .implicit) false)
  let rawPlan := { selected with levelParams := [`u], plan := .expanded raw (.proofLeaf (mkConst ``True) raw) }
  let .ok rawBytes := planEncoding rawPlan | throwError "setup: raw syntax encoding failed"
  report "retained_raw_syntax_roundtrip" (match PlanDecoder.decode rawBytes (32 * rawBytes.size) with
    | .ok (decoded, _) => (planEncoding decoded).toOption == some rawBytes
    | .error _ => false)

end LeanInformationAudit.Tests.DeclaredFraming
