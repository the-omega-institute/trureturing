import LeanInformationAudit.Census.Receipt

open Lean LeanInformationAudit DispositionCensus

run_cmd do
  for bytes in ["", "abc", "line one\nline two\r\n",
      "名字" ++ String.singleton (Char.ofNat 0) ++ "é"] do
    let actual ← CensusReceipt.hashReportBytes bytes
    unless actual == "sha256:" ++ Sha256.hex bytes.toUTF8 do
      throwError "receiptNativeDigestMatches: exact UTF-8 bytes differ"
  let json := truthExportIdentity.setObjVal! "source_commit" (toJson "fixture-head")
    |>.setObjVal! "nodes" (Json.arr #[])
  let bytes := json.compress
  let actual ← CensusReceipt.hashReportBytes bytes
  let report ← IO.ofExcept <| parseReportJson json actual
  unless (checkReportBinding "fixture-head" actual report).isOk do
    throwError "receiptNativeBindingPositive: matching digest rejected"
  let changed ← CensusReceipt.hashReportBytes (bytes ++ " ")
  if (checkReportBinding "fixture-head" changed report).isOk then
    throwError "receiptNativeBindingMismatch: changed bytes accepted"
  logInfo "receiptNativeDigestMatches receiptNativeBindingPositive receiptNativeBindingMismatch"
