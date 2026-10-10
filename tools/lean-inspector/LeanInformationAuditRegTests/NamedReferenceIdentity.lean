import LeanInformationAudit.TemplateWire

open Lean LeanInformationAudit.TemplateAudit

-- Producer vectors for the C# named-reference consumer's bounded grammar.
#eval show IO Unit from do
  let rich := Name.str (Name.num (Name.str (Name.str (Name.str .anonymous "D5") "Probe") "x.λ") 7) "claim"
  let cases : Array (String × Name × List Name × String × String) := #[
    ("rich", rich, [(`u), (`v)], "c2a7b544a37d5ebffb374626811f1f05e53ee417c7c877f4eddb4d56c7342b32", "55a8a220458148df16faf815f13d4ca0c7e2637159d82d836c2b8bd4b9262f10"),
    ("plain", (`Fixture.claim), [], "febd552b62dbe8d57db873ee5a4a4d7bcc0dc35108a6c84706eecd5b20ca580f", "adc05d5f0f79aa2d665056f434d4e18294317c4cb8fa8e52e7bf43a12593ee3d"),
    ("shared", (`Not.claim), [], "d6cf4aab8d84077ad0c3ff1c58335426114f38938757d85854325b5221bff502", "590ceb3960601fb9bfa40855bbd1debf753bd2d80d7c54d1fe5e82f65506d14c"),
    ("numericShared", Name.str (Name.num (`Not) 7) "claim", [], "87f795426861d7c2b8e99a8777b1168e2b1864cb3e47eb42382ecf16e2f4f936", "648d31ccb57d7c1f05169f687a10cb94c0c1bbf0857b9023b44ef3b513e1765e"),
    ("empty", Name.str (`Fixture) "", [], "266610d3f5d1e520f637b1df809212f868c034ffc6ffedd13710dfc1b268f0d1", "a1b15196e2e2d686400229fbcb4bf88daa93bc6bcf2403b21c131ab6afb1e522"),
    ("tokens", Name.str (Name.str (Name.str .anonymous "expr-node") "const") "name-ref", [], "e4f88bd090ff59f4345ce7a0f7a90b15aa05295462b1cbfd04b2e80ee1b7e7c3", "f11b68359b452f9bade3e426cdedd147f1ad9e99027222dbd19d46fc06b2f13b"),
    ("depth", (List.range 256).foldl (fun n _ => Name.str n "x") .anonymous, [], "16297bbbfa56d2f98ec0a92d30a7476570e8adbdc546adcb87bc6f2bf2429eeb", "3182e3f77cc339c34a98e119c4386a3c1894677f7897b050dfc82b70689e6bba"),
    ("universes", (`Fixture.claim), (List.range 64).map (fun i => Name.num (`u) i), "e5178923f96a6704f99a6a766f7e7ff230c29e0e42da405172ee5755954fa4fe", "3eec8cdc8605b872aff57a322cb3b96db8e11b2526b49d91fe5decfb9c5b83b7")]
  for (label, name, params, positive, negative) in cases do
    let reference := Expr.const name (List.map Level.param params)
    for (negated, expr) in #[(false, reference), (true, mkApp (mkConst ``Not) reference)] do
      match compactRawIdentity params expr with
      | .ok (identity, _) =>
        unless identity == (if (negated : Bool) then (negative : String) else positive) do
          throw <| IO.userError s!"named-reference producer mismatch: {(label : String)}:{negated}"
      | .error error => throw <| IO.userError error
