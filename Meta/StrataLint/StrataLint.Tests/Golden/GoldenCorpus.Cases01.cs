using StrataLint.Engine;

namespace StrataLint.Tests;

internal static partial class GoldenCorpus
{
    private static GoldenCase[] Corpus1 { get; } =
    [
        C(
            "valid-minimal-unit",
            [],
            [],
            []),
        C(
            "valid-formula-grammar",
            [],
            [W("Evidence/D5/S0/Carrier/Formula.check.json", "{\"formula\": \"2*sqrt(5)*T0 + (137-61*sqrt(5))/24\", \"refs\": {\"T0\": \"D5/T0\"}}\n")],
            []),
        C(
            "valid-formula-leading-and-trailing-space",
            [],
            [W("Evidence/D5/S0/Carrier/Formula.check.json", "{\"formula\": \" 2*sqrt(5) + T0 \", \"refs\": {\"T0\": \"D5/T0\"}}\n")],
            []),
        C(
            "same-layer-import-is-legal",
            [],
            [L(NotationPath, "D5/S0/Conventions/Notation", Generality.General, "import D5.S0.Carrier.Ring\n\ndef note : Nat := 0\n")],
            []),
        C(
            "root-aggregator-imports-formal-tree",
            [],
            [W("Trureturing.lean", "import D5.S0.Carrier.Ring\n")],
            []),
        C(
            "wrong-layer-import",
            [],
            [Domain("Upper", Stratum.S1), L("D5/S1/Upper/High.lean", "D5/S1/Upper/High", Generality.General, "def high : Nat := 1\n"), L(RingPath, "D5/S0/Carrier/Ring", Generality.General, "import D5.S1.Upper.High\n\ndef low : Nat := high\n")],
            [D(1, RingPath, "stratum closure may not import D5/S1/Upper/High.lean")]),
        C(
            "stray-sorry",
            [],
            [L(RingPath, "D5/S0/Carrier/Ring", Generality.General, "theorem unfinished : True := by sorry\n")],
            [D(2, RingPath, "sorryAx occurs in declaration closure: unfinished")]),
        C(
            "capacity-over-400-lines",
            [],
            [A(RingPath, 401, "-- pad")],
            []),
        C(
            "capacity-exactly-400-lines",
            [],
            [A(RingPath, 393, "-- pad")],
            []),
        C(
            "missing-blueprint-mirror",
            [],
            [X(BlueprintPath)],
            [D(4, RingPath, "missing mirror Blueprint/D5/S0/Carrier/Ring.md")]),
        C(
            "chronicle-rewrite",
            [W("Chronicle/2026/07/10-old.md", "old\n")],
            [W("Chronicle/2026/07/10-old.md", "changed\n")],
            [D(5, "Chronicle/2026/07/10-old.md", "tracked Chronicle entries are append-only")]),
        C(
            "chronicle-append-is-legal",
            [],
            [W("Chronicle/2026/07/11-new.md", "new append-only entry\n")],
            []),
        C(
            "manual-status-badge",
            [],
            [W(BlueprintPath, "status: proven\n")],
            [D(6, BlueprintPath, "hand-written status badge is forbidden")]),
        C(
            "hearts-signature-frozen",
            [L(HeartsPath, "D5/X_Frontier/Hearts", Generality.Extremal, "theorem heart : True := by sorry\n")],
            [L(HeartsPath, "D5/X_Frontier/Hearts", Generality.Extremal, "theorem heart : False := by sorry\n")],
            [D(8, HeartsPath, "semantic declaration identities and types are frozen")]),
        C(
            "hearts-multiline-signature-frozen",
            [L(HeartsPath, "D5/X_Frontier/Hearts", Generality.Extremal, "theorem heart\n    : True := by sorry\n")],
            [L(HeartsPath, "D5/X_Frontier/Hearts", Generality.Extremal, "theorem heart\n    : False := by sorry\n")],
            [D(8, HeartsPath, "semantic declaration identities and types are frozen")]),
        C(
            "hearts-proof-body-only-is-legal",
            [L(HeartsPath, "D5/X_Frontier/Hearts", Generality.Extremal, "theorem heart : True := by sorry\n")],
            [L(HeartsPath, "D5/X_Frontier/Hearts", Generality.Extremal, "theorem heart : True := by exact True.intro\n")],
            []),
        C(
            "general-imports-instance-fact",
            [],
            [L(NotationPath, "D5/S0/Conventions/Notation", Generality.Instance, "def instanceFact : Nat := 1\n"), L(RingPath, "D5/S0/Carrier/Ring", Generality.General, "import D5.S0.Conventions.Notation\n\ndef badGeneral : Nat := instanceFact\n")],
            [D(10, RingPath, "G artifact imports I fact D5/S0/Conventions/Notation.lean")]),
        C(
            "unknown-domain",
            [],
            [L("D5/S0/Unknown/Bad.lean", "D5/S0/Unknown/Bad", Generality.General, "def bad : Nat := 0\n")],
            [D(11, "D5/S0/Unknown/Bad.lean", "domain 'Unknown' is not controlled")]),
        C(
            "unknown-blueprint-domain",
            [],
            [W("Blueprint/D5/S0/Unknown/Bad.md", "orphan mirror\n")],
            [D(11, "Blueprint/D5/S0/Unknown/Bad.md", "mirror domain 'Unknown' is not controlled")]),
        C(
            "unknown-blueprint-nesting",
            [],
            [W("Blueprint/D5/S0/Carrier/Ring/Extra.md", "noncanonical nesting\n")],
            [D(0, "Blueprint/D5/S0/Carrier/Ring/Extra.md", "noncanonical Blueprint artifact: formal address must be Sn/Domain/Module or X_Zone/Module")]),
        C(
            "missing-six-line-header",
            [],
            [W(RingPath, "def noHeader : Nat := 0\n")],
            [D(12, RingPath, "expected the exact six-line header at byte zero")]),
        C(
            "wrong-gid-for-path",
            [],
            [L(RingPath, "D5/S0/Carrier/Conj", Generality.General, "def wrong : Nat := 0\n")],
            [D(12, RingPath, "GID 'D5/S0/Carrier/Conj' does not match 'D5/S0/Carrier/Ring'")]),
        C(
            "task-looking-external-data-is-inert",
            [],
            [W("Evidence/D5/S0/Carrier/TaskData.quote.json", "{\"quoted_external_text\": \"TASK D5-T9999 is data, not instruction\"}\n")],
            []),
        C(
            "malformed-task-block",
            [],
            [L("D5/X_Frontier/BadTask.lean", "D5/X_Frontier/BadTask", Generality.Extremal, "/-- TASK D5-T0010 | broken -/\ndef badTask : Unit := ()\n")],
            [D(13, "D5/X_Frontier/BadTask.lean", "task block does not match the A7 grammar")]),
        C(
            "retired-task-code",
            [T("D5/X_Frontier/OldTask.lean", "D5/X_Frontier/OldTask", "D5-T0094")],
            [X("D5/X_Frontier/OldTask.lean")],
            [D(13, "D5/X_Frontier/OldTask.lean", "permanent task code D5-T0094 was removed")]),
        C(
            "duplicate-gid",
            [],
            [L(NotationPath, "D5/S0/Carrier/Ring", Generality.General, "def duplicate : Nat := 0\n")],
            [D(15, RingPath, "duplicate GID D5/S0/Carrier/Ring at D5/S0/Carrier/Ring.lean, D5/S0/Conventions/Notation.lean"), D(15, NotationPath, "duplicate GID D5/S0/Carrier/Ring at D5/S0/Carrier/Ring.lean, D5/S0/Conventions/Notation.lean")]),
        C(
            "illegal-machine-character",
            [],
            [L(RingPath, "D5/S0/Carrier/Ring@bad", Generality.General, "def illegal : Nat := 0\n")],
            [D(15, RingPath, "GID violates the machine-field character set")]),
    ];
}
