using System.Collections.Immutable;
using System.Text;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

internal sealed partial class RuleFixture
{
    internal const string RingPath = "D5/S0/Carrier/Ring.lean";
    internal const string BlueprintPath = "Blueprint/D5/S0/Carrier/Ring.md";

    private const string Header = """
        /- GID: D5/S0/Carrier/Ring
           generality: G
           mirror-B: D5/B/S0/Carrier/Ring
           mirror-E: none(waiver:pure-definition)
           anchors: []
           digest: StrataLint fixture. -/
        """;

    internal RuleFixture()
    {
        var repositoryRoot = FindRepositoryRoot();
        Files = new Dictionary<string, string>(StringComparer.Ordinal)
        {
            ["Meta/domains.yaml"] = TestRegistry.Domains,
            ["Meta/BACKFILL.yaml"] = File.ReadAllText(Path.Combine(repositoryRoot, "Meta", "BACKFILL.yaml"), Encoding.UTF8),
            ["Meta/registry.yaml"] = TestRegistry.Canonical,
            ["Meta/StrataLint/Generated/anchor-catalog.v1.json"] = File.ReadAllText(
                Path.Combine(repositoryRoot, "Meta", "StrataLint", "Generated", "anchor-catalog.v1.json"),
                Encoding.UTF8),
            ["Library/queries.yaml"] = "schema_version: 1\nqueries: []\n",
            [RingPath] = Header + "def goldenRing : Nat := 0\n",
            [BlueprintPath] = "# Golden ring\n",
        };
        foreach (var theoryPath in new[]
        {
            "docs/develop/theory/GICT_complete_development_v3 (3).md",
            "docs/develop/theory/PZG_BEDC_kernel_formal_170.md",
        })
        {
            Files[theoryPath] = File.ReadAllText(Path.Combine(repositoryRoot, theoryPath), Encoding.UTF8);
        }

        const string specPath = "docs/develop/spec/golden-ledger-repo-spec.md";
        Files[specPath] = RestoreApprovedCanonicalClaim(
            File.ReadAllText(Path.Combine(repositoryRoot, specPath), Encoding.UTF8));
        Baseline = new Dictionary<string, string>(Files, StringComparer.Ordinal);
        Reports = new Dictionary<string, LeanFileReport>(StringComparer.Ordinal)
        {
            [RingPath] = Report(
                declarations: new[] { new LeanDeclaration("goldenRing", "def", "Nat", ImmutableArray<string>.Empty) }),
        };
        BaselineReports = new Dictionary<string, LeanFileReport>(Reports, StringComparer.Ordinal);
        Changes = new List<string> { BlueprintPath };
    }

    internal Dictionary<string, string> Files { get; }

    internal Dictionary<string, string> Baseline { get; }

    internal Dictionary<string, LeanFileReport> Reports { get; }

    internal Dictionary<string, LeanFileReport> BaselineReports { get; }

    internal List<string> Changes { get; }

    internal void Apply(string mutation)
    {
        switch (mutation)
        {
            case "upward-import": AddUpwardImport(); break;
            case "sorry": SetRingDeclaration("unfinished", "theorem", "sorryAx"); break;
            case "file-capacity": Files[RingPath] += string.Concat(Enumerable.Repeat("-- pad\n", 801)); break;
            case "mirror": Files.Remove(BlueprintPath); break;
            case "chronicle": RewriteChronicle(); break;
            case "badge": Files[BlueprintPath] = "status: proven\n"; break;
            case "heart": ChangeHeartSignature(); break;
            case "generality": AddInstanceImport(); break;
            case "domain": AddUnknownDomain(); break;
            case "header": Files[RingPath] = "def noHeader : Nat := 0\n"; break;
            case "task": AddMalformedTask(); break;
            case "formula": AddIllegalFormula(); break;
            case "backfill": Files["Meta/BACKFILL.yaml"] = Files["Meta/BACKFILL.yaml"].Replace("schema_version: 2", "schema_version: 1", StringComparison.Ordinal); break;
            case "query": Files["Library/queries.yaml"] = "schema_version: 1\nqueries:\n  - id: D5-Q0099\n    target_gid: D5/S0/Carrier/Ring\n"; break;
            case "values": Files["Evidence/D5/values.result.json"] = "{\"D5/sample\": {\"status\": \"verified\"}}\n"; break;
            case "anomaly": Files["Evidence/D5/S0/Carrier/Result.run.json"] = "{\"anomaly\": \"fixture drift\"}\n"; break;
            case "axiom": SetRingDeclaration("invented", "axiom", "invented"); break;
            case "future": AddFutureTheory(); break;
            default: throw new ArgumentOutOfRangeException(nameof(mutation));
        }
    }

    internal RuleEvaluationContext Build(ValidatedPolicy? suppliedPolicy = null)
    {
        var current = Decode(Files);
        var baseline = Decode(Baseline);
        var policy = suppliedPolicy;
        if (policy is null)
        {
            var policyOutcome = RegistryLoader.Load(
                Encoding.UTF8.GetBytes(TestRegistry.Canonical),
                Encoding.UTF8.GetBytes(TestRegistry.Domains));
            policy = Assert.IsType<RegistryLoadOutcome.Accepted>(policyOutcome).Policy;
        }
        var lean = AcceptLean(current, Reports);
        var baselineLean = AcceptLean(baseline, BaselineReports);
        var bootstrap = BootstrapGate.Evaluate(RawChangeSet.Create(Changes));
        var meta = Assert.IsType<BootstrapOutcome.Clear>(bootstrap).Capability;
        return RuleEvaluationContext.Create(
            current,
            baseline,
            policy,
            lean,
            baselineLean,
            RawChangeSet.Create(Changes),
            meta);
    }

    internal RuleEvaluationContext BuildForRuleCompatibility()
    {
        var current = Decode(Files);
        var baseline = Decode(Baseline);
        var policyOutcome = RegistryLoader.Load(
            Encoding.UTF8.GetBytes(TestRegistry.Canonical),
            Encoding.UTF8.GetBytes(TestRegistry.Domains));
        var policy = Assert.IsType<RegistryLoadOutcome.Accepted>(policyOutcome).Policy;
        var bootstrap = BootstrapGate.Evaluate(RawChangeSet.Create(Changes));
        var meta = Assert.IsType<BootstrapOutcome.Clear>(bootstrap).Capability;
        return RuleEvaluationContext.Create(
            current,
            baseline,
            policy,
            AcceptedLeanClosure.Create(LeanAxiomReport.Create(Reports)),
            AcceptedLeanClosure.Create(LeanAxiomReport.Create(BaselineReports)),
            RawChangeSet.Create(Changes),
            meta);
    }

    internal RuleEvaluationContext BuildForProtectedRuleCompatibility()
    {
        var current = Decode(Files);
        var baseline = Decode(Baseline);
        var policyOutcome = RegistryLoader.Load(
            Encoding.UTF8.GetBytes(TestRegistry.Canonical),
            Encoding.UTF8.GetBytes(TestRegistry.Domains));
        var policy = Assert.IsType<RegistryLoadOutcome.Accepted>(policyOutcome).Policy;
        var bootstrap = BootstrapGate.Evaluate(RawChangeSet.Create(Changes));
        var meta = Assert.IsType<BootstrapOutcome.HumanReviewRequired>(bootstrap).ChangeSet;
        return RuleEvaluationContext.Create(
            current,
            baseline,
            policy,
            AcceptedLeanClosure.Create(LeanAxiomReport.Create(Reports)),
            AcceptedLeanClosure.Create(LeanAxiomReport.Create(BaselineReports)),
            RawChangeSet.Create(Changes),
            MetaEvaluationProfile.ForProtectedSurface(meta));
    }

    internal void AddUpwardImport()
    {
        const string highPath = "D5/S1/Upper/High.lean";
        Files[highPath] = HeaderFor("D5/S1/Upper/High", "G") + "def high : Nat := 1\n";
        Reports[highPath] = Report(declarations: new[]
        {
            new LeanDeclaration("high", "def", "Nat", ImmutableArray<string>.Empty),
        });
        Reports[RingPath] = Report(imports: new[] { "D5.S1.Upper.High" });
    }

    internal const string AssumptionDebtPath = "D5/X_Assumptions/AxiomDebt.lean";

    // A stratum content file carrying a classical theorem via a registered
    // assumption: importing the X_Assumptions foundation is allowed (SL-001).
    internal void AddAssumptionImport()
    {
        Files[AssumptionDebtPath] = HeaderFor("D5/X_Assumptions/AxiomDebt", "G") + "axiom classicalDebt : True\n";
        Reports[AssumptionDebtPath] = Report(declarations: new[]
        {
            new LeanDeclaration("classicalDebt", "axiom", "True", ImmutableArray.Create("classicalDebt")),
        });
        Reports[RingPath] = Report(imports: new[] { "D5.X_Assumptions.AxiomDebt" });
    }

    // The X_Assumptions foundation may not import content: keeping it a sink
    // makes the import partial order acyclic (SL-001).
    internal void AddAssumptionImportingStratum()
    {
        Files[AssumptionDebtPath] = HeaderFor("D5/X_Assumptions/AxiomDebt", "G") + "axiom classicalDebt : True\n";
        Reports[AssumptionDebtPath] = Report(imports: new[] { "D5.S0.Carrier.Ring" });
    }

    internal void SetRingDeclaration(string name, string kind, string axiom)
    {
        Reports[RingPath] = Report(declarations: new[]
        {
            new LeanDeclaration(name, kind, "False", ImmutableArray.Create(axiom)),
        });
    }

    internal void RewriteChronicle()
    {
        const string path = "Chronicle/2026/07/10-old.md";
        Baseline[path] = "old\n";
        Files[path] = "changed\n";
    }

    internal void ChangeHeartSignature()
    {
        const string path = "D5/X_Frontier/Hearts.lean";
        Baseline[path] = HeaderFor("D5/X_Frontier/Hearts", "E") + "theorem heart : True := by sorry\n";
        Files[path] = HeaderFor("D5/X_Frontier/Hearts", "E") + "theorem heart : False := by sorry\n";
        BaselineReports[path] = Report(declarations: new[]
        {
            new LeanDeclaration("heart", "theorem", "True", ImmutableArray.Create("sorryAx")),
        });
        Reports[path] = Report(declarations: new[]
        {
            new LeanDeclaration("heart", "theorem", "False", ImmutableArray.Create("sorryAx")),
        });
    }

    internal void AddInstanceImport()
    {
        const string path = "D5/S0/Conventions/Notation.lean";
        Files[path] = HeaderFor("D5/S0/Conventions/Notation", "I") + "def instanceFact : Nat := 1\n";
        Reports[path] = Report(declarations: new[]
        {
            new LeanDeclaration("instanceFact", "def", "Nat", ImmutableArray<string>.Empty),
        });
        Reports[RingPath] = Report(imports: new[] { "D5.S0.Conventions.Notation" });
    }

    internal void AddUnknownDomain()
    {
        const string path = "D5/S0/Unknown/Bad.lean";
        Files[path] = HeaderFor("D5/S0/Unknown/Bad", "G") + "def bad : Nat := 0\n";
        Reports[path] = Report();
    }

    internal void AddMalformedTask()
    {
        const string path = "D5/X_Frontier/BadTask.lean";
        Files[path] = HeaderFor("D5/X_Frontier/BadTask", "E")
            + "/-- TASK D5-T0010 | broken -/\ndef badTask : Unit := ()\n";
        Reports[path] = Report();
    }

    internal void AddIllegalFormula() =>
        Files["Evidence/D5/S0/Carrier/Formula.check.json"] = "{\"formula\": \"sqrt@5\", \"refs\": {}}\n";

    internal void AddFutureTheory() =>
        Files["D8/S0/Carrier/Ring.lean"] = "future\n";

    internal void AddTask(string path, string gid, string code)
    {
        Files[path] = HeaderFor(gid, "E")
            + $"/-- TASK {code} | 难度:3 | 依赖:就绪 | 尝试:0\n"
            + "    提示:Fixture task.\n"
            + "    尸检:none -/\n"
            + "def fixtureTask : Unit := ()\n";
        Reports[path] = Report();
    }

    internal void AddBackfillTargets()
    {
        var inventory = BackfillInventoryLoader.Load(Files["Meta/BACKFILL.yaml"]);
        var ticketsByGid = inventory.RequireTickets()
            .GroupBy(static ticket => ticket.Gid, StringComparer.Ordinal)
            .ToDictionary(
                static group => group.Key,
                static group => group.Select(static ticket => ticket.CaseId).ToArray(),
                StringComparer.Ordinal);
        foreach (var gidText in inventory.RequireReferencedGids())
        {
            if (!Gid.TryParse(gidText, out var gid))
            {
                throw new FormatException($"canonical BACKFILL contains invalid GID {gidText}");
            }

            var path = gid.Path.Value;
            if (!path.EndsWith(".lean", StringComparison.Ordinal))
            {
                if (path == ValuesProjectionLoader.RelativePath)
                {
                    var repositoryRoot = FindRepositoryRoot();
                    Files[path] = File.ReadAllText(Path.Combine(repositoryRoot, path), Encoding.UTF8);
                    foreach (var inputPath in new[]
                    {
                        ValuesProjectionLoader.InputPath,
                        "Directory.Build.props",
                        "Directory.Packages.props",
                        "Meta/StrataLint/StrataLint.Scribe/packages.lock.json",
                        "global.json",
                    })
                    {
                        Files[inputPath] = File.ReadAllText(
                            Path.Combine(repositoryRoot, inputPath),
                            Encoding.UTF8);
                    }

                    Reports[ValuesProjectionLoader.InputPath] = Report(declarations: new[]
                    {
                        new LeanDeclaration(
                            "valuesProducerTicket",
                            "def",
                            "Unit",
                            ImmutableArray<string>.Empty),
                    });
                }

                continue;
            }

            if (!Files.TryGetValue(path, out var text))
            {
                text = HeaderFor(gidText, path.Contains("/S0/", StringComparison.Ordinal) ? "G" : "E")
                    + (path.Contains("/X_Frontier/", StringComparison.Ordinal) ? "-- D5-T9999\n" : string.Empty)
                    + "def protectedTargetFixture : Unit := ()\n";
                Reports[path] = Report();
            }

            if (ticketsByGid.TryGetValue(gidText, out var cases))
            {
                text += string.Concat(cases.Where(caseId =>
                        !text.Contains($"TASK {caseId} ", StringComparison.Ordinal))
                    .Select(static caseId =>
                    $"/-- TASK {caseId} | 难度:3 | 依赖:就绪 | 尝试:0\n"
                    + "    提示:Fixture task.\n"
                    + "    尸检:none -/\n"
                    + $"def fixtureTask{caseId[4..]} : Unit := ()\n"));
            }

            Files[path] = text;
            if (path == "D5/X_Frontier/Hearts.lean")
            {
                Baseline[path] = text;
                BaselineReports[path] = Reports[path];
            }
        }
    }

    internal void AddNormalizedBackfillTicketTarget()
    {
        const string gid = "D5/X_Frontier/BackfillTasks";
        var path = gid + ".lean";
        Files[path] = HeaderFor(gid, "E")
            + string.Concat(Enumerable.Range(1, 18).Select(static number =>
                $"/-- TASK D5-T{number:0000} | 难度:3 | 依赖:就绪 | 尝试:0\n"
                + "    提示:Fixture task.\n"
                + "    尸检:none -/\n"
                + $"def fixtureTask{number:0000} : Unit := ()\n"));
        Reports[path] = Report();
    }

    private static RepositorySnapshot Decode(IReadOnlyDictionary<string, string> files)
    {
        var raw = RawRepositorySnapshot.Create(files.Select(pair => RawRepositoryEntry.FromText(pair.Key, pair.Value)));
        return Assert.IsType<SnapshotDecodeOutcome.Decoded>(SnapshotDecoder.Decode(raw)).Snapshot;
    }

    private static AcceptedLeanClosure AcceptLean(
        RepositorySnapshot snapshot,
        IReadOnlyDictionary<string, LeanFileReport> reports)
    {
        var report = LeanAxiomReport.Create(reports);
        var outcome = LeanClosureValidator.Validate(snapshot, report);
        return Assert.IsType<LeanValidationOutcome.Accepted>(outcome).Capability;
    }

    private static LeanFileReport Report(
        IEnumerable<string>? imports = null,
        IEnumerable<LeanDeclaration>? declarations = null) =>
        new(
            (imports ?? Array.Empty<string>()).ToImmutableArray(),
            (declarations ?? Array.Empty<LeanDeclaration>()).ToImmutableArray());

    private static string HeaderFor(string gid, string generality) => $"""
        /- GID: {gid}
           generality: {generality}
           mirror-B: none(waiver:test-fixture)
           mirror-E: none(waiver:test-fixture)
           anchors: []
           digest: StrataLint fixture. -/
        """;

    private static string RestoreApprovedCanonicalClaim(string text)
    {
        const string marker = "**papergen/blueprint 只接受全 GID;跨库引用自带理论坐标。**";
        const string approved = " **M0 admission 精确主张**:给定一个受支持且经人类门控核准的语义 manifest,至多存在一种规范表示与恰一次 admission;不受支持或未核准的 manifest 按 fail-closed 得零次 admission。受 manifest 路由的 JSON/YAML 结构化语义工件现役强制 UTF-8、禁 BOM、对象键字典序、禁行尾空白且末尾恰一 LF;完整 Unicode NFC、默认值与 tag 顺序规范化延后 D5-T0015,故字节规范不得报 full active。";
        if (text.Contains(approved, StringComparison.Ordinal))
        {
            return text;
        }

        if (!text.Contains(marker, StringComparison.Ordinal))
        {
            throw new InvalidOperationException("protected spec fixture lacks the approved canonical-claim anchor");
        }

        return text.Replace(marker, marker + approved, StringComparison.Ordinal);
    }

    private static string FindRepositoryRoot()
    {
        var directory = new DirectoryInfo(AppContext.BaseDirectory);
        while (directory is not null)
        {
            if (File.Exists(Path.Combine(directory.FullName, "Meta", "BACKFILL.yaml")))
            {
                return directory.FullName;
            }

            directory = directory.Parent;
        }

        throw new DirectoryNotFoundException("could not locate repository root for protected fixtures");
    }
}
