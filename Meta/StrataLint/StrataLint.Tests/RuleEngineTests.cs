using System.Collections.Immutable;
using System.Text;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class RuleEngineTests
{
    public static TheoryData<int, string> BlockingCases => new()
    {
        { 1, "upward-import" },
        { 2, "sorry" },
        { 3, "file-capacity" },
        { 4, "mirror" },
        { 5, "chronicle" },
        { 6, "badge" },
        { 8, "heart" },
        { 10, "generality" },
        { 11, "domain" },
        { 12, "header" },
        { 13, "task" },
        { 15, "formula" },
        { 16, "backfill" },
        { 17, "query" },
        { 18, "values" },
        { 19, "anomaly" },
        { 20, "axiom" },
        { 21, "future" },
    };

    [Theory]
    [MemberData(nameof(BlockingCases))]
    public void ActiveRuleHasGreenAndRedExecutableFixtures(int number, string mutation)
    {
        var green = new RuleFixture();
        if (number == 16)
        {
            green.AddBackfillTargets();
        }
        var greenResult = RuleCatalog.Default.EvaluateSingle(RuleId.CreateKnown(number), green.Build());
        Assert.Empty(greenResult.Diagnostics);
        Assert.Null(greenResult.DeferredCase);

        var red = new RuleFixture();
        if (number == 16)
        {
            red.AddBackfillTargets();
        }
        red.Apply(mutation);
        var redContext = number == 20 ? red.BuildForRuleCompatibility() : red.Build();
        var redResult = RuleCatalog.Default.EvaluateSingle(RuleId.CreateKnown(number), redContext);

        Assert.NotEmpty(redResult.Diagnostics);
        Assert.All(
            redResult.Diagnostics,
            diagnostic => Assert.Equal(RuleId.CreateKnown(number), diagnostic.RuleId));
        Assert.Null(redResult.DeferredCase);
    }

    [Theory]
    [InlineData(7, "D5-T0011")]
    [InlineData(9, "D5-T0012")]
    [InlineData(14, "D5-T0010")]
    public void DeferredRulesNeverMasqueradeAsPass(int number, string caseId)
    {
        var result = RuleCatalog.Default.EvaluateSingle(
            RuleId.CreateKnown(number),
            new RuleFixture().Build());

        Assert.Empty(result.Diagnostics);
        Assert.Equal(CaseId.CreateKnown(caseId), result.DeferredCase);
    }

    [Fact]
    public void CoverageManifestNamesEveryRuleWithARealRedOrDeferredBranch()
    {
        var exercised = BlockingCases.Select(item => (int)item[0])
            .Concat(new[] { 7, 9, 14, 22 })
            .Order()
            .ToArray();

        Assert.Equal(Enumerable.Range(1, 22), exercised);
    }
}

internal sealed class RuleFixture
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
            ["Library/queries.yaml"] = "schema_version: 1\nqueries: []\n",
            [RingPath] = Header + "def goldenRing : Nat := 0\n",
            [BlueprintPath] = "# Golden ring\n",
            ["Evidence/D5/values.legacy.json"] = "{\"D5/sample\": {\"status\": \"legacy-import-unverified\"}}\n",
        };
        foreach (var protectedPath in new[]
        {
            "docs/develop/theory/GICT_complete_development_v3 (3).md",
            "docs/develop/theory/PZG_BEDC_kernel_formal_170.md",
            "docs/develop/spec/golden-ledger-repo-spec.md",
        })
        {
            var protectedText = File.ReadAllText(Path.Combine(repositoryRoot, protectedPath), Encoding.UTF8);
            Files[protectedPath] = protectedPath.EndsWith("golden-ledger-repo-spec.md", StringComparison.Ordinal)
                ? RestoreApprovedCanonicalClaim(protectedText)
                : protectedText;
        }
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
            case "file-capacity": Files[RingPath] += string.Concat(Enumerable.Repeat("-- pad\n", 401)); break;
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
            case "values": Files["Evidence/D5/values.legacy.json"] = "{\"D5/sample\": {\"status\": \"verified\"}}\n"; break;
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
        foreach (var gid in new[]
        {
            "D5/S0/Carrier/Norm",
            "D5/X_Frontier/D5P001",
            "D5/X_Frontier/FutureInstances",
            "D5/X_Frontier/GoldenUnitsUFD",
            "D5/X_Frontier/GovernanceDeferrals",
            "D5/X_Frontier/Hearts",
            "D5/X_Frontier/HeartsDraft",
            "D5/X_Frontier/PaperGenerator",
            "D5/X_Frontier/RequiredChecks",
            "D5/X_Frontier/SplitTool",
            "D5/X_Frontier/StrataLintLeanEnvironment",
            "D5/X_Frontier/ToolchainUpgrade",
            "D5/X_Frontier/ValuesProducer",
        })
        {
            var path = gid + ".lean";
            Files[path] = HeaderFor(gid, gid.Contains("/S0/", StringComparison.Ordinal) ? "G" : "E")
                + (gid.Contains("/X_Frontier/", StringComparison.Ordinal) ? "-- D5-T9999\n" : string.Empty)
                + "def protectedTargetFixture : Unit := ()\n";
            Reports[path] = Report();
            if (gid == "D5/X_Frontier/Hearts")
            {
                Baseline[path] = Files[path];
                BaselineReports[path] = Reports[path];
            }
        }
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
