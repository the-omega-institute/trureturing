using System.Collections.Immutable;
using System.Text;
using System.Text.Json;
using StrataLint.Cli;
using StrataLint.Engine;
using Trureturing.Truth;
using static StrataLint.Tests.InformationTemplateDebtStoreTests;

namespace StrataLint.Tests;

// Wire fixtures model two imported-theorem registrations. They exercise the
// production reader, dispatch and writer; they make no kernel-proof claim.
public sealed class DeclaredTemplateReviewTests
{
    internal const string Registration = "D5/S0/Carrier/Registration.lean";
    internal const string Target = "D5/S0/Carrier/Target.lean";
    internal const string Judge = "tools/lean-inspector/LeanInformationAudit/Registry/Assessment.lean";
    private const string Module = "D5.S0.Carrier.Registration";
    private const string TargetModule = "D5.S0.Carrier.Target";
    internal static readonly string[] JudgeModules = ["RegistryTypes", "Registry", "Registry/Reifier",
        "Registry/Entries", "Registry/Evidence", "Registry/Enrollment", "Registry/Assessment",
        "ReadoutProvenance/Family", "ReadoutProvenance/State", "ReadoutProvenance/Carriers",
        "ReadoutProvenance/Types", "ReadoutProvenance", "Syntax"];

    internal static Dictionary<string, string> PolicyFiles()
    {
        var files = JudgeModules.ToDictionary(n => "tools/lean-inspector/LeanInformationAudit/" + n + ".lean",
            _ => "-- synthetic judge input\n", StringComparer.Ordinal);
        files["tools/lean-inspector/LeanInformationAudit/Syntax.lean"] =
            "import LeanInformationAudit.Registry\n";
        files["tools/lean-inspector/LeanInformationAudit/Registry.lean"] =
            "import LeanInformationAudit.Registry.Assessment\n";
        files[Judge] = "import LeanInformationAudit.ExtraPolicy\n";
        files["tools/lean-inspector/LeanInformationAudit/ExtraPolicy.lean"] = "-- transitive judge input\n";
        files["tools/lean-inspector/native_image.c"] = "/* synthetic native input */\n";
        files["lean-toolchain"] = "leanprover/lean4:v4.33.0\n";
        files["lake-manifest.json"] = "{\"packages\":[]}";
        files["lean-report-inputs.json"] = """
            {"schema_version":1,"report_semantic_version":5,
             "report_modules":{"include":[{"pattern":"D5/**/*.lean","optional":true}],"exclude":[]},
             "inspector_sources":{"include":[],"exclude":[]},
             "dependency_sources":{"include":[],"exclude":[]},
             "config_inputs":{"include":[],"exclude":[]},"producer_scopes":{}}
            """;
        return files;
    }

    internal static Dictionary<string, string> Files(string seed = Seed, bool active = false)
    {
        var files = PolicyFiles();
        files[Registration] = "import D5.S0.Carrier.Target\nimport LeanInformationAudit.Syntax\n";
        files[Target] = "-- synthetic imported theorem source\n";
        files[InformationTemplateDebtStore.ActivationPath] = Text(InformationTemplateDebtStore.WriteActivation(new(seed, active)));
        files[AdmissionPlanePolicy.FileMapPath] = File.ReadAllText(Path.Combine(TestRepositoryLayout.FindRoot(), "Meta/FILEMAP.toml"));
        return files;
    }

    internal static RepositorySnapshot Tree(Dictionary<string, string> files) =>
        Snapshot(files.Select(p => (p.Key, p.Value)).ToArray());
    internal static string Text(ImmutableArray<byte> bytes) => Encoding.UTF8.GetString(bytes.AsSpan());
    private static string Hash(string text) => InformationTemplateJson.Sha256(Encoding.UTF8.GetBytes(text));
    internal static InformationOccurrenceKey Key(int n) => new(Module, Module, TargetModule + ".target" + n,
        Module + ".arena", Module + ".catalog");
    internal static ImmutableArray<InformationTemplateContentInput> Content(Dictionary<string, string> files) =>
        [new(Registration, Hash(files[Registration])), new(Target, Hash(files[Target]))];

    internal static LeanAxiomReport Report(Dictionary<string, string> files, int count = 2,
        bool declared = false, string? omit = null)
    {
        var snapshot = Tree(files);
        var inputs = files.Where(p => p.Key.EndsWith(".lean", StringComparison.Ordinal)
                || p.Key is "lean-report-inputs.json" or "lean-toolchain" or "lake-manifest.json"
                    or "tools/lean-inspector/native_image.c")
            .Where(p => p.Key != omit).OrderBy(p => p.Key, StringComparer.Ordinal)
            .Select(p => new { path = p.Key, sha256 = Hash(p.Value) }).ToArray();
        var keys = Enumerable.Range(0, count).Select(Key).ToArray();
        var reports = new Dictionary<string, LeanFileReport>();
        foreach (var path in new[] { Registration, Target })
        {
            var own = path == Registration ? keys : [];
            var wire = JsonSerializer.SerializeToElement(new
            {
                schema_version = 1, compatibility_version = 5, inputs,
                inventory = own.Select(InformationTemplateDebtStore.KeyJson),
                registered = own.Select(InformationTemplateDebtStore.KeyJson),
                records = own.Select(key => new
                {
                    key = InformationTemplateDebtStore.KeyJson(key), registration_source_path = Registration,
                    statement_identity = Hash(key.Theorem),
                    content_inputs = Content(files).Select(i => new { path = i.Path, sha256 = i.Sha256 }),
                    binding_source_path = declared ? Registration : null,
                    state = declared ? "declared_validated" : "undeclared",
                    diagnostic = declared ? null : $"IE-C050 ClosedTruthReadout key={key.Root}/{key.Catalog}/{key.Theorem} "
                        + "reason=unclassified_form rule=dtr.missing_declaration site=\"\" readout=\"\" "
                        + "provenance={\"argument_inputs\":[],\"extraction_inputs\":[],\"plan_identity\":null,"
                        + "\"rule\":\"dtr.missing_declaration\",\"site\":\"\",\"template_key\":null}",
                    unit_name = key.Theorem + ".unit", realization_name = key.Theorem + ".realization",
                    certificate = declared ? new
                    {
                        key = InformationTemplateDebtStore.KeyJson(key), evidence_ref = Hash("evidence"),
                        plan_identity = Hash("plan"), descriptor_identity = Hash("descriptor"), actual_identity = Hash("actual"),
                        argument_inputs = Array.Empty<object>(), extraction_inputs = Array.Empty<object>(),
                    } : null,
                }),
            });
            var declarations = keys.Select(key => new LeanDeclaration(key.Theorem +
                (path == Registration ? ".unit" : ".realization"), "def", "True", [])).ToImmutableArray();
            reports[path] = new(path == Registration ? [TargetModule, "LeanInformationAudit.Syntax"] : [], declarations)
            { InformationTemplates = InformationTemplateEvidence.Read(wire, path, snapshot), InformationRegistrationErrors = [] };
        }
        var report = LeanAxiomReport.Create(reports);
        // Round-trip canonical raw bytes: admission never receives hand-attached
        // InformationTemplates in place of the strict raw artifact loader.
        return RawLeanReportArtifact.Read(RawLeanReportArtifact.Write(snapshot, report).AsSpan(), snapshot);
    }

    internal static RuleEvaluationContext Context(Dictionary<string, string> baseline, Dictionary<string, string> head,
        LeanAxiomReport report, string[] changes, InformationTemplateEvidenceContext? history = null)
    {
        var prototype = new RuleFixture().Build();
        report.TemplateEvidenceContext = history;
        return RuleEvaluationContext.Create(Tree(head), Tree(baseline), prototype.Policy,
            AcceptedLeanClosure.Create(report), RawChangeSet.Create(changes), prototype.MetaEvaluation);
    }

    private static ImmutableArray<Diagnostic> Dispatch(RuleEvaluationContext context) =>
        RuleCatalog.Default.EvaluateSingle(UtilityAdmissionTestSupport.UtilityRuleId, context).Diagnostics;

    [Theory]
    [InlineData(null)]
    [InlineData(Judge)]
    [InlineData("tools/lean-inspector/LeanInformationAudit/ExtraPolicy.lean")]
    [InlineData("tools/lean-inspector/native_image.c")]
    public void required_judge_inputs_are_independent_of_supplied_hashes(string? omitted)
    {
        var before = Files();
        var after = new Dictionary<string, string>(before);
        if (omitted is not null) after[omitted] += "-- changed after evidence production\n";
        var report = Report(after, omit: omitted);
        var diagnostics = Dispatch(Context(before, after, report, [InformationTemplateDebtStore.ActivationPath]));
        var blocks = diagnostics.Where(d => d.AdmissionEffect == AdmissionEffect.Block).ToArray();
        if (omitted is null) Assert.Empty(blocks);
        else Assert.True(blocks.Any(d => d.Message.Contains("DTR-Evidence", StringComparison.Ordinal)
                && d.Message.Contains("omitted", StringComparison.Ordinal)),
            "[FAIL] required_judge_inputs_are_independent_of_supplied_hashes: omitted " + omitted);
    }

    [Fact]
    public void empty_seed_can_activate_after_protected_inventory_reconciliation()
    {
        var before = Files();
        var after = Files(active: true);
        var reads = new List<string>();
        const string protectedRevision = "1234567890123456789012345678901234567890";
        var history = new InformationTemplateEvidenceContext(protectedRevision, revision =>
        {
            reads.Add(revision);
            return new(Tree(before), Report(before, count: 0));
        });
        var diagnostics = Dispatch(Context(before, after, Report(after, count: 0),
            [InformationTemplateDebtStore.ActivationPath], history));
        Assert.True(!diagnostics.Any(d => d.AdmissionEffect == AdmissionEffect.Block)
                && reads.SequenceEqual([Seed, protectedRevision]),
            "[FAIL] empty_seed_can_activate_after_protected_inventory_reconciliation: "
            + string.Join("; ", diagnostics.Select(d => d.Message)));
    }
    internal static Dictionary<string, string> ExpectedRows(Dictionary<string, string> files, string seed = Seed, int count = 2)
    {
        var rows = new Dictionary<string, string>(StringComparer.Ordinal);
        foreach (var key in Enumerable.Range(0, count).Select(Key))
        {
            var tuple = InformationTemplateJson.Canonical(JsonSerializer.SerializeToElement(new[]
                { key.Root, key.RegistrationModule, key.Theorem, key.ObjectArena, key.Catalog }), newline: false);
            var tupleText = Text(tuple).TrimEnd('\n');
            var path = "Golden/InformationTemplateDebt/rows/" + Hash("DTR-occurrence-v1\0" + tupleText) + ".json";
            var row = JsonSerializer.Serialize(new
            {
                schema_version = 1,
                key = new { root = key.Root, registration_module = key.RegistrationModule,
                    theorem = key.Theorem, object_arena = key.ObjectArena, catalog = key.Catalog },
                seed_base = seed, base_statement_identity = Hash(key.Theorem),
                base_registration_source_sha256 = Hash(files[Registration]),
                base_content_inputs = Content(files).Select(i => new { path = i.Path, sha256 = i.Sha256 }),
                reason = "undeclared",
            });
            rows[path] = Text(InformationTemplateJson.Canonical(JsonSerializer.Deserialize<JsonElement>(row)));
        }
        return rows;
    }

    [Theory]
    [InlineData("valid")]
    [InlineData("subset")]
    [InlineData("extra")]
    [InlineData("statement")]
    [InlineData("content")]
    [InlineData("empty-activation")]
    public void protected_seed_relation_is_checked_by_dispatch(string mutation)
    {
        var before = Files();
        var after = new Dictionary<string, string>(before);
        var rows = ExpectedRows(before);
        foreach (var pair in rows) after[pair.Key] = pair.Value;
        if (mutation == "subset") after.Remove(rows.Keys.First());
        if (mutation == "extra")
            foreach (var pair in ExpectedRows(before, count: 3)) after[pair.Key] = pair.Value;
        if (mutation is "statement" or "content")
        {
            var path = rows.Keys.First();
            var node = System.Text.Json.Nodes.JsonNode.Parse(after[path])!;
            if (mutation == "statement") node["base_statement_identity"] = new string('f', 64);
            else node["base_content_inputs"]!.AsArray().RemoveAt(1);
            after[path] = Text(InformationTemplateJson.Canonical(JsonSerializer.SerializeToElement(node)));
        }
        if (mutation == "empty-activation")
        {
            foreach (var path in rows.Keys) after.Remove(path);
            after[InformationTemplateDebtStore.ActivationPath] = Text(InformationTemplateDebtStore.WriteActivation(new(Seed, true)));
        }
        const string protectedRevision = "1234567890123456789012345678901234567890";
        var reads = new List<string>();
        var history = new InformationTemplateEvidenceContext(protectedRevision, revision =>
        {
            reads.Add(revision);
            return new(Tree(before), Report(before));
        });
        var changes = mutation == "empty-activation" ? new[] { InformationTemplateDebtStore.ActivationPath } : rows.Keys.ToArray();
        var diagnostics = Dispatch(Context(before, after, Report(after), changes, history));
        var blocks = diagnostics.Where(d => d.AdmissionEffect == AdmissionEffect.Block).ToArray();
        if (mutation == "valid") Assert.True(blocks.Length == 0 && reads.SequenceEqual([Seed, protectedRevision]),
            "[FAIL] protected_seed_valid_dispatch: " + string.Join("; ", diagnostics.Select(d => d.Message)));
        else Assert.True(blocks.Any(d => d.Message.Contains("DTR-Seed:", StringComparison.Ordinal)),
            "[FAIL] protected_seed_relation_" + mutation + ": " + string.Join("; ", diagnostics.Select(d => d.Message)));
    }

    [Fact]
    public void nonempty_source_bound_writer_publishes_exact_rows_and_deletes_discharge()
    {
        using var repository = new TemporaryDirectory();
        using var artifacts = new TemporaryDirectory();
        string Git(params string[] args) => ReviewRegressionTests.RunGit(repository.Path, args).Trim();
        void WriteFiles(Dictionary<string, string> files)
        {
            foreach (var (path, text) in files)
            {
                var full = Path.Combine(repository.Path, path);
                Directory.CreateDirectory(Path.GetDirectoryName(full)!);
                File.WriteAllText(full, text);
            }
        }
        string WriteReport(string name, Dictionary<string, string> files, bool declared = false)
        {
            var path = Path.Combine(artifacts.Path, name + ".json");
            File.WriteAllBytes(path, RawLeanReportArtifact.Write(Tree(files), Report(files, declared: declared)).AsSpan());
            return path;
        }
        Git("init");
        Git("config", "user.email", "stratalint@example.invalid");
        Git("config", "user.name", "StrataLint Tests");
        var files = Files();
        files.Remove(InformationTemplateDebtStore.ActivationPath);
        WriteFiles(files);
        Git("add", "."); Git("commit", "-m", "original occurrences");
        var seed = Git("rev-parse", "HEAD");
        files[InformationTemplateDebtStore.ActivationPath] = Text(InformationTemplateDebtStore.WriteActivation(new(seed, false)));
        WriteFiles(files);
        Git("add", "."); Git("commit", "-m", "inactive installation");
        var installed = Git("rev-parse", "HEAD");
        var gateway = new GitRepositoryGateway(repository.Path);
        var seedReport = WriteReport("seed", files);
        var initialize = InformationTemplateDebtWriter.Run(repository.Path, gateway,
            ["initialize", "--protected-base", installed, "--seed-lean-report", seedReport]);
        Assert.True(initialize.Success, initialize.Error);
        var expected = ExpectedRows(files, seed);
        var rowsDir = Path.Combine(repository.Path, InformationTemplateDebtStore.RowsRoot);
        Assert.True(Directory.Exists(rowsDir), "[FAIL] nonempty_seed_publication_required: no row directory");
        Assert.Equal(expected.Keys.Order(StringComparer.Ordinal), Directory.GetFiles(rowsDir)
            .Select(path => Path.GetRelativePath(repository.Path, path).Replace('\\', '/')).Order(StringComparer.Ordinal));
        foreach (var (path, bytes) in expected)
        {
            Assert.True(File.ReadAllText(Path.Combine(repository.Path, path)) == bytes,
                "[FAIL] nonempty_seed_exact_bytes: " + path);
            files[path] = bytes;
        }
        files[InformationTemplateDebtStore.ActivationPath] = Text(InformationTemplateDebtStore.WriteActivation(new(seed, true)));
        WriteFiles(files);
        Git("add", "."); Git("commit", "-m", "activated seeded debt");
        var baseline = Git("rev-parse", "HEAD");
        var baseReport = WriteReport("base", files);
        files[Registration] += "-- current declared binding source\n";
        WriteFiles(files);
        Git("add", "."); Git("commit", "-m", "declared bindings");
        var candidateReport = WriteReport("candidate", files, declared: true);
        var discharge = InformationTemplateDebtWriter.Run(repository.Path, gateway,
            ["discharge", "--protected-base", baseline, "--seed-lean-report", seedReport,
             "--base-lean-report", baseReport, "--candidate-lean-report", candidateReport]);
        Assert.True(discharge.Success, "[FAIL] nonempty_discharge_run: " + discharge.Error);
        Assert.True(expected.Keys.All(path => !File.Exists(Path.Combine(repository.Path, path))),
            "[FAIL] validated_discharge_deletes_published_rows");
        Assert.Equal(2, Git("status", "--porcelain").Split('\n').Count(line => line.StartsWith("D ", StringComparison.Ordinal)
            || line.StartsWith(" D ", StringComparison.Ordinal)));
    }

}
