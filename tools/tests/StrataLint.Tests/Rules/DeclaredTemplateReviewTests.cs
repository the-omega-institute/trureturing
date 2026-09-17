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
    internal static Dictionary<string, string> PolicyFiles() => new(StringComparer.Ordinal)
    {
        ["lean-toolchain"] = "leanprover/lean4:v4.33.0\n",
        ["lake-manifest.json"] = "{\"packages\":[]}",
        ["lean-report-inputs.json"] = """
            {"schema_version":1,"report_semantic_version":6,
             "report_modules":{"include":[{"pattern":"D5/**/*.lean","optional":true}],"exclude":[]},
             "inspector_sources":{"include":[],"exclude":[]},
             "dependency_sources":{"include":[],"exclude":[]},
             "config_inputs":{"include":[],"exclude":[]},"producer_scopes":{}}
            """,
    };

    internal static Dictionary<string, string> Files(string seed = Seed, bool active = false)
    {
        var files = PolicyFiles();
        files[Judge] = "-- judge implementation\n";
        var engineering = System.Text.Json.Nodes.JsonNode.Parse(EngineeringRegistrationFixture.Manifest())!;
        engineering["rule_build_inputs"] = JsonSerializer.SerializeToNode(new[] { Judge });
        files[EngineeringRegistrationFixture.Path] = engineering.ToJsonString();
        files[Registration] = "import D5.S0.Carrier.Target\nimport LeanInformationAudit.Syntax\n";
        files[Target] = "-- synthetic imported theorem source\n";
        files[InformationTemplateDebtStore.ActivationPath] = Text(InformationTemplateDebtStore.WriteActivation(new(seed, active)));
        files[AdmissionPlanePolicy.FileMapPath] = "schema_version = 2\ninclude = [\"FILEMAP.inputs.toml\"]\n";
        files["Meta/FILEMAP.inputs.toml"] = "schema_version = 2\nfiles = [\n" + string.Join("\n",
            new[] { ("D5/**", "content"), (InformationTemplateDebtStore.ActivationPath, "judge"),
                ("Golden/InformationTemplateDebt/rows/*.json", "content"), ("Meta/**", "judge"), ("tools/**", "judge") }
                .Select(pair => "{ pattern = \"" + pair.Item1 + "\", admission_plane = \"" + pair.Item2
                    + "\", kind = \"data\", produced_by = \"none\", consumed_by = [\"StrataLint\"], "
                    + "verified_by = [\"StrataLint\"], artifact_id = \"none\", runtime_disposition = \"committed-source\" },"))
            + "\n]\n";
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
        bool declared = false, string? omit = null, bool indirectJudgePath = false)
    {
        var snapshot = Tree(files);
        var inputs = files.Where(p => p.Key == Registration || p.Key == Target
                || PolicyFiles().ContainsKey(p.Key))
            .Where(p => p.Key != omit).OrderBy(p => p.Key, StringComparer.Ordinal)
            .Select(p => new { path = p.Key, sha256 = Hash(p.Value) }).ToArray();
        var keys = Enumerable.Range(0, count).Select(Key).ToArray();
        var reports = new Dictionary<string, LeanFileReport>();
        foreach (var path in new[] { Registration, Target })
        {
            var own = path == Registration ? keys : [];
            var wire = JsonSerializer.SerializeToElement(new
            {
                schema_version = 1, compatibility_version = 6, inputs,
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
            string[] imports = path == Registration
                ? indirectJudgePath
                    ? ["tools.lean-inspector.LeanInformationAudit.Syntax"]
                    : [TargetModule, "LeanInformationAudit.Syntax"]
                : [];
            reports[path] = new(imports.ToImmutableArray(), declarations)
            { InformationTemplates = InformationTemplateEvidence.Read(wire, path, snapshot), InformationRegistrationErrors = [] };
        }
        if (indirectJudgePath)
            reports["tools/lean-inspector/LeanInformationAudit/Syntax.lean"] =
                new([TargetModule], []);
        var report = LeanAxiomReport.Create(reports);
        // Round-trip canonical raw bytes for every fixture, including the
        // indirect judge-import case. Admission never receives hand-attached
        // InformationTemplates in place of the strict raw artifact loader.
        return RawLeanReportArtifact.Read(RawLeanReportArtifact.Write(snapshot, report).AsSpan(), snapshot);
    }

    internal static DeltaRuleContext Context(Dictionary<string, string> baseline, Dictionary<string, string> head,
        LeanAxiomReport report, string[] changes, InformationTemplateEvidenceContext? history = null)
    {
        var prototype = new RuleFixture().Build();
        report.TemplateEvidenceContext = history;
        return DeltaRuleContext.Create(Tree(head), Tree(baseline), prototype.Policy,
            AcceptedLeanClosure.Create(report), RawChangeSet.Create(changes), prototype.MetaEvaluation);
    }

    private static ImmutableArray<Diagnostic> Dispatch(DeltaRuleContext context) =>
        RuleCatalog.Default.EvaluateSingle(UtilityAdmissionTestSupport.UtilityRuleId, context).Diagnostics;

    [Fact]
    public void same_version_changed_judge_bytes_preserve_binding_evidence()
    {
        var before = Files();
        var bytes = RawLeanReportArtifact.Write(Tree(before), Report(before));
        var after = new Dictionary<string, string>(before) { [Judge] = "-- optimized judge implementation\n" };
        var report = RawLeanReportArtifact.Read(bytes.AsSpan(), Tree(after));
        var diagnostics = Dispatch(Context(before, after, report, [Judge, InformationTemplateDebtStore.ActivationPath]));
        Assert.True(!diagnostics.Any(d => d.AdmissionEffect == AdmissionEffect.Block)
                && diagnostics.Any(d => d.Message.Contains("DTR-Inactive complete producer", StringComparison.Ordinal)),
            "[FAIL] same_version_changed_judge_bytes_preserve_binding_evidence: "
            + string.Join("; ", diagnostics.Select(d => d.Message)));
    }

    [Theory]
    [InlineData(5)]
    [InlineData(7)]
    public void mismatched_report_semantic_version_rejects_binding_evidence(int version)
    {
        var files = Files();
        var bytes = RawLeanReportArtifact.Write(Tree(files), Report(files));
        var wire = System.Text.Json.Nodes.JsonNode.Parse(bytes.AsSpan())!;
        foreach (var module in wire["modules"]!.AsArray())
            module!["information_templates"]!["compatibility_version"] = version;
        var changed = StructuredCanonicalWriter.WriteJson(wire.ToJsonString());
        var error = Record.Exception(() => RawLeanReportArtifact.Read(changed.AsSpan(), Tree(files)));
        Assert.True(error is FormatException && error.Message.Contains("DTR-Evidence", StringComparison.Ordinal),
            "[FAIL] mismatched_report_semantic_version_rejects_binding_evidence: " + version);
    }

    [Theory]
    [InlineData("lean-report-inputs.json")]
    [InlineData("lean-toolchain")]
    [InlineData("lake-manifest.json")]
    public void required_configuration_input_omission_rejected(string omitted)
    {
        var before = Files();
        var report = Report(before, omit: omitted);
        var diagnostics = Dispatch(Context(before, before, report, [InformationTemplateDebtStore.ActivationPath]));
        Assert.True(diagnostics.Any(d => d.AdmissionEffect == AdmissionEffect.Block
                && d.Message.Contains("DTR-Evidence", StringComparison.Ordinal)
                && d.Message.Contains(omitted, StringComparison.Ordinal)),
            "[FAIL] required_configuration_input_omission_rejected: " + omitted);
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

    [Fact]
    public void indirect_judge_import_closure_keeps_content_and_drops_judge_inputs()
    {
        var files = Files();
        const string syntax = "tools/lean-inspector/LeanInformationAudit/Syntax.lean";
        files[syntax] = "-- indirect judge fixture\n";
        var loaded = Report(files, indirectJudgePath: true);
        // The raw artifact is the strict reader boundary. The synthetic judge
        // module is then supplied as import metadata so this same fixture can
        // exercise the repository closure across an excluded judge module.
        var reportFiles = loaded.Files.ToDictionary(pair => pair.Key.Value, pair => pair.Value,
            StringComparer.Ordinal);
        reportFiles[syntax] = new([TargetModule], []);
        var report = LeanAxiomReport.Create(reportFiles);
        Assert.Contains(RepoPath.CreateKnown(syntax), report.Files.Keys);
        Assert.Equal("tools.lean-inspector.LeanInformationAudit.Syntax",
            Assert.Single(report.Files[RepoPath.CreateKnown(Registration)].Imports));
        var closure = LeanImportClosure.RepositoryPaths(report, RepoPath.CreateKnown(Registration));
        Assert.Contains(RepoPath.CreateKnown(Target), closure);
        Assert.Equal(1, report.Files[RepoPath.CreateKnown(Registration)].Declarations.Count(
            declaration => declaration.Name == Key(0).Theorem + ".unit"));
        var error = Record.Exception(() => InformationTemplateEvidence.Collect(Tree(files), report));
        Assert.Null(error);
        var evidence = report.Files[RepoPath.CreateKnown(Registration)].InformationTemplates!;
        Assert.Contains(evidence.Inputs, input => input.Path == Target);
        Assert.DoesNotContain(evidence.Inputs,
            input => input.Path.StartsWith("tools/lean-inspector/", StringComparison.Ordinal));
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
        var initializedRows = expected.Keys.ToDictionary(path => path,
            path => File.ReadAllBytes(Path.Combine(repository.Path, path)), StringComparer.Ordinal);
        foreach (var (path, bytes) in expected)
            Assert.True(initializedRows[path].AsSpan().SequenceEqual(Encoding.UTF8.GetBytes(bytes)),
                "[FAIL] nonempty_seed_exact_bytes: " + path);
        files[InformationTemplateDebtStore.ActivationPath] = Text(InformationTemplateDebtStore.WriteActivation(new(seed, true)));
        WriteFiles(files);
        foreach (var (path, bytes) in initializedRows)
            File.WriteAllBytes(Path.Combine(repository.Path, path), bytes);
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
