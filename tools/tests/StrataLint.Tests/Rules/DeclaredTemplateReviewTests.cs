using System.Collections.Immutable;
using System.Text;
using System.Text.Json;
using StrataLint.Engine;
using Trureturing.Truth;

namespace StrataLint.Tests;

// Wire fixtures model two imported-theorem registrations. They exercise the
// production reader and dispatch; they make no kernel-proof claim.
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
            {"schema_version":1,"report_semantic_version":8,
             "report_modules":{"include":[{"pattern":"D5/**/*.lean","optional":true}],"exclude":[]},
             "inspector_sources":{"include":[],"exclude":[]},
             "dependency_sources":{"include":[],"exclude":[]},
             "config_inputs":{"include":[],"exclude":[]},"producer_scopes":{}}
            """,
    };

    internal static int ManifestVersion(Dictionary<string, string> files)
    {
        using var manifest = JsonDocument.Parse(files["lean-report-inputs.json"]);
        return manifest.RootElement.GetProperty("report_semantic_version").GetInt32();
    }

    internal static Dictionary<string, string> Files()
    {
        var files = PolicyFiles();
        files[Judge] = "-- judge implementation\n";
        var engineering = System.Text.Json.Nodes.JsonNode.Parse(EngineeringRegistrationFixture.Manifest())!;
        engineering["rule_build_inputs"] = JsonSerializer.SerializeToNode(new[] { Judge });
        files[EngineeringRegistrationFixture.Path] = engineering.ToJsonString();
        files[Registration] = "import D5.S0.Carrier.Target\nimport LeanInformationAudit.Syntax\n";
        files[Target] = "-- synthetic imported theorem source\n";
        files[AdmissionPlanePolicy.FileMapPath] = "schema_version = 2\ninclude = [\"FILEMAP.inputs.toml\"]\n";
        files["Meta/FILEMAP.inputs.toml"] = "schema_version = 2\nfiles = [\n" + string.Join("\n",
            new[] { ("D5/**", "content"), ("Meta/**", "judge"), ("tools/**", "judge") }
                .Select(pair => "{ pattern = \"" + pair.Item1 + "\", admission_plane = \"" + pair.Item2
                    + "\", kind = \"data\", produced_by = \"none\", consumed_by = [\"StrataLint\"], "
                    + "verified_by = [\"StrataLint\"], artifact_id = \"none\", runtime_disposition = \"committed-source\" },"))
            + "\n]\n";
        return files;
    }

    internal static RepositorySnapshot Tree(Dictionary<string, string> files) =>
        Assert.IsType<SnapshotDecodeOutcome.Decoded>(SnapshotDecoder.Decode(
            RawRepositorySnapshot.Create(files.Select(p => RawRepositoryEntry.FromText(p.Key, p.Value))))).Snapshot;
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
                schema_version = 1, compatibility_version = ManifestVersion(files), inputs,
                inventory = own.Select(InformationTemplateJson.KeyJson),
                registered = own.Select(InformationTemplateJson.KeyJson),
                records = own.Select(key => new
                {
                    key = InformationTemplateJson.KeyJson(key), registration_source_path = Registration,
                    statement_identity = Hash(key.Theorem),
                    content_inputs = Content(files).Select(i => new { path = i.Path, sha256 = i.Sha256 }),
                    binding_source_path = declared ? Registration : null,
                    state = declared ? "declared_validated" : "undeclared",
                    diagnostic = declared ? null : $"IE-C050 ClosedTruthReadout key={key.Root}/{key.Catalog}/{key.Theorem} "
                        + "reason=unclassified_form rule=dtr.missing_declaration site=\"\" readout=\"\" "
                        + "provenance={\"argument_inputs\":[],\"extraction_inputs\":[],\"plan_identity\":null,"
                        + "\"rule\":\"dtr.missing_declaration\",\"site\":\"\",\"template_key\":null}",
                    escape_from = DeclaredTemplateEscapeRecordTests.FromSlot,
                    escape_continues = DeclaredTemplateEscapeRecordTests.OpenSlot, bridge_kind = "legacy",
                    unit_name = key.Theorem + ".unit", realization_name = key.Theorem + ".realization",
                    certificate = declared ? new
                    {
                        key = InformationTemplateJson.KeyJson(key), evidence_ref = Hash("evidence"),
                        plan_identity = Hash("plan"), descriptor_identity = Hash("descriptor"), actual_identity = Hash("actual"),
                        argument_inputs = Array.Empty<object>(), extraction_inputs = Array.Empty<object>(),
                    } : null,
                }),
            });
            var declarations = keys.Select(key => new LeanDeclaration(key.Theorem +
                (path == Registration ? ".unit" : ".realization"), "def", "True", [])).ToImmutableArray();
            string[] imports = path == Registration
                ? indirectJudgePath
                    ? ["LeanInformationAudit.Syntax"]
                    : [TargetModule, "LeanInformationAudit.Syntax"]
                : [];
            reports[path] = new(imports.ToImmutableArray(), declarations)
            { InformationTemplates = wire, InformationRegistrationErrors = [] };
        }
        if (indirectJudgePath)
            reports["tools/lean-inspector/LeanInformationAudit/Syntax.lean"] =
                new([TargetModule], []);
        var report = LeanAxiomReport.Create(reports);
        // Round-trip canonical raw bytes for every fixture, including the
        // indirect judge-import case. Admission never receives hand-attached
        // InformationTemplates in place of the production raw artifact loader.
        return RawLeanReportArtifact.Read(RawLeanReportArtifact.Write(snapshot, report).AsSpan(), snapshot);
    }

    internal static DeltaRuleContext Context(Dictionary<string, string> baseline, Dictionary<string, string> head,
        LeanAxiomReport report, string[] changes)
    {
        var prototype = new RuleFixture().Build();
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
        var diagnostics = Dispatch(Context(before, after, report, [Judge]));
        Assert.True(!diagnostics.Any(d => d.AdmissionEffect == AdmissionEffect.Block)
                && !diagnostics.Any(d => d.Message.StartsWith("DTR-", StringComparison.Ordinal)),
            "[FAIL] same_version_changed_judge_bytes_preserve_binding_evidence: "
            + string.Join("; ", diagnostics.Select(d => d.Message)));
    }

    [Fact]
    public void manifest_only_bump_accepts_eight()
    {
        var files = Files();
        var error = Record.Exception(() =>
        {
            var bytes = RawLeanReportArtifact.Write(Tree(files), Report(files));
            Assert.Equal(2, RawLeanReportArtifact.Read(bytes.AsSpan(), Tree(files)).Files.Count);
        });
        Assert.True(error is null, "[FAIL] manifest_only_bump_accepts_eight: " + error?.Message);
    }

    private static Exception? ReadChangedManifest(string? manifest, int compatibility)
    {
        var files = Files();
        var wire = System.Text.Json.Nodes.JsonNode.Parse(RawLeanReportArtifact.Write(Tree(files), Report(files)).AsSpan())!;
        if (manifest is null) files.Remove("lean-report-inputs.json");
        else files["lean-report-inputs.json"] = manifest;
        foreach (var module in wire["modules"]!.AsArray())
        {
            var evidence = module!["information_templates"]!;
            evidence["compatibility_version"] = compatibility;
            // Keep source binding current so only version validation can reject.
            foreach (var input in evidence["inputs"]!.AsArray())
                if (manifest is not null && input!["path"]!.GetValue<string>() == "lean-report-inputs.json")
                    input["sha256"] = Hash(manifest);
        }
        var bytes = StructuredCanonicalWriter.WriteJson(wire.ToJsonString());
        var snapshot = Tree(files);
        return Record.Exception(() => InformationTemplateEvidence.Collect(snapshot,
            RawLeanReportArtifact.Read(bytes.AsSpan(), snapshot), [RepoPath.CreateKnown(Registration)]));
    }

    [Theory]
    [InlineData(null)]
    [InlineData("null")]
    [InlineData("true")]
    [InlineData("\"7\"")]
    [InlineData("0")]
    [InlineData("-1")]
    [InlineData("7.0")]
    [InlineData("7.5")]
    public void invalid_evidence_version_uses_named_diagnostic(string? version)
    {
        var files = Files();
        var wire = System.Text.Json.Nodes.JsonNode.Parse(RawLeanReportArtifact.Write(Tree(files), Report(files)).AsSpan())!;
        foreach (var module in wire["modules"]!.AsArray())
        {
            var evidence = module!["information_templates"]!.AsObject();
            if (version is null) evidence.Remove("compatibility_version");
            else evidence["compatibility_version"] = System.Text.Json.Nodes.JsonNode.Parse(version);
            // Preserve the version token: the canonical writer normalizes 7.0 to 7.
            using var document = JsonDocument.Parse(evidence.ToJsonString());
            if (version is not null)
                Assert.Equal(version, document.RootElement.GetProperty("compatibility_version").GetRawText());
            var error = Record.Exception(() => InformationTemplateEvidence.Read(document.RootElement,
                module["source_path"]!.GetValue<string>(), Tree(files)));
            Assert.True(error is FormatException && error.Message.StartsWith("DTR-EvidenceVersion:", StringComparison.Ordinal),
                "[FAIL] invalid_evidence_version_uses_named_diagnostic: " + error?.Message);
        }
    }

    [Fact]
    public void bumped_manifest_rejects_seven()
    {
        var manifest = PolicyFiles()["lean-report-inputs.json"];
        var error = ReadChangedManifest(manifest, 7);
        Assert.True(error is FormatException && error.Message.Contains("DTR-EvidenceVersion", StringComparison.Ordinal),
            "[FAIL] bumped_manifest_rejects_seven: " + error?.Message);
    }

    [Theory]
    [InlineData(null)]
    [InlineData("{}")]
    [InlineData("{")]
    [InlineData("[]")]
    [InlineData("{\"report_semantic_version\":null}")]
    [InlineData("{\"report_semantic_version\":\"8\"}")]
    [InlineData("{\"report_semantic_version\":true}")]
    [InlineData("{\"report_semantic_version\":0}")]
    [InlineData("{\"report_semantic_version\":-1}")]
    [InlineData("{\"report_semantic_version\":6.5}")]
    public void invalid_manifest_version_rejected(string? manifest)
    {
        var error = ReadChangedManifest(manifest, 7);
        Assert.True(error is FormatException && error.Message.Contains("DTR-ManifestVersion", StringComparison.Ordinal),
            "[FAIL] invalid_manifest_version_rejected: " + error?.Message);
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
        var snapshot = Tree(files);
        var error = Record.Exception(() => InformationTemplateEvidence.Collect(snapshot,
            RawLeanReportArtifact.Read(changed.AsSpan(), snapshot), [RepoPath.CreateKnown(Registration)]));
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
        var after = new Dictionary<string, string>(before) { [Registration] = before[Registration] + "-- changed\n" };
        var report = Report(after, omit: omitted);
        var diagnostics = Dispatch(Context(before, after, report, [Registration]));
        Assert.True(diagnostics.Any(d => d.AdmissionEffect == AdmissionEffect.Observe
                && d.Message.Contains("DTR-Evidence", StringComparison.Ordinal)
                && d.Message.Contains(omitted, StringComparison.Ordinal)),
            "[FAIL] required_configuration_input_omission_rejected: " + omitted);
    }

    [Fact]
    public void actual_inline_proof_helper_input_omission_rejected()
    {
        const string prefix = "tools/lean-inspector/LeanInformationAudit/Tests/RegistrationGates/";
        const string registration = prefix + "InlineRealization.lean";
        const string source = prefix + "InlineRealizationSource.lean";
        const string helper = prefix + "InlineProofHelper.lean";
        var root = TestRepositoryLayout.FindRoot();
        // Engineering restores only a seed, not this fixture's compiled imports.
        // Lake owns the prerequisite closure; the canonical runner owns cache
        // provisioning and locking. Do not build the whole inspector test library.
        var build = TestProcessRunner.Run("make",
            ["lean", "LEAN_TARGETS=LeanInformationAudit.Tests.RegistrationGates.InlineRealizationSource "
                + "LeanInformationAudit.Tests.RegistrationGates.Positive LeanInformationAudit.Tests.SourceIsolation"],
            root, TestBudgets.ReportSupervisorHangGuard, 2 * 1024 * 1024);
        Assert.True(build.ExitCode == 0, Encoding.UTF8.GetString(build.StandardOutput)
            + Encoding.UTF8.GetString(build.StandardError));
        var process = TestProcessRunner.Run("/bin/bash",
            [Path.Combine(root, "tools/scripts/worktree/lean-cache-run.sh"),
                "lake", "env", "lean", "--root=tools/lean-inspector", Path.Combine(root, registration)],
            root, TestBudgets.LeanProcessHangGuard, 2 * 1024 * 1024);
        var output = Encoding.UTF8.GetString(process.StandardOutput)
            + Encoding.UTF8.GetString(process.StandardError);
        Assert.True(process.ExitCode == 0, output);
        const string marker = "INLINE_PROVENANCE_REPORT=";
        var start = output.IndexOf(marker, StringComparison.Ordinal);
        Assert.True(start >= 0, output);
        start += marker.Length;
        var end = output.IndexOf('\n', start);
        var wire = System.Text.Json.Nodes.JsonNode.Parse(output[start..(end < 0 ? output.Length : end)])!;
        var inputs = wire["inputs"]!.AsArray();
        Assert.Contains(inputs, input => input!["path"]!.GetValue<string>() == helper);

        var entries = inputs.Select(input =>
        {
            var path = input!["path"]!.GetValue<string>();
            return new RawRepositoryEntry(path,
                ImmutableArray.CreateRange(File.ReadAllBytes(Path.Combine(root, path))));
        });
        var snapshot = Assert.IsType<SnapshotDecodeOutcome.Decoded>(SnapshotDecoder.Decode(
            RawRepositorySnapshot.Create(entries))).Snapshot;
        var declarations = wire["records"]!.AsArray().SelectMany(record => new[]
        {
            new LeanDeclaration(record!["unit_name"]!.GetValue<string>(), "def", "True", []),
            new LeanDeclaration(record["realization_name"]!.GetValue<string>(), "theorem", "True", []),
        }).DistinctBy(declaration => declaration.Name).ToImmutableArray();
        LeanAxiomReport WithWire(System.Text.Json.Nodes.JsonNode evidence) =>
            LeanAxiomReport.Create(new Dictionary<string, LeanFileReport>
            {
                [registration] = new(["LeanInformationAudit.Tests.RegistrationGates.InlineRealizationSource"], declarations)
                { InformationTemplates = JsonSerializer.SerializeToElement(evidence) },
                [source] = new(["LeanInformationAudit.Tests.RegistrationGates.InlineProofHelper"], []),
                [helper] = new([], []),
            });
        var selected = new[] { RepoPath.CreateKnown(registration) };
        Assert.Null(Record.Exception(() => InformationTemplateEvidence.Collect(
            snapshot, WithWire(wire), selected)));

        var omitted = wire.DeepClone();
        var omittedInputs = omitted["inputs"]!.AsArray();
        omittedInputs.RemoveAt(omittedInputs.ToList().FindIndex(input =>
            input!["path"]!.GetValue<string>() == helper));
        var error = Assert.Throws<FormatException>(() => InformationTemplateEvidence.Collect(
            snapshot, WithWire(omitted), selected));
        Assert.Contains("omitted required producer/source input " + helper, error.Message,
            StringComparison.Ordinal);
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
        Assert.Equal("LeanInformationAudit.Syntax",
            Assert.Single(report.Files[RepoPath.CreateKnown(Registration)].Imports));
        var closure = LeanImportClosure.RepositoryPaths(report, RepoPath.CreateKnown(Registration));
        Assert.Contains(RepoPath.CreateKnown(Target), closure);
        Assert.Equal(1, report.Files[RepoPath.CreateKnown(Registration)].Declarations.Count(
            declaration => declaration.Name == Key(0).Theorem + ".unit"));
        var error = Record.Exception(() => InformationTemplateEvidence.Collect(Tree(files), report,
            new[] { RepoPath.CreateKnown(Registration) }));
        Assert.Null(error);
        var evidence = InformationTemplateEvidence.Read(
            report.Files[RepoPath.CreateKnown(Registration)].InformationTemplates!.Value, Registration, Tree(files));
        Assert.Contains(evidence.Inputs, input => input.Path == Target);
        Assert.DoesNotContain(evidence.Inputs,
            input => input.Path.StartsWith("tools/lean-inspector/", StringComparison.Ordinal));
    }
}
