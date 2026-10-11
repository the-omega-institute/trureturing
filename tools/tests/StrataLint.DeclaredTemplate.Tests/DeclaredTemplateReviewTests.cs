using static StrataLint.TestSupport.DeclaredTemplateFixture;
using static StrataLint.TestSupport.InformationTemplateFixture;
using System.Collections.Immutable;
using System.Text;
using System.Text.Json;
using StrataLint.Engine;
using Trureturing.Truth;

namespace StrataLint.DeclaredTemplate.Tests;

// Wire fixtures model two imported-theorem registrations. They exercise the
// production reader and dispatch; they make no kernel-proof claim.
public sealed class DeclaredTemplateReviewTests
{
    private static ImmutableArray<Diagnostic> Dispatch(DeltaRuleContext context) =>
        RuleCatalog.Default.EvaluateSingle(UtilityAdmissionTestSupport.UtilityRuleId, context).Diagnostics;

    [Fact]
    public void changed_judge_bytes_preserve_binding_evidence()
    {
        var before = Files();
        var bytes = RawLeanReportArtifact.Write(Tree(before), Report(before));
        var after = new Dictionary<string, string>(before) { [Judge] = "-- optimized judge implementation\n" };
        var report = RawLeanReportArtifact.Read(bytes.AsSpan(), Tree(after));
        var diagnostics = Dispatch(Context(before, after, report, [Judge]));
        Assert.True(!diagnostics.Any(d => d.AdmissionEffect == AdmissionEffect.Block)
                && !diagnostics.Any(d => d.Message.StartsWith("DTR-", StringComparison.Ordinal)),
            "[FAIL] changed_judge_bytes_preserve_binding_evidence: "
            + string.Join("; ", diagnostics.Select(d => d.Message)));
    }

    [Fact]
    public void binding_evidence_needs_no_semantic_manifest()
    {
        var files = Files();
        var error = Record.Exception(() =>
        {
            var bytes = RawLeanReportArtifact.Write(Tree(files), Report(files));
            files.Remove("lean-report-inputs.json");
            Assert.Equal(2, RawLeanReportArtifact.Read(bytes.AsSpan(), Tree(files)).Files.Count);
        });
        Assert.True(error is null, "[FAIL] binding_evidence_needs_no_semantic_manifest: " + error?.Message);
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
        }
        var bytes = StructuredCanonicalWriter.WriteJson(wire.ToJsonString());
        var snapshot = Tree(files);
        return Record.Exception(() => InformationTemplateEvidence.Collect(snapshot,
            RawLeanReportArtifact.Read(bytes.AsSpan(), snapshot), [RepoPath.CreateKnown(Registration)]));
    }

    [Fact]
    public void retired_module_version_field_is_rejected()
    {
        var error = ReadChangedManifest(InformationTemplateFixture.PolicyFiles()["lean-report-inputs.json"], 9);
        Assert.True(error is FormatException && error.Message.Contains("DTR-Evidence", StringComparison.Ordinal),
            "[FAIL] retired_module_version_field_is_rejected: " + error?.Message);
    }

    [Fact]
    public void selected_module_accepts_evidence_without_source_hash_lists()
    {
        var before = Files();
        var after = new Dictionary<string, string>(before) { [Registration] = before[Registration] + "-- changed\n" };
        var retained = Report(before, declared: true);
        var diagnostics = Dispatch(Context(before, after, retained, [Registration]));
        Assert.True(diagnostics.Any(d => d.Message.Contains("DTR-Declared", StringComparison.Ordinal))
            && diagnostics.All(d => !d.Message.Contains("DTR-Evidence", StringComparison.Ordinal)),
            "[FAIL] selected_module_accepts_evidence_without_source_hash_lists");
    }

    [Fact]
    public void indirect_judge_import_closure_keeps_ownership_without_hash_lists()
    {
        var files = Files();
        const string syntax = "tools/lean-inspector-interface/LeanInformationAuditInterface/Contract/Core.lean";
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
        Assert.Equal("LeanInformationAuditInterface.Contract.Core",
            Assert.Single(report.Files[RepoPath.CreateKnown(Registration)].Imports));
        var closure = LeanImportClosure.RepositoryPaths(report, RepoPath.CreateKnown(Registration));
        Assert.Contains(RepoPath.CreateKnown(DeclaredTemplateFixture.Target), closure);
        Assert.Equal(1, report.Files[RepoPath.CreateKnown(Registration)].Declarations.Count(
            declaration => declaration.Name == Key(0).Theorem + ".unit"));
        var error = Record.Exception(() => InformationTemplateEvidence.Collect(Tree(files), report,
            new[] { RepoPath.CreateKnown(Registration) }));
        Assert.Null(error);
        var evidence = InformationTemplateEvidence.Read(
            report.Files[RepoPath.CreateKnown(Registration)].InformationTemplates!.Value, Registration, Tree(files));
        Assert.False(evidence.Wire.TryGetProperty("inputs", out _));
    }
}
