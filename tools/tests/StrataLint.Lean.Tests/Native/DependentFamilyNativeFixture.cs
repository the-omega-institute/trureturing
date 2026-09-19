using System.Collections.Immutable;
using System.Text;
using System.Text.Json;
using StrataLint.Engine;
using StrataLint.TestSupport;

namespace StrataLint.Lean.Tests;

// One real Lake/Inspector production shared by this test class. No fixture rows
// are synthesized and no source/report fallback is accepted.
public sealed class DependentFamilyNativeFixture : IDisposable
{
    private readonly TemporaryDirectory temporary = new();
    internal const string Prefix = "tools/lean-inspector/LeanInformationAudit/Tests/RegistrationGates/";
    internal RepositorySnapshot Snapshot { get; }
    internal LeanAxiomReport Report { get; }
    internal string Root { get; }

    public DependentFamilyNativeFixture()
    {
        Root = TestRepositoryLayout.FindRoot();
        var producer = Path.Combine(AppContext.BaseDirectory, "StrataLint.Lean.dll");
        // Production compilation, fixture compilation and report extraction
        // each use the existing process guard. Lake still owns all rebuilds.
        foreach (var operation in new[] { "build-producer", "build-fixtures", "produce" })
        {
            var result = TestProcessRunner.Run("python3",
                ["-B", "tools/lean-inspector/tests/family_native_fixture.py", operation, producer, temporary.Path],
                Root, TestBudgets.ReportSupervisorHangGuard, 4 * 1024 * 1024);
            Assert.True(result.ExitCode == 0, Encoding.UTF8.GetString(result.StandardOutput)
                + Encoding.UTF8.GetString(result.StandardError));
        }
        (Snapshot, Report) = Read(Root, Path.Combine(temporary.Path, "native.json"));
    }

    private static (RepositorySnapshot Snapshot, LeanAxiomReport Report) Read(string root, string artifact)
    {
        using var document = JsonDocument.Parse(File.ReadAllBytes(artifact));
        var modules = document.RootElement.GetProperty("modules").EnumerateArray().ToArray();
        var inputs = modules.SelectMany(m => m.GetProperty("information_templates").GetProperty("inputs")
            .EnumerateArray().Select(i => i.GetProperty("path").GetString()!)).Distinct().ToArray();
        var raw = RawRepositorySnapshot.Create(inputs.Select(p =>
            RawRepositoryEntry.FromText(p, File.ReadAllText(Path.Combine(root, p)))));
        var snapshot = Assert.IsType<SnapshotDecodeOutcome.Decoded>(SnapshotDecoder.Decode(raw)).Snapshot;
        var addresses = modules.SelectMany(m => m.GetProperty("declarations").EnumerateArray()
            .Select(d => d.GetProperty("type_sha256").GetString()!)).ToArray();
        var materials = RawLeanReportArtifact.OpenStatementMaterialSource(artifact, addresses);
        var reports = modules.ToDictionary(m => m.GetProperty("source_path").GetString()!, m =>
            new LeanFileReport(m.GetProperty("imports").EnumerateArray().Select(i => i.GetString()!).ToImmutableArray(),
                RawLeanReportArtifact.ReadDeclarations(m.GetProperty("declarations"), materials))
            { InformationTemplates = m.GetProperty("information_templates").Clone(),
                FamilyAssessments = m.GetProperty("family_assessments").Clone() });
        return (snapshot, LeanAxiomReport.Create(reports));
    }

    internal (RepositorySnapshot Snapshot, LeanAxiomReport Report) WarmTransition()
    {
        var destination = Path.Combine(temporary.Path, "transition");
        Directory.CreateDirectory(destination);
        var producer = Path.Combine(AppContext.BaseDirectory, "StrataLint.Lean.dll");
        foreach (var operation in new[] { "snapshot", "prior-build", "prior-produce",
            "current-build", "current-produce", "reuse" })
        {
            string[] command = ["python3", "-B", "tools/lean-inspector/tests/family_native_fixture.py",
                "transition-" + operation, producer, destination];
            if (operation == "snapshot") command = ["dotnet", producer, "with-cache-reader", "--", .. command];
            var result = TestProcessRunner.Run(command[0], command[1..], Root,
                TestBudgets.ReportSupervisorHangGuard, 4 * 1024 * 1024);
            Assert.True(result.ExitCode == 0, Encoding.UTF8.GetString(result.StandardOutput)
                + Encoding.UTF8.GetString(result.StandardError));
        }
        return Read(Path.Combine(destination, "repository"), Path.Combine(destination, "current", "native.json"));
    }

    internal static RepoPath Source(string name) => RepoPath.CreateKnown(Prefix + name + ".lean");

    internal InformationTemplateOccurrence Collect(string name, LeanAxiomReport? report = null) =>
        Assert.Single(InformationTemplateEvidence.Collect(Snapshot, report ?? Report, [Source(name)]).Occurrences.Values);

    internal JsonElement Payload(string name) => Report.Files[Source(name)].InformationTemplates!.Value;

    internal LeanAxiomReport Change(params (string Name, JsonElement Payload)[] changes) =>
        LeanAxiomReport.Create(Report.Files.ToDictionary(pair => pair.Key.Value, pair =>
        {
            var change = changes.SingleOrDefault(c => Source(c.Name) == pair.Key);
            return change.Name is null ? pair.Value : pair.Value with { InformationTemplates = change.Payload };
        }));

    internal LeanAxiomReport IndependentlyProduced(params string[] names)
    {
        var replacements = new Dictionary<string, LeanFileReport>();
        foreach (var name in names)
        {
            var artifact = Path.Combine(temporary.Path, name, "native.json");
            using var document = JsonDocument.Parse(File.ReadAllBytes(artifact));
            var module = Assert.Single(document.RootElement.GetProperty("modules").EnumerateArray());
            var declarations = module.GetProperty("declarations");
            var materials = RawLeanReportArtifact.OpenStatementMaterialSource(artifact,
                declarations.EnumerateArray().Select(d => d.GetProperty("type_sha256").GetString()!));
            replacements.Add(Source(name).Value, new LeanFileReport(module.GetProperty("imports")
                .EnumerateArray().Select(i => i.GetString()!).ToImmutableArray(),
                RawLeanReportArtifact.ReadDeclarations(declarations, materials))
            {
                InformationTemplates = module.GetProperty("information_templates").Clone(),
                FamilyAssessments = module.GetProperty("family_assessments").Clone(),
            });
        }
        return LeanAxiomReport.Create(Report.Files.ToDictionary(pair => pair.Key.Value,
            pair => replacements.GetValueOrDefault(pair.Key.Value, pair.Value)));
    }

    public void Dispose() => temporary.Dispose();
}
