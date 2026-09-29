using System.Collections.Immutable;
using System.IO.Compression;
using System.Text.Json;
using System.Text.Json.Nodes;
using StrataLint.Engine;
using Trureturing.Truth;
using static StrataLint.TestSupport.DeclaredTemplateFixture;

namespace StrataLint.DeclaredTemplate.Tests;

public sealed class PhysicalParserEvidenceTests
{
    private static readonly (string Module, string Theorem)[] Originals =
    [
        ("PhysicalSixParser", "coupled_source_rewind"),
        ("PhysicalParserTally", "count_one"),
        ("PhysicalParserPadding", "pad_one"),
        ("PhysicalParserField", "parse_field"),
        ("PhysicalParserExecution", "parser_frame_resources"),
    ];

    // Opt in with current scoped Lake :report artifacts, never a synthetic wire.
    // The companion Lean test checks complete Laws, erasure and actual dependence.
    [SkippableFact]
    public void current_physical_parser_artifacts_preserve_freeze_and_pass_production_consumer()
    {
        var directory = Environment.GetEnvironmentVariable("PHYSICAL_PARSER_ARTIFACTS");
        Skip.If(string.IsNullOrEmpty(directory), "Focused physical parser artifacts were not supplied.");
        var root = TestRepositoryLayout.FindRoot();
        var files = new Dictionary<string, LeanFileReport>();
        var sources = new Dictionary<string, string>();
        void Source(string path) => sources.TryAdd(path, File.ReadAllText(Path.Combine(root, path)));
        Source("lean-report-inputs.json");
        using var scratch = new TemporaryDirectory();
        foreach (var artifact in Directory.GetFiles(directory!, "*.zip").Order(StringComparer.Ordinal))
        {
            var extracted = Path.Combine(scratch.Path, Path.GetFileNameWithoutExtension(artifact));
            ZipFile.ExtractToDirectory(artifact, extracted);
            var reportPath = Path.Combine(extracted, "raw-lean-report.json");
            using var document = JsonDocument.Parse(File.ReadAllBytes(reportPath));
            var row = Assert.Single(document.RootElement.GetProperty("modules").EnumerateArray());
            var source = row.GetProperty("source_path").GetString()!;
            Source(source);
            var reportSources = new Dictionary<string, string>
            {
                ["lean-report-inputs.json"] = sources["lean-report-inputs.json"],
                [source] = sources[source],
            };
            var report = RawLeanReportArtifact.ReadFile(reportPath, Tree(reportSources), validateMaterials: true);
            var file = report.Files[RepoPath.CreateKnown(source)];
            Assert.All(file.Declarations, declaration =>
            {
                Assert.NotEmpty(declaration.LoadTypeRepresentation());
                Assert.All(declaration.Axioms, axiom =>
                    Assert.Contains(axiom, new[] { "propext", "Classical.choice", "Quot.sound" }));
            });
            files.Add(source, file);
        }

        var selected = new List<RepoPath>();
        var changes = new List<string>();
        var acceptedEvents = Directory.GetFiles(Path.Combine(root, "Golden/Frozen/accepted"), "*.json")
            .Select(p => (Path: p, Node: JsonNode.Parse(File.ReadAllText(p))!))
            .Where(p => Originals.Any(o => p.Node["payload"]?["descriptor_selector"]?.GetValue<string>()
                == "D5/S0/Computability/Coding/" + o.Module + ".lean")).ToArray();
        Assert.Equal(Originals.Length, acceptedEvents.Length);
        foreach (var (module, theorem) in Originals)
        {
            var path = RepoPath.CreateKnown("D5/S0/Computability/Coding/" + module + ".lean");
            var registration = "Reg/" + path.Value;
            var originalName = "D5.S0.Computability.Coding." + module + "." + theorem;
            Assert.Single(files[path.Value].Declarations.Where(d => d.Name == originalName && d.Kind == "theorem"));
            var declarations = CanonicalStatementWriter.DeclarationStatementIds(path, files[path.Value]);
            var statementId = FrozenContentHash.Compute(FrozenHashDomains.Statement,
                CanonicalStatementWriter.WriteModule(path, declarations).AsSpan());
            var pinPath = "Golden/Frozen/state/" + path.Value + ".json";
            Source(pinPath);
            Assert.Equal(statementId, FrozenStateRecordLoader.Load(Tree(sources).Files[
                RepoPath.CreateKnown(pinPath)]).StatementId.Value);

            // Validate the original writer event under the current candidate schema,
            // including every declaration identity, not only the designated result.
            var events = acceptedEvents
                .Where(p => p.Node["payload"]?["descriptor_selector"]?.GetValue<string>() == path.Value)
                .ToArray();
            var accepted = Assert.Single(events);
            var eventPath = Path.GetRelativePath(root, accepted.Path).Replace('\\', '/');
            Source(eventPath);
            var loaded = Assert.IsType<DagLedgerFilesLoadOutcome.Loaded>(FrozenAcceptedEventLoader.LoadFiles(
                [Tree(sources).Files[RepoPath.CreateKnown(eventPath)]]));
            var payload = Assert.Single(loaded.Events).Payload;
            Assert.Equal(statementId, payload.GetProperty("statement_id").GetString());
            var actualDeclarations = payload.GetProperty("declaration_statement_ids").EnumerateArray().Select(d =>
                (d.GetProperty("declaration_name_key").GetString()!, d.GetProperty("kind").GetString()!,
                    d.GetProperty("statement_id").GetString()!));
            Assert.Equal(declarations.Select(d => (d.DeclarationNameKey, d.Kind, d.StatementId.Value)), actualDeclarations);
            selected.Add(RepoPath.CreateKnown(registration));
            changes.AddRange([path.Value, registration, pinPath]);
        }

        Source(EngineeringProjectRegistry.ManifestPath);
        foreach (var input in EngineeringProjectRegistry.Parse(sources[EngineeringProjectRegistry.ManifestPath]).RuleBuildInputs)
            Source(input);
        var current = Tree(sources);
        var joined = LeanAxiomReport.Create(files);
        var evidence = InformationTemplateEvidence.Collect(current, joined, selected);
        Assert.Equal(Originals.Length, evidence.Inventory.Count);
        foreach (var (module, theorem) in Originals)
        {
            var occurrence = Assert.Single(evidence.Occurrences.Values,
                o => o.Key.Theorem == "D5.S0.Computability.Coding." + module + "." + theorem);
            Assert.True(occurrence.HasFourSlots);
            Assert.Equal("Reg.D5.S0.Computability.Coding." + module, occurrence.Key.RegistrationModule);
            Assert.Equal("legacy", occurrence.BridgeKind);
            Assert.Equal("Bool", occurrence.EscapeFrom!.Name);
            Assert.Equal("open", occurrence.EscapeContinues!.Kind);
        }

        var baseline = sources.Where(p => !changes.Contains(p.Key)).ToDictionary(p => p.Key, p => p.Value);
        var findings = DeclaredTemplateBindingRule.Evaluate(Context(baseline, sources, joined, changes.ToArray()));
        Assert.Equal(Originals.Length, findings.Length);
        Assert.All(findings, finding =>
        {
            Assert.StartsWith("DTR-Declared ", finding.Message);
            Assert.Equal(AdmissionEffect.Observe, finding.Effect);
        });

        // The actual consumer must reject a missing generated bridge declaration.
        foreach (var path in selected)
        {
            var realization = evidence.Occurrences.Values.Single(o => o.RegistrationSourcePath == path.Value)
                .RealizationName;
            var broken = new Dictionary<string, LeanFileReport>(files)
            {
                [path.Value] = files[path.Value] with
                {
                    Declarations = files[path.Value].Declarations.Where(d => d.Name != realization).ToImmutableArray(),
                },
            };
            Assert.Throws<FormatException>(() => InformationTemplateEvidence.Collect(
                current, LeanAxiomReport.Create(broken), [path]));

            var wire = JsonNode.Parse(files[path.Value].InformationTemplates!.Value.GetRawText())!;
            wire["records"]![0]!["certificate"]!["key"]!["theorem"] = "D5.Other.result";
            broken[path.Value] = files[path.Value] with { InformationTemplates = JsonSerializer.SerializeToElement(wire) };
            Assert.Throws<FormatException>(() => InformationTemplateEvidence.Collect(
                current, LeanAxiomReport.Create(broken), [path]));
        }
    }
}
