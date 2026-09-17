using System.Collections.Immutable;
using System.Text;
using System.Text.Json;
using StrataLint.Engine;
using static StrataLint.Tests.InformationTemplateDebtStoreTests;

namespace StrataLint.Tests;

// These are strict wire/ownership fixtures. Kernel behavior is exercised by the
// Lean enrollment and registration controls, not by fabricated C# proofs.
public sealed class InformationTemplateEvidenceTests
{
    private const string PathA = "D5/S0/Carrier/Probe.lean";
    private const string ModuleA = "D5.S0.Carrier.Probe";
    private const string PathB = "D5/S0/Carrier/Binding.lean";
    private const string TextA = "-- synthetic evidence loader source A\n";
    private const string TextB = "import D5.S0.Carrier.Probe\n-- synthetic sidecar source\n";
    private static readonly InformationOccurrenceKey Key = new(ModuleA, ModuleA,
        ModuleA + ".target", ModuleA + ".arena", ModuleA + ".catalog");
    private static readonly string Unit = ModuleA + ".target.__information_unit";
    private static readonly string Realization = ModuleA + ".target.__primitive_realization";
    private const string MissingDiagnostic = "IE-C050 ClosedTruthReadout "
        + "key=D5.S0.Carrier.Probe/D5.S0.Carrier.Probe.catalog/D5.S0.Carrier.Probe.target "
        + "reason=unclassified_form rule=dtr.missing_declaration site=\"\" readout=\"\" "
        + "provenance={\"argument_inputs\":[],\"extraction_inputs\":[],\"plan_identity\":null,"
        + "\"rule\":\"dtr.missing_declaration\",\"site\":\"\",\"template_key\":null}";
    private static string Hash(string text) => InformationTemplateJson.Sha256(Encoding.UTF8.GetBytes(text));
    private static object Input(string path, string text) => new { path, sha256 = Hash(text) };

    private static RepositorySnapshot Snapshot(params (string Path, string Text)[] entries)
    {
        var files = DeclaredTemplateReviewTests.PolicyFiles();
        foreach (var (path, text) in entries) files[path] = text;
        return InformationTemplateDebtStoreTests.Snapshot(files.Select(p => (p.Key, p.Value)).ToArray());
    }

    private static object[] WithPolicy(params object[] inputs) => inputs.Concat(
        DeclaredTemplateReviewTests.PolicyFiles().Select(p => Input(p.Key, p.Value)))
        .OrderBy(input => JsonSerializer.SerializeToElement(input).GetProperty("path").GetString(), StringComparer.Ordinal).ToArray();

    private static JsonElement Wire(bool declared = false, bool sidecar = false, int? compatibility = null) =>
        JsonSerializer.SerializeToElement(new
        {
            schema_version = 1,
            compatibility_version = compatibility ?? DeclaredTemplateReviewTests.ManifestVersion(DeclaredTemplateReviewTests.PolicyFiles()),
            inputs = WithPolicy(sidecar ? new[] { Input(PathB, TextB), Input(PathA, TextA) } : new[] { Input(PathA, TextA) }),
            inventory = sidecar ? [] : new[] { InformationTemplateDebtStore.KeyJson(Key) },
            registered = sidecar ? [] : new[] { InformationTemplateDebtStore.KeyJson(Key) },
            records = new[] { new
            {
                key = InformationTemplateDebtStore.KeyJson(Key),
                unit_name = Unit,
                realization_name = Realization,
                registration_source_path = PathA,
                statement_identity = Hash("fixture statement A"),
                content_inputs = new[] { Input(PathA, TextA) },
                binding_source_path = declared ? sidecar ? PathB : PathA : null,
                state = declared ? "declared_validated" : "undeclared",
                diagnostic = declared ? null : MissingDiagnostic,
                certificate = declared ? new
                {
                    key = InformationTemplateDebtStore.KeyJson(Key),
                    evidence_ref = Hash("fixture binding A"),
                    plan_identity = Hash("fixture plan"),
                    descriptor_identity = Hash("fixture descriptor"),
                    actual_identity = Hash("fixture actual"),
                    argument_inputs = System.Array.Empty<object>(),
                    extraction_inputs = System.Array.Empty<object>(),
                } : null,
            } },
        });

    private static LeanFileReport Module(InformationTemplateModuleEvidence evidence, bool sidecar = false) =>
        new(sidecar ? [ModuleA] : [], sidecar ? [] :
            [new(Unit, "def", "fixture unit", []), new(Realization, "def", "fixture realization", [])])
        { InformationTemplates = evidence };

    [Theory]
    [InlineData("D5/S0/Carrier/Probe.lean", "D5.S0.Carrier.Probe")]
    [InlineData("tools/lean-inspector/LeanInformationAudit/Tests/Probe.lean", "LeanInformationAudit.Tests.Probe")]
    public void registration_owner_uses_lean_source_root(string path, string module) =>
        Assert.Equal(module, InformationTemplateEvidence.ModuleForSource(path));

    private static LeanAxiomReport RawReport(int? compatibility = null)
    {
        var wire = JsonSerializer.SerializeToElement(new
        {
            schema = "stratalint-raw-lean-report-v2",
            modules = new[] { new
            {
                module = ModuleA,
                source_path = PathA,
                source_sha256 = "sha256:" + Hash(TextA),
                imports = System.Array.Empty<string>(),
                declarations = System.Array.Empty<object>(),
                information_templates = Wire(compatibility: compatibility),
            } },
        });
        return RawLeanReportArtifact.Read(Trureturing.Truth.StructuredCanonicalWriter.WriteJson(wire.GetRawText()).AsSpan(),
            Snapshot((PathA, TextA)));
    }

    [Fact]
    public void complete_producer_loader_accepted() => Assert.Single(RawReport().Files);

    [Fact]
    public void raw_report_retains_binding_inventory()
    {
        var module = RawReport().Files[RepoPath.CreateKnown(PathA)];
        Assert.Equal(Key, Assert.Single(Assert.IsType<InformationTemplateModuleEvidence>(module.InformationTemplates).Records).Key);
    }

    [Theory]
    [InlineData(3)]
    [InlineData(4)]
    public void binding_loader_required(int retiredVersion) => Assert.Throws<FormatException>(() => RawReport(compatibility: retiredVersion));

    [Fact]
    public void fresh_imported_record_accepted()
    {
        var snapshot = Snapshot((PathA, TextA));
        var evidence = InformationTemplateEvidence.Read(Wire(), PathA, snapshot);
        var universe = InformationTemplateEvidence.Collect(snapshot,
            LeanAxiomReport.Create(new Dictionary<string, LeanFileReport> { [PathA] = Module(evidence) }));
        Assert.Single(universe.Inventory);
        Assert.Equal(InformationTemplateBindingState.Undeclared, universe.Occurrences[Key].State);
        Assert.Null(universe.Occurrences[Key].EvidenceRef);
        Assert.Equal(MissingDiagnostic, universe.Occurrences[Key].Diagnostic);
    }

    [Fact]
    public void seal_generated_unit_declarations_do_not_register_occurrences()
    {
        var snapshot = Snapshot((PathA, TextA));
        var module = Module(InformationTemplateEvidence.Read(Wire(), PathA, snapshot));
        // Sealing imports creates root-qualified abbreviations of retained
        // units without executing register_information_theorem again.
        module = module with { Declarations = module.Declarations.Add(
            new(ModuleA + ".sealed.__information_unit", "def", "fixture sealed unit", [])) };
        var error = Record.Exception(() =>
        {
            var universe = InformationTemplateEvidence.Collect(snapshot,
                LeanAxiomReport.Create(new Dictionary<string, LeanFileReport> { [PathA] = module }));
            Assert.Single(universe.Inventory);
        });
        Assert.True(error is null,
            "[FAIL] seal_generated_unit_declarations_do_not_register_occurrences: " + error?.Message);
    }

    [Fact]
    public void registered_occurrence_cannot_be_hidden_with_empty_events()
    {
        var snapshot = Snapshot((PathA, TextA));
        var wire = JsonSerializer.SerializeToNode(Wire())!.AsObject();
        wire["inventory"] = new System.Text.Json.Nodes.JsonArray();
        wire["records"] = new System.Text.Json.Nodes.JsonArray();
        var module = Module(InformationTemplateEvidence.Read(JsonSerializer.SerializeToElement(wire), PathA, snapshot));
        var error = Assert.Throws<FormatException>(() => InformationTemplateEvidence.Collect(snapshot,
            LeanAxiomReport.Create(new Dictionary<string, LeanFileReport> { [PathA] = module })));
        Assert.Contains("command inventory, retained units and binding records differ", error.Message);
    }

    [Fact]
    public void generated_name_with_nested_quote_accepted()
    {
        // Name.toString cannot wrap a component containing » in another pair
        // of quotes. This is the actual generated-name shape in the seed.
        var unit = ModuleA + ".target.Fixture.Root/Fixture.arena/«causal-unified-transitions».__information_unit";
        var realization = unit.Replace("__information_unit", "__primitive_realization", StringComparison.Ordinal);
        var snapshot = Snapshot((PathA, TextA));
        var wire = JsonSerializer.SerializeToNode(Wire())!.AsObject();
        wire["records"]![0]!["unit_name"] = unit;
        wire["records"]![0]!["realization_name"] = realization;
        InformationTemplateUniverse? universe = null;
        var error = Record.Exception(() =>
        {
            var evidence = InformationTemplateEvidence.Read(JsonSerializer.SerializeToElement(wire), PathA, snapshot);
            universe = InformationTemplateEvidence.Collect(snapshot, LeanAxiomReport.Create(
                new Dictionary<string, LeanFileReport>
                {
                    [PathA] = new([], [new(unit, "def", "fixture unit", []),
                        new(realization, "def", "fixture realization", [])]) { InformationTemplates = evidence },
                }));
        });
        Assert.True(error is null, "[FAIL] generated_name_with_nested_quote_accepted: " + error?.Message);
        Assert.Equal(unit, Assert.Single(universe!.Occurrences).Value.UnitName);
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void ambiguous_generated_name_rejected(bool realization)
    {
        var snapshot = Snapshot((PathA, TextA));
        var evidence = InformationTemplateEvidence.Read(Wire(), PathA, snapshot);
        var module = Module(evidence);
        // Distinct structural names can have the same display spelling. A
        // compiler-bound declaration count, not parser acceptance, rejects it.
        var duplicate = new LeanDeclaration(realization ? Realization : Unit, "def", "other declaration", [])
            { NameKey = "ns(n0,9:different)" };
        module = module with { Declarations = module.Declarations.Add(duplicate) };
        var error = Record.Exception(() => InformationTemplateEvidence.Collect(snapshot,
            LeanAxiomReport.Create(new Dictionary<string, LeanFileReport> { [PathA] = module })));
        Assert.True(error is FormatException && error.Message.Contains("retained unit/realization owner", StringComparison.Ordinal),
            "[FAIL] ambiguous_generated_" + (realization ? "realization" : "unit") + "_rejected");
    }

    private static InformationTemplateUniverse ImportedRealization(bool imported)
    {
        const string bridgeSource = "-- independently owned realization fixture\n";
        var registrationSource = imported ? "import D5.S0.Carrier.Binding\n" + TextA : TextA;
        var snapshot = Snapshot((PathA, registrationSource), (PathB, bridgeSource));
        var wire = JsonSerializer.SerializeToNode(Wire())!.AsObject();
        var inputs = new[] { Input(PathB, bridgeSource), Input(PathA, registrationSource) };
        wire["inputs"] = JsonSerializer.SerializeToNode(WithPolicy(inputs));
        wire["records"]![0]!["content_inputs"] = JsonSerializer.SerializeToNode(inputs);
        var owner = InformationTemplateEvidence.Read(JsonSerializer.SerializeToElement(wire), PathA, snapshot);
        var bridge = InformationTemplateEvidence.Read(JsonSerializer.SerializeToElement(new
        {
            schema_version = 1, compatibility_version = DeclaredTemplateReviewTests.ManifestVersion(DeclaredTemplateReviewTests.PolicyFiles()),
            inputs = WithPolicy(Input(PathB, bridgeSource)),
            inventory = System.Array.Empty<object>(), registered = System.Array.Empty<object>(),
            records = System.Array.Empty<object>(),
        }), PathB, snapshot);
        return InformationTemplateEvidence.Collect(snapshot, LeanAxiomReport.Create(
            new Dictionary<string, LeanFileReport>
            {
                [PathA] = new(imported ? ["D5.S0.Carrier.Binding"] : [],
                    [new(Unit, "def", "fixture unit", [])]) { InformationTemplates = owner },
                [PathB] = new([], [new(Realization, "theorem", "fixture realization", [])])
                    { InformationTemplates = bridge },
            }));
    }

    [Fact]
    public void imported_realization_owner_accepted() => Assert.Single(ImportedRealization(true).Inventory);

    [Fact]
    public void unimported_realization_owner_rejected() =>
        Assert.Throws<FormatException>(() => ImportedRealization(false));

    [Fact]
    public void undeclared_diagnostic_required()
    {
        var wire = JsonSerializer.SerializeToNode(Wire())!.AsObject();
        wire["records"]![0]!["diagnostic"] = null;
        Assert.Throws<FormatException>(() => InformationTemplateEvidence.Read(
            JsonSerializer.SerializeToElement(wire), PathA, Snapshot((PathA, TextA))));
    }

    [Fact]
    public void undeclared_diagnostic_cannot_retarget_occurrence()
    {
        var wire = JsonSerializer.SerializeToNode(Wire())!.AsObject();
        wire["records"]![0]!["diagnostic"] = MissingDiagnostic.Replace(".target ", ".other ", StringComparison.Ordinal);
        Assert.Throws<FormatException>(() => InformationTemplateEvidence.Read(
            JsonSerializer.SerializeToElement(wire), PathA, Snapshot((PathA, TextA))));
    }

    [Fact]
    public void complete_sidecar_join_accepted()
    {
        var snapshot = Snapshot((PathA, TextA), (PathB, TextB));
        var report = LeanAxiomReport.Create(new Dictionary<string, LeanFileReport>
        {
            [PathA] = Module(InformationTemplateEvidence.Read(Wire(), PathA, snapshot)),
            [PathB] = Module(InformationTemplateEvidence.Read(Wire(declared: true, sidecar: true), PathB, snapshot), sidecar: true),
        });
        var universe = InformationTemplateEvidence.Collect(snapshot, report);
        Assert.Single(universe.Occurrences);
        Assert.Equal(PathB, universe.Occurrences[Key].BindingSourcePath);
        Assert.Equal(InformationTemplateBindingState.DeclaredValidated, universe.Occurrences[Key].State);
    }

    [Fact]
    public void old_report_not_current_binding_evidence() =>
        Assert.Throws<FormatException>(() => InformationTemplateEvidence.Read(Wire(compatibility: 3), PathA,
            Snapshot((PathA, TextA))));

    [Theory]
    [InlineData("missing_inventory")]
    [InlineData("invalid_schema")]
    [InlineData("unknown_field")]
    [InlineData("non_object")]
    public void unrelated_malformed_evidence_keeps_structural_diagnostic(string mutation)
    {
        var wire = JsonSerializer.SerializeToNode(Wire())!.AsObject();
        if (mutation == "missing_inventory") wire.Remove("inventory");
        if (mutation == "invalid_schema") wire["schema_version"] = true;
        if (mutation == "unknown_field") wire["unknown"] = 1;
        var value = mutation == "non_object" ? JsonSerializer.SerializeToElement(Array.Empty<object>())
            : JsonSerializer.SerializeToElement(wire);
        var error = Assert.Throws<FormatException>(() => InformationTemplateEvidence.Read(value, PathA,
            Snapshot((PathA, TextA))));
        Assert.StartsWith("DTR-DebtSchema:", error.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void persisted_changed_input_rejected() =>
        Assert.Throws<FormatException>(() => InformationTemplateEvidence.Read(Wire(), PathA,
            Snapshot((PathA, TextA + "-- changed\n"))));

    [Fact]
    public void persisted_replay_rejected()
    {
        // Both source files are present and correctly hashed. The producer
        // cannot replay A's inline binding merely by adding B to its inputs.
        var wire = JsonSerializer.SerializeToNode(Wire(declared: true))!.AsObject();
        wire["inputs"] = JsonSerializer.SerializeToNode(new[] { Input(PathB, TextB), Input(PathA, TextA) });
        var error = Assert.Throws<FormatException>(() => InformationTemplateEvidence.Read(
            JsonSerializer.SerializeToElement(wire), PathB, Snapshot((PathA, TextA), (PathB, TextB))));
        Assert.Equal("DTR-Evidence: binding owner/diagnostic is missing or wrong", error.Message);
    }

    [Fact]
    public void binding_producer_cannot_disappear()
    {
        var snapshot = Snapshot((PathA, TextA));
        var report = LeanAxiomReport.Create(new Dictionary<string, LeanFileReport> { [PathA] = new([], []) });
        Assert.Throws<FormatException>(() => InformationTemplateEvidence.Collect(snapshot, report));
    }

    [Fact]
    public void inventory_hidden_root_rejected()
    {
        var snapshot = Snapshot((PathA, TextA), (PathB, TextB));
        var report = LeanAxiomReport.Create(new Dictionary<string, LeanFileReport>
        {
            [PathA] = Module(InformationTemplateEvidence.Read(Wire(), PathA, snapshot)),
        });
        Assert.Throws<FormatException>(() => InformationTemplateEvidence.Collect(snapshot, report));
    }

    [Fact]
    public void sidecar_cannot_overwrite_inline_claim()
    {
        var snapshot = Snapshot((PathA, TextA), (PathB, TextB));
        var report = LeanAxiomReport.Create(new Dictionary<string, LeanFileReport>
        {
            [PathA] = Module(InformationTemplateEvidence.Read(Wire(declared: true), PathA, snapshot)),
            [PathB] = Module(InformationTemplateEvidence.Read(Wire(declared: true, sidecar: true), PathB, snapshot), sidecar: true),
        });
        Assert.Throws<FormatException>(() => InformationTemplateEvidence.Collect(snapshot, report));
    }
    [Fact]
    public void historical_content_uses_current_judge_producer()
    {
        const string judge = "tools/lean-inspector/LeanInformationAudit/Registry.lean";
        var historical = Snapshot((PathA, TextA), (judge, "old producer"));
        var current = Snapshot((PathA, "candidate content cannot replace seed"), (judge, "current producer"));
        var wire = JsonSerializer.SerializeToNode(Wire())!.AsObject();
        wire["inputs"] = JsonSerializer.SerializeToNode(new[] { Input(PathA, TextA), Input(judge, "current producer") });
        var value = JsonSerializer.SerializeToElement(wire);
        Assert.Throws<FormatException>(() => InformationTemplateEvidence.Read(value, PathA, historical));
        var inputs = InformationTemplateEvidence.HistoricalInputs(historical, current);
        var evidence = InformationTemplateEvidence.Read(value, PathA, inputs);
        Assert.Single(evidence.Inventory);
        Assert.Equal(Key, Assert.Single(evidence.Records).Key);
        Assert.Equal(Hash(TextA), Assert.Single(evidence.Records).ContentInputs[0].Sha256);
        Assert.Throws<FormatException>(() => InformationTemplateEvidence.Read(value, PathA, current));
    }
}
