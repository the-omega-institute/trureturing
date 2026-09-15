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
    private static string Hash(string text) => InformationTemplateJson.Sha256(Encoding.UTF8.GetBytes(text));
    private static object Input(string path, string text) => new { path, sha256 = Hash(text) };

    private static JsonElement Wire(bool declared = false, bool sidecar = false, int compatibility = 4) =>
        JsonSerializer.SerializeToElement(new
        {
            schema_version = 1,
            compatibility_version = compatibility,
            inputs = sidecar ? new[] { Input(PathB, TextB), Input(PathA, TextA) } : new[] { Input(PathA, TextA) },
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
                diagnostic = (string?)null,
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

    private static LeanAxiomReport RawReport(int compatibility = 4)
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

    [Fact]
    public void binding_loader_required() => Assert.Throws<FormatException>(() => RawReport(compatibility: 3));

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
