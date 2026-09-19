using System.Collections.Immutable;
using System.Runtime.CompilerServices;
using System.Text.Json;
using System.Text.Json.Nodes;
using StrataLint.Cli;
using StrataLint.Engine;
using Trureturing.Truth;

namespace StrataLint.Tests;

// Synthetic compiler evidence crosses the production raw loader before admission.
// RuleFixture supplies repository-backed policy through its normal read contracts.
public sealed class DeclaredTemplateDeltaLoadTests
{
    private const string A = RuleFixture.RingPath;
    private const string B = RuleFixture.ValuesBindingPath;
    private const string Pin = "Golden/Frozen/state/D5/S0/Carrier/Ring.lean.json";

    [Fact]
    public void changed_a_is_judged_when_unchanged_b_has_invalid_state()
    {
        using var fixture = new WireFixture();
        fixture.Evidence(B)["records"]![0]!["state"] = "invalid";
        AssertFinding(fixture, "DTR-Declared", AdmissionEffect.Observe);
        fixture.AssertAdmissionReachesRules(blocked: false);
    }

    [Fact]
    public void unchanged_b_malformed_payload_is_not_read()
    {
        using var fixture = new WireFixture();
        fixture.Module(B)["information_templates"] = "malformed";
        AssertFinding(fixture, "DTR-Declared", AdmissionEffect.Observe);
    }

    [Fact]
    public void selected_a_malformed_evidence_blocks_in_rule()
    {
        using var fixture = new WireFixture();
        fixture.Evidence(A)["records"]![0]!["state"] = "invalid";
        AssertFinding(fixture, "DTR-Evidence", AdmissionEffect.Observe);
        fixture.AssertAdmissionReachesRules(blocked: false);
    }

    [Fact]
    public void selected_malformed_owner_path_blocks_in_rule()
    {
        using var fixture = new WireFixture();
        fixture.Evidence(A)["records"]![0]!["registration_source_path"] = "../Ring.lean";
        var error = Xunit.Record.Exception(() => AssertFinding(fixture, "DTR-Evidence", AdmissionEffect.Observe));
        Assert.True(error is null, "[FAIL] selected_malformed_owner_path_blocks_in_rule: " + error?.Message);
        fixture.AssertAdmissionReachesRules(blocked: false);
    }

    [Fact]
    public void mixed_sidecar_validates_only_selected_registration_records()
    {
        using var fixture = new WireFixture();
        fixture.SetUndeclared(A);
        fixture.Evidence(B)["records"]!.AsArray().Add(fixture.Record(A, B));
        fixture.Evidence(B)["records"]![0]!["state"] = "invalid";
        AssertFinding(fixture, "DTR-Declared", AdmissionEffect.Observe);
    }

    [Fact]
    public void selected_producer_skips_sidecar_record_for_unchanged_owner()
    {
        using var fixture = new WireFixture();
        var foreign = fixture.Record(B, A);
        foreign["certificate"] = "malformed";
        fixture.Evidence(A)["records"]!.AsArray().Add(foreign);
        AssertFinding(fixture, "DTR-Declared", AdmissionEffect.Observe);
    }

    [Fact]
    public void selected_sidecar_malformed_record_blocks()
    {
        using var fixture = new WireFixture();
        fixture.SetUndeclared(A);
        var selected = fixture.Record(A, B);
        selected["certificate"] = "malformed";
        fixture.Evidence(B)["records"]!.AsArray().Add(selected);
        AssertFinding(fixture, "DTR-Evidence", AdmissionEffect.Observe);
    }

    [Fact]
    public void first_pin_reads_unchanged_source_evidence()
    {
        using var fixture = new WireFixture("first-pin");
        AssertFinding(fixture, "DTR-Declared", AdmissionEffect.Observe);
    }

    [Fact]
    public void selected_missing_evidence_blocks()
    {
        using var fixture = new WireFixture();
        fixture.Module(A).Remove("information_templates");
        AssertFinding(fixture, "DTR-Evidence", AdmissionEffect.Observe);
    }

    [Fact]
    public void selected_stale_evidence_blocks()
    {
        using var fixture = new WireFixture();
        fixture.Evidence(A)["inputs"]![0]!["sha256"] = new string('0', 64);
        AssertFinding(fixture, "DTR-Evidence", AdmissionEffect.Observe);
    }

    [Fact]
    public void selected_malformed_payload_blocks()
    {
        using var fixture = new WireFixture();
        fixture.Module(A)["information_templates"] = "malformed";
        AssertFinding(fixture, "DTR-Evidence", AdmissionEffect.Observe);
    }

    [Fact]
    public void rename_destination_is_selected()
    {
        using var fixture = new WireFixture("rename");
        AssertFinding(fixture, "DTR-Declared", AdmissionEffect.Observe);
    }

    [Fact]
    public void copy_destination_is_selected()
    {
        using var fixture = new WireFixture("copy");
        AssertFinding(fixture, "DTR-Declared", AdmissionEffect.Observe);
    }

    [Fact]
    public void judge_only_delta_is_unaffected_and_does_not_read_evidence()
    {
        using var fixture = new WireFixture("judge");
        fixture.Module(A)["information_templates"] = "malformed";
        AssertUnaffected(fixture);
    }

    [Fact]
    public void deleted_d5_module_has_no_finding()
    {
        using var fixture = new WireFixture("delete");
        fixture.Module(B)["information_templates"] = "malformed";
        AssertUnaffected(fixture);
    }

    private static void AssertUnaffected(WireFixture fixture, [CallerMemberName] string name = "")
    {
        var context = fixture.Load(name);
        Assert.False(DeclaredTemplateBindingRule.IsAffectedBy(context), "[FAIL] " + name);
        Assert.Empty(DeclaredTemplateBindingRule.Evaluate(context));
        Assert.Empty(Diagnostics(context));
    }

    private static ImmutableArray<Diagnostic> Diagnostics(DeltaRuleContext context) =>
        RuleCatalog.Default.EvaluateSingle(UtilityAdmissionTestSupport.UtilityRuleId, context).Diagnostics
            .Where(d => d.Message.StartsWith("DTR-", StringComparison.Ordinal)).ToImmutableArray();

    private static void AssertFinding(WireFixture fixture, string code, AdmissionEffect effect,
        [CallerMemberName] string name = "")
    {
        var context = fixture.Load(name);
        Assert.True(DeclaredTemplateBindingRule.IsAffectedBy(context), "[FAIL] " + name + " not selected");
        var findings = Diagnostics(context);
        Assert.True(findings.Length == 1 && findings[0].Path == A
            && findings[0].Message.StartsWith(code + " ", StringComparison.Ordinal)
            && findings[0].AdmissionEffect == effect,
            "[FAIL] " + name + ": " + string.Join("; ", findings.Select(d => d.Render())));
    }

    private sealed class WireFixture : IDisposable
    {
        private readonly TemporaryDirectory directory = new();
        private readonly DeltaRuleContext context;
        private readonly string reportPath;
        private readonly JsonNode wire;

        internal WireFixture(string delta = "changed")
        {
            var fixture = new RuleFixture();
            fixture.Files[A] = UtilityAdmissionTestSupport.WithUtility(fixture.Files[A], "none");
            fixture.Baseline[A] = fixture.Files[A];
            var changes = RawChangeSet.Create([A]);
            switch (delta)
            {
                case "first-pin":
                    fixture.Files[Pin] = "{}\n";
                    changes = RawChangeSet.CreateWithKinds([(Pin, RawChangeKind.Added)]);
                    break;
                case "rename":
                case "copy":
                    const string old = "D5/S0/Carrier/Old.lean";
                    fixture.Baseline[old] = fixture.Baseline[A];
                    fixture.Baseline.Remove(A);
                    if (delta == "copy")
                    {
                        fixture.Files[old] = fixture.Baseline[old];
                        fixture.Reports[old] = new([], []);
                    }
                    changes = RawChangeSet.CreateWithKinds(delta == "rename"
                        ? [(old, RawChangeKind.Deleted), (A, RawChangeKind.Added)]
                        : [(A, RawChangeKind.Copied)]);
                    break;
                case "judge":
                    fixture.Files[RuleFixture.SyntheticProtectedPath] = "// changed judge\n";
                    changes = RawChangeSet.Create([RuleFixture.SyntheticProtectedPath]);
                    break;
                case "delete":
                    fixture.Files.Remove(A);
                    fixture.Reports.Remove(A);
                    changes = RawChangeSet.CreateWithKinds([(A, RawChangeKind.Deleted)]);
                    break;
                default:
                    fixture.Files[A] += "-- changed\n";
                    break;
            }
            foreach (var path in new[] { A, B }.Where(fixture.Reports.ContainsKey))
                fixture.Reports[path] = fixture.Reports[path] with
                {
                    Declarations = fixture.Reports[path].Declarations.AddRange(new LeanDeclaration[] {
                        new(ModuleName(path) + ".unit", "def", "True", []),
                        new(ModuleName(path) + ".realization", "def", "True", []) }),
                };
            context = fixture.Build(changes);
            reportPath = Path.Combine(directory.Path, "candidate.json");
            RawLeanReportArtifact.WriteFile(reportPath, context.Current, context.Lean.Report);
            wire = JsonNode.Parse(File.ReadAllBytes(reportPath))!;
            foreach (var path in new[] { A, B }.Where(fixture.Reports.ContainsKey))
            {
                var evidence = Evidence(path);
                evidence["inventory"] = new JsonArray(Key(path));
                evidence["registered"] = new JsonArray(Key(path));
                evidence["records"] = new JsonArray(Record(path, path));
            }
        }

        private static string ModuleName(string path) => path[..^5].Replace('/', '.');
        private static JsonNode Key(string path)
        {
            var module = ModuleName(path);
            return JsonSerializer.SerializeToNode(new
            {
                root = module, registration_module = module, theorem = module + ".target",
                object_arena = module + ".arena", catalog = module + ".catalog", mode = "fixed-state-v1",
            })!;
        }

        internal JsonObject Module(string path) => wire["modules"]!.AsArray()
            .Single(node => node!["source_path"]!.GetValue<string>() == path)!.AsObject();
        internal JsonObject Evidence(string path) => Module(path)["information_templates"]!.AsObject();

        internal JsonObject Record(string owner, string producer) => JsonSerializer.SerializeToNode(new
        {
            key = Key(owner), registration_source_path = owner,
            statement_identity = new string('a', 64),
            content_inputs = new[] { new { path = owner,
                sha256 = InformationTemplateJson.Sha256(context.Current.Files[RepoPath.CreateKnown(owner)].RawBytes.AsSpan()) } },
            binding_source_path = producer, state = "declared_validated", diagnostic = (string?)null,
            escape_from = DeclaredTemplateEscapeRecordTests.FromSlot,
            escape_continues = DeclaredTemplateEscapeRecordTests.OpenSlot, bridge_kind = "legacy",
            unit_name = ModuleName(owner) + ".unit", realization_name = ModuleName(owner) + ".realization",
            certificate = new
            {
                key = Key(owner), evidence_ref = new string('b', 64), plan_identity = new string('c', 64),
                descriptor_identity = new string('d', 64), actual_identity = new string('e', 64),
                argument_inputs = Array.Empty<object>(), extraction_inputs = Array.Empty<object>(),
            },
        })!.AsObject();

        internal void SetUndeclared(string path)
        {
            var record = Evidence(path)["records"]![0]!;
            var module = ModuleName(path);
            record["state"] = "undeclared";
            record["binding_source_path"] = null;
            record["certificate"] = null;
            record["diagnostic"] = $"IE-C050 ClosedTruthReadout key={module}/{module}.catalog/{module}.target "
                + "reason=unclassified_form rule=dtr.missing_declaration site=\"\" readout=\"\" "
                + "provenance={\"argument_inputs\":[],\"extraction_inputs\":[],\"plan_identity\":null,"
                + "\"rule\":\"dtr.missing_declaration\",\"site\":\"\",\"template_key\":null}";
        }

        internal DeltaRuleContext Load(string name)
        {
            File.WriteAllBytes(reportPath, StructuredCanonicalWriter.WriteJson(wire.ToJsonString()).ToArray());
            LeanAxiomReport? report = null;
            var error = Xunit.Record.Exception(() => report = RawLeanReportArtifact.ReadFile(reportPath, context.Current));
            Assert.True(error is null, "[FAIL] " + name + " global load failure: " + error?.Message);
            return DeltaRuleContext.Create(context.Current, context.Baseline, context.Policy,
                AcceptedLeanClosure.Create(report!), context.Changes, context.MetaEvaluation);
        }

        internal void AssertAdmissionReachesRules(bool blocked, [CallerMemberName] string name = "")
        {
            var loaded = Load(name);
            var evaluation = SnapshotAdmissionCore.Evaluate(loaded.Current, loaded.Baseline,
                loaded.Lean.Report, loaded.Changes, BootstrapGate.Evaluate(loaded.Changes), null);
            // The test map binds source without Dunet's generated outcome inheritance.
            object outcome = evaluation.Outcome;
            Assert.True(outcome is not AdmissionOutcome.InfrastructureFailure,
                "[FAIL] " + name + ": " + outcome);
            if (!blocked)
                Assert.True(outcome is AdmissionOutcome.Admitted, "[FAIL] " + name + ": "
                    + (outcome is AdmissionOutcome.RuleRejected failure
                        ? string.Join("; ", failure.Diagnostics.Select(d => d.Render())) : outcome.ToString()));
            var diagnostics = blocked
                ? Assert.IsType<AdmissionOutcome.RuleRejected>(outcome).Diagnostics
                : Assert.IsType<AdmissionOutcome.Admitted>(outcome).Observations;
            Assert.Contains(diagnostics, d => d.Path == A && d.Message.StartsWith("DTR-", StringComparison.Ordinal));
            Assert.DoesNotContain(diagnostics, d => d.Path == B && d.Message.StartsWith("DTR-", StringComparison.Ordinal));
        }

        public void Dispose() => directory.Dispose();
    }
}
