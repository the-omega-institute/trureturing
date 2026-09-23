using System.Collections.Immutable;
using System.Text.Json;
using System.Text.Json.Nodes;
using StrataLint.Engine;
using static StrataLint.Tests.DeclaredTemplateReviewTests;

namespace StrataLint.Tests;

public sealed class DeclaredTemplateOwnerMirrorTests
{
    private const string SourceOwner = DeclaredTemplateReviewTests.Target;
    private const string Mirror = "Reg/" + SourceOwner;
    private const string Variant = "Reg/D5/S0/Carrier/Target/Alternate.lean";
    private const string Other = "Reg/D5/S0/Carrier/Other.lean";
    private const string Theorem = "Different.Namespace.result";
    private const string Source = "namespace Different.Namespace\ntheorem result : True := by trivial\nend Different.Namespace\n";

    [Fact]
    public void reg_only_change_dispatches_declared_observation()
    {
        var fixture = new Fixture();
        fixture.AddRegistration(Mirror);
        fixture.Change(Mirror);
        var context = fixture.Context();
        Assert.True(DeclaredTemplateBindingRule.IsAffectedBy(context));
        AssertDeclared(DeclaredTemplateBindingRule.Evaluate(context), 1);
        var diagnostics = RuleCatalog.Default.EvaluateSingle(UtilityAdmissionTestSupport.UtilityRuleId, context).Diagnostics;
        Assert.Contains(diagnostics, d => d.Path == Mirror && d.Message.StartsWith("DTR-Declared ", StringComparison.Ordinal)
            && d.AdmissionEffect == AdmissionEffect.Observe);
    }

    [Fact]
    public void new_theorem_routes_by_source_owner_despite_different_namespace()
    {
        var fixture = new Fixture(newTheorem: true);
        fixture.AddRegistration(Mirror);
        AssertDeclared(fixture.Findings(), 1);
    }

    [Fact]
    public void absent_owner_mirror_cannot_be_replaced_by_theorem_name_discovery()
    {
        var fixture = new Fixture(newTheorem: true);
        fixture.AddRegistration(Other);
        AssertUnregistered(fixture.Findings());
    }

    [Fact]
    public void theorem_namespace_path_does_not_replace_source_owner_mirror()
    {
        var fixture = new Fixture(newTheorem: true);
        fixture.AddRegistration("Reg/Different/Namespace.lean");
        AssertUnregistered(fixture.Findings());
    }

    [Fact]
    public void deleted_owner_mirror_yields_unregistered()
    {
        var fixture = new Fixture(newTheorem: true);
        fixture.AddRegistration(Mirror);
        fixture.After.Remove(Mirror);
        fixture.Reports.Remove(Mirror);
        fixture.Changes.Add(Mirror);
        fixture.AddRegistration(Other);
        AssertUnregistered(fixture.Findings());
    }

    [Fact]
    public void imported_variant_preserves_each_occurrence_identity()
    {
        var fixture = new Fixture(newTheorem: true);
        fixture.AddRegistration(Mirror);
        fixture.AddRegistration(Variant);
        fixture.Import(Mirror, Variant);
        var findings = fixture.Findings();
        AssertDeclared(findings, 2);
        Assert.Contains(findings, f => f.Message.Contains("Reg.D5.S0.Carrier.Target.Alternate", StringComparison.Ordinal));
    }

    [Fact]
    public void unimported_variant_does_not_cover_new_theorem()
    {
        var fixture = new Fixture(newTheorem: true);
        fixture.AddEmpty(Mirror);
        fixture.AddRegistration(Variant);
        AssertUnregistered(fixture.Findings());
    }

    [Fact]
    public void unrelated_malformed_registration_in_imported_module_is_not_validated()
    {
        var fixture = new Fixture(newTheorem: true);
        fixture.AddRegistration(Mirror);
        fixture.AddRegistration(Other, "Unrelated.result");
        fixture.Mutate(Other, wire => wire["records"]![0]!["certificate"] = "malformed");
        fixture.Import(Mirror, Other);
        AssertDeclared(fixture.Findings(), 1);
    }

    [Fact]
    public void unrelated_report_payload_cannot_fail_new_theorem()
    {
        var fixture = new Fixture(newTheorem: true);
        fixture.AddRegistration(Mirror);
        fixture.AddEmpty(Other);
        fixture.Reports[Other] = fixture.Reports[Other] with { InformationTemplates = JsonSerializer.SerializeToElement("malformed") };
        AssertDeclared(fixture.Findings(), 1);
    }

    [Fact]
    public void unrelated_record_in_exact_mirror_is_not_selected_by_new_theorem()
    {
        var fixture = new Fixture(newTheorem: true);
        fixture.AddRegistration(Mirror);
        fixture.Mutate(Mirror, wire => wire["records"]!.AsArray().Add(JsonSerializer.SerializeToNode(new
        {
            key = new { theorem = "Unrelated.result" }, certificate = "malformed",
        })));
        AssertDeclared(fixture.Findings(), 1);
    }

    [Fact]
    public void owner_mismatch_is_observed_and_does_not_cover_theorem()
    {
        var fixture = new Fixture(newTheorem: true);
        fixture.AddRegistration(Mirror);
        fixture.Mutate(Mirror, wire => wire["records"]![0]!["registration_source_path"] = Other);
        var findings = fixture.Findings();
        AssertUnregistered(findings);
        Assert.Contains(findings, f => f.Message.StartsWith("DTR-Evidence ", StringComparison.Ordinal));
    }

    [Fact]
    public void registration_must_import_actual_theorem_owner_even_with_local_realization()
    {
        var fixture = new Fixture(newTheorem: true);
        fixture.AddRegistration(Mirror);
        fixture.Reports[Mirror] = fixture.Reports[Mirror] with
        {
            Imports = [],
            Declarations = fixture.Reports[Mirror].Declarations.Add(new(Theorem + ".realization", "def", "True", [])),
        };
        var findings = fixture.Findings();
        AssertUnregistered(findings);
        Assert.Contains(findings, f => f.Message.Contains("unique theorem source owner", StringComparison.Ordinal));
    }

    [Fact]
    public void unchanged_reg_path_in_changes_does_not_select_malformed_payload()
    {
        var fixture = new Fixture();
        fixture.AddEmpty(Mirror);
        fixture.Changes.Add(Mirror);
        fixture.Reports[Mirror] = fixture.Reports[Mirror] with { InformationTemplates = JsonSerializer.SerializeToElement("malformed") };
        Assert.False(DeclaredTemplateBindingRule.IsAffectedBy(fixture.Context()));
        Assert.Empty(fixture.Findings());
    }

    [Fact]
    public void malformed_selected_mirror_keeps_unregistered_observation()
    {
        var fixture = new Fixture(newTheorem: true);
        fixture.AddEmpty(Mirror);
        fixture.Reports[Mirror] = fixture.Reports[Mirror] with { InformationTemplates = JsonSerializer.SerializeToElement("malformed") };
        var findings = fixture.Findings();
        AssertUnregistered(findings);
        Assert.Contains(findings, f => f.Message.StartsWith("DTR-Evidence ", StringComparison.Ordinal));
    }

    [Fact]
    public void malformed_selected_producer_does_not_suppress_other_selected_producer()
    {
        var fixture = new Fixture();
        fixture.AddRegistration(Mirror);
        fixture.AddRegistration(Other);
        fixture.Change(Mirror);
        fixture.Change(Other);
        fixture.Mutate(Mirror, wire => wire["records"]![0]!["state"] = "invalid");
        var findings = fixture.Findings();
        Assert.Contains(findings, f => f.Path == Mirror && f.Message.StartsWith("DTR-Evidence ", StringComparison.Ordinal));
        Assert.Contains(findings, f => f.Path == Other && f.Message.StartsWith("DTR-Declared ", StringComparison.Ordinal));
        Assert.All(findings, f => Assert.Equal(AdmissionEffect.Observe, f.Effect));
    }

    [Fact]
    public void malformed_variant_does_not_hide_valid_route_for_same_theorem()
    {
        var fixture = new Fixture(newTheorem: true);
        fixture.AddRegistration(Mirror);
        fixture.AddRegistration(Variant);
        fixture.Import(Mirror, Variant);
        fixture.Mutate(Variant, wire => wire["records"]![0]!["state"] = "invalid");
        var findings = fixture.Findings();
        Assert.Contains(findings, f => f.Message.StartsWith("DTR-Evidence ", StringComparison.Ordinal));
        Assert.Contains(findings, f => f.Message.StartsWith("DTR-Declared ", StringComparison.Ordinal));
        Assert.DoesNotContain(findings, f => f.Message.StartsWith("DTR-Unregistered ", StringComparison.Ordinal));
        Assert.All(findings, f => Assert.Equal(AdmissionEffect.Observe, f.Effect));
    }

    [Fact]
    public void first_pin_does_not_create_authored_theorem_or_read_unchanged_mirror()
    {
        var fixture = new Fixture();
        fixture.AddRegistration(Mirror);
        fixture.Reports[Mirror] = fixture.Reports[Mirror] with { InformationTemplates = JsonSerializer.SerializeToElement("malformed") };
        const string pin = "Golden/Frozen/state/" + SourceOwner + ".json";
        fixture.After[pin] = "{}";
        fixture.Changes.Add(pin);
        Assert.Empty(fixture.Findings());
    }

    [Theory]
    [InlineData("undeclared", "DTR-Undeclared ")]
    [InlineData("declared_unresolved", "DTR-Evidence ")]
    [InlineData("declared_validated", "DTR-Declared ")]
    [InlineData("invalid", "DTR-Evidence ")]
    public void selected_reg_statuses_remain_observe(string state, string prefix)
    {
        var fixture = new Fixture();
        fixture.AddRegistration(Mirror, declared: state != "undeclared");
        fixture.Change(Mirror);
        fixture.Mutate(Mirror, wire =>
        {
            var record = wire["records"]![0]!;
            record["state"] = state;
            if (state == "declared_unresolved") { record["certificate"] = null; record["diagnostic"] = "unresolved"; }
        });
        var findings = fixture.Findings();
        Assert.StartsWith(prefix, Assert.Single(findings).Message, StringComparison.Ordinal);
        Assert.All(findings, f => Assert.Equal(AdmissionEffect.Observe, f.Effect));
    }

    private const string SidecarOwner = "Reg/Support/SidecarOwner.lean";
    private const string Sidecar = "Reg/Support/SidecarBinding.lean";

    [Theory]
    [InlineData("validated", "DTR-Declared ")]
    [InlineData("unresolved", "DTR-Evidence ")]
    [InlineData("missing_slots", "DTR-Undeclared ")]
    public void changed_sidecar_routes_to_original_occurrence(string mode, string prefix)
    {
        var fixture = SidecarFixture();
        fixture.Mutate(Sidecar, wire =>
        {
            var record = wire["records"]![0]!;
            if (mode == "unresolved")
            {
                record["state"] = "declared_unresolved";
                record["certificate"] = null;
                record["diagnostic"] = "unresolved";
            }
            if (mode == "missing_slots") { record["escape_from"] = null; record["escape_continues"] = null; }
        });
        var context = fixture.Context();
        Assert.Equal(fixture.Before[SidecarOwner], fixture.After[SidecarOwner]);
        Assert.Equal(new[] { Sidecar }, InformationTemplateSelection.ChangedProducers(context).Select(p => p.Value));
        Assert.DoesNotContain(RepoPath.CreateKnown(Sidecar),
            LeanImportClosure.RepositoryPaths(context.Lean.Report, RepoPath.CreateKnown(SidecarOwner)));
        AssertSidecarFinding(context, prefix);
        // The unchanged producer is not selected just because Changes names it.
        fixture.Before[Sidecar] = fixture.After[Sidecar];
        Assert.Empty(fixture.Findings());
        fixture.Change(SidecarOwner);
        Assert.StartsWith(prefix, Assert.Single(fixture.Findings()).Message, StringComparison.Ordinal);
    }

    [Theory]
    [InlineData("payload")]
    [InlineData("certificate")]
    [InlineData("key")]
    [InlineData("binding_owner")]
    [InlineData("registration_owner")]
    [InlineData("missing_original")]
    [InlineData("duplicate")]
    [InlineData("inline_claim")]
    [InlineData("other_sidecar")]
    [InlineData("statement")]
    [InlineData("unit")]
    [InlineData("realization")]
    public void changed_sidecar_invalid_selected_evidence_is_observed(string mutation)
    {
        var fixture = SidecarFixture();
        if (mutation == "payload")
            fixture.Reports[Sidecar] = fixture.Reports[Sidecar] with { InformationTemplates = JsonSerializer.SerializeToElement("malformed") };
        else if (mutation == "missing_original") fixture.AddEmpty(SidecarOwner);
        else if (mutation == "inline_claim") fixture.AddRegistration(SidecarOwner);
        else if (mutation == "other_sidecar") fixture.AddSidecar(Other, SidecarOwner);
        else fixture.Mutate(Sidecar, wire =>
        {
            var record = wire["records"]![0]!;
            switch (mutation)
            {
                case "certificate": record["certificate"] = "malformed"; break;
                case "key": record["key"] = null; break;
                case "binding_owner": record["binding_source_path"] = Other; break;
                case "registration_owner": record["registration_source_path"] = Other; break;
                case "duplicate": wire["records"]!.AsArray().Add(record.DeepClone()); break;
                case "statement": record["statement_identity"] = new string('f', 64); break;
                case "unit": record["unit_name"] = "Other.unit"; break;
                case "realization": record["realization_name"] = "Other.realization"; break;
            }
        });
        AssertSidecarFinding(fixture.Context(), "DTR-Evidence ");
    }

    [Fact]
    public void changed_sidecar_selects_exact_occurrence_not_entire_unchanged_owner()
    {
        var fixture = SidecarFixture();
        fixture.AddRegistration(Other);
        fixture.Mutate(Other, wire => wire["records"]![0]!["certificate"] = "malformed");
        fixture.Mutate(SidecarOwner, wire =>
        {
            // Even another occurrence of the SAME theorem stays unselected.
            var key = wire["inventory"]![0]!.DeepClone();
            key["object_arena"] = "Other.arena";
            key["catalog"] = "Other.catalog";
            wire["inventory"]!.AsArray().Add(key.DeepClone());
            wire["registered"]!.AsArray().Add(key.DeepClone());
            var record = wire["records"]![0]!.DeepClone();
            record["key"] = key;
            record["certificate"] = "malformed";
            wire["records"]!.AsArray().Add(record);
        });
        fixture.Changes.Add(Other); // unchanged bytes must not acquire an obligation
        AssertSidecarFinding(fixture.Context(), "DTR-Declared ");
    }

    [Fact]
    public void changed_sidecar_with_own_registration_collects_both_owners_once()
    {
        var fixture = SidecarFixture();
        var overlay = JsonSerializer.SerializeToNode(fixture.Reports[Sidecar].InformationTemplates)!["records"]![0]!.DeepClone();
        fixture.AddRegistration(Sidecar, "Sidecar.local");
        fixture.Import(Sidecar, SidecarOwner);
        fixture.Changes.Clear();
        fixture.Change(Sidecar);
        fixture.Mutate(Sidecar, wire => wire["records"]!.AsArray().Add(overlay));
        AssertDeclared(fixture.Findings(), 2);
        fixture.Change(SidecarOwner);
        AssertDeclared(fixture.Findings(), 2);
    }

    private static Fixture SidecarFixture()
    {
        var fixture = new Fixture();
        fixture.AddRegistration(SidecarOwner, declared: false);
        fixture.AddSidecar(Sidecar, SidecarOwner);
        fixture.Change(Sidecar);
        return fixture;
    }

    private static void AssertSidecarFinding(DeltaRuleContext context, string prefix)
    {
        var finding = Assert.Single(DeclaredTemplateBindingRule.Evaluate(context));
        Assert.Equal(Sidecar, finding.Path);
        Assert.StartsWith(prefix, finding.Message, StringComparison.Ordinal);
        Assert.Equal(AdmissionEffect.Observe, finding.Effect);
        var dispatched = Assert.Single(RuleCatalog.Default.EvaluateSingle(UtilityAdmissionTestSupport.UtilityRuleId, context)
            .Diagnostics.Where(d => d.Message.StartsWith("DTR-", StringComparison.Ordinal)));
        Assert.Equal(finding.Message, dispatched.Message);
        Assert.Equal(AdmissionEffect.Observe, dispatched.AdmissionEffect);
    }

    private static void AssertUnregistered(ImmutableArray<RuleFinding> findings)
    {
        Assert.Contains(findings, f => f.Message == "DTR-Unregistered D5.S0.Carrier.Target/" + Theorem);
        Assert.All(findings, f => Assert.Equal(AdmissionEffect.Observe, f.Effect));
    }

    private static void AssertDeclared(ImmutableArray<RuleFinding> findings, int count)
    {
        Assert.Equal(count, findings.Length);
        Assert.All(findings, f =>
        {
            Assert.StartsWith("DTR-Declared ", f.Message, StringComparison.Ordinal);
            Assert.Equal(AdmissionEffect.Observe, f.Effect);
        });
    }

    private sealed class Fixture
    {
        internal readonly Dictionary<string, string> Before = Files();
        internal readonly Dictionary<string, string> After;
        internal readonly Dictionary<string, LeanFileReport> Reports;
        internal readonly List<string> Changes = [];

        internal Fixture(bool newTheorem = false)
        {
            Before["lean-report-inputs.json"] = Before["lean-report-inputs.json"].Replace(
                "\"D5/**/*.lean\"", "\"**/*.lean\"", StringComparison.Ordinal);
            Before["Meta/FILEMAP.inputs.toml"] = Before["Meta/FILEMAP.inputs.toml"].Replace(
                "\"D5/**\"", "\"**/*.lean\"", StringComparison.Ordinal);
            Before[SourceOwner] = newTheorem ? "-- no theorem\n" : Source;
            After = new(Before) { [SourceOwner] = Source };
            Reports = Report(After, count: 0).Files.ToDictionary(p => p.Key.Value, p => p.Value);
            Reports[SourceOwner] = Reports[SourceOwner] with { Declarations = [new(Theorem, "theorem", "True", [])] };
            if (newTheorem) Changes.Add(SourceOwner);
        }

        internal void AddEmpty(string path)
        {
            Before[path] = After[path] = "import D5.S0.Carrier.Target\n";
            Reports[path] = new(["D5.S0.Carrier.Target"], []) { InformationTemplates = Reports[SourceOwner].InformationTemplates };
        }

        internal void AddRegistration(string path, string theorem = Theorem, bool declared = true)
        {
            AddEmpty(path);
            var module = InformationTemplateEvidence.ModuleForSource(path);
            var template = Report(Files(), count: 1, declared: declared).Files[RepoPath.CreateKnown(Registration)];
            var wire = JsonNode.Parse(template.InformationTemplates!.Value.GetRawText().Replace(
                Registration, path, StringComparison.Ordinal).Replace("D5.S0.Carrier.Registration", module, StringComparison.Ordinal)
                .Replace("D5.S0.Carrier.Target.target0", theorem, StringComparison.Ordinal))!;
            Reports[path] = Reports[path] with
            {
                InformationTemplates = JsonSerializer.SerializeToElement(wire),
                Declarations = [new(theorem + ".unit", "def", "True", [])],
            };
            if (!Reports[SourceOwner].Declarations.Any(d => d.Name == theorem + ".realization"))
                Reports[SourceOwner] = Reports[SourceOwner] with { Declarations = Reports[SourceOwner].Declarations.Add(new(theorem + ".realization", "def", "True", [])) };
        }

        internal void AddSidecar(string path, string owner)
        {
            // Synthetic wire follows moduleJson: originals in M, only the claim in S.
            AddRegistration(path);
            var claim = JsonSerializer.SerializeToNode(Reports[path].InformationTemplates)!["records"]![0]!.DeepClone();
            var original = JsonSerializer.SerializeToNode(Reports[owner].InformationTemplates)!["records"]![0]!;
            claim["key"] = original["key"]!.DeepClone();
            claim["certificate"]!["key"] = original["key"]!.DeepClone();
            claim["registration_source_path"] = owner;
            AddEmpty(path);
            Import(path, owner);
            Mutate(path, wire => wire["records"]!.AsArray().Add(claim));
        }

        internal void Change(string path) { After[path] += "-- changed\n"; Changes.Add(path); }
        internal void Import(string owner, string dependency)
        {
            var module = InformationTemplateEvidence.ModuleForSource(dependency);
            Reports[owner] = Reports[owner] with { Imports = Reports[owner].Imports.Add(module) };
            Before[owner] = After[owner] = Before[owner] + "import " + module + "\n";
        }
        internal void Mutate(string path, Action<JsonNode> change)
        {
            var wire = JsonSerializer.SerializeToNode(Reports[path].InformationTemplates)!;
            change(wire);
            Reports[path] = Reports[path] with { InformationTemplates = JsonSerializer.SerializeToElement(wire) };
        }
        internal DeltaRuleContext Context()
        {
            var snapshot = Tree(After);
            var report = RawLeanReportArtifact.Read(RawLeanReportArtifact.Write(snapshot,
                LeanAxiomReport.Create(Reports)).AsSpan(), snapshot);
            return DeclaredTemplateReviewTests.Context(Before, After, report, Changes.ToArray());
        }
        internal ImmutableArray<RuleFinding> Findings() => DeclaredTemplateBindingRule.Evaluate(Context());
    }
}
