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
