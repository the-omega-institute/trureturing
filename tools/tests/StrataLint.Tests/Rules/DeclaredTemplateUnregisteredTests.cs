using System.Collections.Immutable;
using System.Runtime.CompilerServices;
using System.Text;
using System.Text.Json;
using StrataLint.Engine;
using static StrataLint.Tests.DeclaredTemplateReviewTests;

namespace StrataLint.Tests;

public sealed class DeclaredTemplateUnregisteredTests
{
    private const string Target = DeclaredTemplateReviewTests.Target;
    internal const string Theorem = "D5.S0.Carrier.Target.target0";
    private const string Source = "namespace D5.S0.Carrier.Target\ntheorem target0 : True := by trivial\nend D5.S0.Carrier.Target\n";

    [Fact]
    public void new_public_theorem_without_registration_blocks() => Block(Build());

    [Fact]
    public void validated_readout_registration_covers_new_theorem() => Declared(Build(binding: "inline"));

    [Fact]
    public void validated_sidecar_covers_new_theorem() => Declared(Build(binding: "sidecar"));

    [Fact]
    public void registration_in_another_module_covers_new_theorem() => Declared(Build(binding: "foreign"));

    [Theory]
    [InlineData("theorem")]
    [InlineData("lemma")]
    public void same_name_in_base_is_not_new(string keyword) =>
        Empty(Build(baseline: Source.Replace("theorem", keyword, StringComparison.Ordinal)));

    [Fact]
    public void new_private_theorem_is_exempt() => Empty(Build(
        source: Source.Replace("theorem", "private theorem", StringComparison.Ordinal),
        declarations: [new("_private.D5.S0.Carrier.Target.0." + Theorem, "theorem", "True", [])]));

    [Theory]
    [InlineData("def", "def")]
    [InlineData("instance", "def")]
    [InlineData("instance", "theorem")]
    [InlineData("abbrev", "def")]
    [InlineData("structure", "inductive")]
    public void non_theorem_source_declarations_are_exempt(string keyword, string kind) => Empty(Build(
        source: Source.Replace("theorem", keyword, StringComparison.Ordinal),
        declarations: [new(Theorem, kind, "True", [])]));

    [Theory]
    [InlineData("def")]
    [InlineData("opaque")]
    [InlineData("inductive")]
    [InlineData("constructor")]
    [InlineData("recursor")]
    [InlineData("axiom")]
    public void non_theorem_report_kinds_are_exempt_without_source(string kind) => Empty(Build(
        source: "-- generated non-theorem declarations\n", declarations: [new(Theorem, kind, "True", [])]));

    [Fact]
    public void internal_detail_theorems_are_exempt() => Empty(Build(
        declarations: [new(Theorem + ".proof_1", "theorem", "True", []) { IncludeInStatement = false }]));

    [Fact]
    public void generated_occurrence_and_seal_companions_are_exempt() => Empty(Build(source: "-- generated companions\n",
        declarations: [new(Theorem + ".«root/arena/catalog».__lowers_escape", "theorem", "True", []),
            new(Theorem + "__information_unit", "def", "True", []),
            new(Theorem + "__catalog_irredundant", "theorem", "True", [])]));

    [Fact]
    public void generated_equation_and_congruence_companions_are_exempt() => Empty(Build(
        source: "-- Lean compiler generated companions\n",
        declarations: [new(Theorem + ".eq_def", "theorem", "True", []) { IsGeneratedCompanion = true },
            new(Theorem + ".congr_simp", "theorem", "True", []) { IsGeneratedCompanion = true }]));

    [Fact]
    public void actual_compiler_companions_survive_publication_and_strict_loader_to_dtr()
    {
        using var output = new TemporaryDirectory();
        var root = TestRepositoryLayout.FindRoot();
        var run = TestProcessRunner.Run("env",
            ["STRATALINT_NATIVE_RESULT_DIR=" + output.Path, "python3", "-B", "-m", "unittest",
                "test_native.NativeTests.test_generated_companions", "-v"],
            Path.Combine(root, "tools/lean-inspector/tests"), TestBudgets.ReportSupervisorHangGuard, 1024 * 1024);
        Assert.True(run.ExitCode == 0, Encoding.UTF8.GetString(run.StandardOutput)
            + Encoding.UTF8.GetString(run.StandardError));
        var published = Path.Combine(output.Path, "test_generated_companions/published");
        var files = new Dictionary<string, string>(StringComparer.Ordinal);
        files["lean-report-inputs.json"] = File.ReadAllText(Path.Combine(published, "lean-report-inputs.json"));
        foreach (var path in Directory.EnumerateFiles(published, "*.lean", SearchOption.AllDirectories))
            files[Path.GetRelativePath(published, path).Replace('\\', '/')] = File.ReadAllText(path);
        var report = RawLeanReportArtifact.ReadFile(Path.Combine(published, "public.json"), Tree(files));
        var declarations = report.Files.Single(p => p.Key.Value == Target).Value.Declarations;
        using var result = JsonDocument.Parse(File.ReadAllText(Path.Combine(published, "result.json")));
        string[] Names(string key) => result.RootElement.GetProperty(key).EnumerateArray()
            .Select(n => "D5.S0.Carrier.Target." + n.GetString()).ToArray();
        var generated = Names("generated");
        var controls = Names("controls");
        var unclassified = Names("unclassified");
        Assert.Equal(8, generated.Length);
        Assert.Equal(10, controls.Length);
        Assert.All(generated, n => Assert.True(declarations.Single(d => d.Name == n).IsGeneratedCompanion));
        Assert.All(controls, n => Assert.False(declarations.Single(d => d.Name == n).IsGeneratedCompanion));
        Assert.All(unclassified, n => Assert.False(declarations.Single(d => d.Name == n).IsGeneratedCompanion));
        // Empty registration inventories come from the rule fixture. All
        // declaration metadata and material identities come from actual Lean
        // extraction, native compaction/publication and the strict reader.
        var findings = Findings(Build(source: files[Target], declarations: declarations.ToArray()));
        Assert.Equal(controls.Concat(unclassified).Order(StringComparer.Ordinal), findings.Select(f =>
            f.Message.Replace("DTR-Unregistered D5.S0.Carrier.Target/", "", StringComparison.Ordinal))
            .Order(StringComparer.Ordinal));
        Assert.All(findings, f => Assert.Equal(AdmissionEffect.Block, f.Effect));
        files[Target] += "-- stale report\n";
        Assert.Throws<FormatException>(() => RawLeanReportArtifact.ReadFile(
            Path.Combine(published, "public.json"), Tree(files)));
    }

    [Theory]
    [InlineData("eq_def")]
    [InlineData("congr_simp")]
    public void authored_companion_suffix_is_selected_even_with_generated_origin(string suffix)
    {
        var theorem = Theorem + "." + suffix;
        Block(Build(
            source: Source.Replace("target0", "target0." + suffix, StringComparison.Ordinal),
            declarations: [new(theorem, "theorem", "True", []) { IsGeneratedCompanion = true }]), theorem);
    }

    [Theory]
    [InlineData("eq_def")]
    [InlineData("congr_simp")]
    public void unknown_companion_origin_remains_selected(string suffix)
    {
        var theorem = Theorem + "." + suffix;
        Block(Build(source: "-- unknown declaration provenance\n",
            declarations: [new(theorem, "theorem", "True", [])]), theorem);
    }

    [Fact]
    public void handwritten_companion_suffix_does_not_exempt_theorem() => Block(Build(
        source: Source.Replace("target0", "target0__catalog_irredundant", StringComparison.Ordinal),
        declarations: [new(Theorem + "__catalog_irredundant", "theorem", "True", [])]), Theorem + "__catalog_irredundant");

    [Fact]
    public void unselected_new_theorem_and_malformed_evidence_are_not_judged() => Empty(Build(selected: false, malformed: true));

    [Fact]
    public void candidate_new_module_judges_every_public_theorem()
    {
        var findings = Findings(Build(added: true, declarations:
            [new(Theorem, "theorem", "True", []), new(Theorem + "_second", "theorem", "True", [])]));
        Assert.True(findings.Count(f => f.Message.StartsWith("DTR-Unregistered ", StringComparison.Ordinal)
            && f.Effect == AdmissionEffect.Block) == 2, "[FAIL] candidate_new_module_judges_every_public_theorem");
    }

    [Fact]
    public void lemma_is_a_public_theorem() => Block(Build(source: Source.Replace("theorem", "lemma", StringComparison.Ordinal)));

    [Fact]
    public void first_pin_uses_base_theorem_names() => Empty(Build(baseline: Source, firstPin: true));

    [Fact]
    public void rename_destination_has_no_same_path_base_theorem() => Block(Build(added: true, renamed: true));

    [Theory]
    [InlineData("-- theorem D5.S0.Carrier.Target.target0 : True := by trivial\n")]
    [InlineData("/- outer /- nested -/ theorem D5.S0.Carrier.Target.target0 : True := by trivial -/\n")]
    [InlineData("def text := \"theorem D5.S0.Carrier.Target.target0 : True := by trivial\"\n")]
    [InlineData("namespace Other\ntheorem target0 : True := by trivial\nend Other\n")]
    [InlineData("def D5.S0.Carrier.Target.target0 : True := by trivial\n")]
    public void nonmatching_base_text_does_not_grandfather_theorem(string baseline) => Block(Build(baseline: baseline));

    [Theory]
    [InlineData("namespace D5\nnamespace S0.Carrier.Target\n  lemma target0 : True := by trivial\nend S0.Carrier.Target\nend D5\n")]
    [InlineData("namespace Other\ntheorem _root_.D5.S0.Carrier.Target.target0 : True := by trivial\nend Other\n")]
    public void qualified_base_names_are_resolved(string baseline) => Empty(Build(baseline: baseline));

    [Theory]
    [InlineData("namespace D5.S0.Carrier.Target\nlemma «target0» : True := by trivial\nend D5.S0.Carrier.Target\n")]
    [InlineData("def quote := '\"'\ntheorem D5.S0.Carrier.Target.target0 : True := by trivial\n")]
    public void quoted_identifiers_and_character_literals_preserve_base_names(string baseline) => Empty(Build(baseline: baseline));

    [Theory]
    [InlineData("r#")]
    [InlineData("r##")]
    public void raw_string_contents_are_not_base_declarations(string prefix) => Block(Build(
        baseline: "def text := " + prefix + "\" \" theorem " + Theorem + " : True := by trivial \" \"" + prefix[1..] + "\n"));

    [Theory]
    [InlineData("s!")]
    [InlineData("m!")]
    public void interpolated_string_contents_are_not_base_declarations(string prefix) => Block(Build(
        baseline: "def text := " + prefix + "\"{id \" theorem " + Theorem + " : True := by trivial \"}\"\n"));

    [Fact]
    public void supplementary_unicode_base_name_is_existing() => Empty(Build(
        baseline: "theorem 𝒳 : True := by trivial\n", source: "theorem 𝒳 : True := by trivial\n",
        declarations: [new("𝒳", "theorem", "True", [])]));

    [Fact]
    public void unvalidated_registration_does_not_cover_new_theorem() => Block(Build(binding: "undeclared"));

    [Fact]
    public void registration_for_other_theorem_does_not_cover_new_theorem() => Block(Build(binding: "inline",
        declarations: [new(Theorem + "_second", "theorem", "True", [])]), Theorem + "_second");

    [Fact]
    public void unrelated_foreign_records_cannot_fail_selected_theorem() => Declared(Build(binding: "foreign", malformed: true));

    [Fact]
    public void sl031_dispatch_blocks_unregistered_theorem()
    {
        var diagnostics = RuleCatalog.Default.EvaluateSingle(UtilityAdmissionTestSupport.UtilityRuleId, Build()).Diagnostics;
        Assert.True(diagnostics.Any(d => d.Message == "DTR-Unregistered D5.S0.Carrier.Target/" + Theorem
            && d.AdmissionEffect == AdmissionEffect.Block), "[FAIL] sl031_dispatch_blocks_unregistered_theorem");
    }

    internal static ImmutableArray<RuleFinding> Findings(DeltaRuleContext context) => DeclaredTemplateBindingRule.Evaluate(context);
    private static void Empty(DeltaRuleContext context, [CallerMemberName] string name = "") =>
        Assert.True(Findings(context).IsEmpty, "[FAIL] " + name + ": " + string.Join("; ", Findings(context).Select(f => f.Message)));
    private static void Block(DeltaRuleContext context, string theorem = Theorem, [CallerMemberName] string name = "") =>
        Assert.True(Findings(context).Any(f => f.Message == "DTR-Unregistered D5.S0.Carrier.Target/" + theorem
            && f.Effect == AdmissionEffect.Block), "[FAIL] " + name);
    private static void Declared(DeltaRuleContext context, [CallerMemberName] string name = "")
    {
        var findings = Findings(context);
        Assert.True(findings.Any(f => f.Message.StartsWith("DTR-Declared ", StringComparison.Ordinal)
            && f.Effect == AdmissionEffect.Observe) && findings.All(f => f.Effect == AdmissionEffect.Observe),
            "[FAIL] " + name + ": " + string.Join("; ", findings.Select(f => f.Message)));
    }

    internal static DeltaRuleContext Build(string? baseline = null, string source = Source, string binding = "none",
        bool selected = true, bool added = false, bool firstPin = false, bool renamed = false, bool malformed = false,
        LeanDeclaration[]? declarations = null)
    {
        var before = Files();
        before[Target] = baseline ?? "-- no previous theorem\n";
        var after = new Dictionary<string, string>(before) { [Target] = source + (firstPin ? "" : "-- candidate\n") };
        if (!selected) before[Target] = after[Target];
        if (renamed) before["D5/S0/Carrier/Old.lean"] = Source;
        if (added) before.Remove(Target);
        var changes = selected ? new[] { Target } : new[] { Judge };
        if (firstPin)
        {
            const string pin = "Golden/Frozen/state/D5/S0/Carrier/Target.lean.json";
            after[pin] = "{}\n";
            changes = [pin];
        }
        var owner = binding == "foreign" ? Registration : Target;
        var ownerModule = InformationTemplateEvidence.ModuleForSource(owner);
        var key = new InformationOccurrenceKey(ownerModule, ownerModule, Theorem, ownerModule + ".arena", ownerModule + ".catalog");
        var reports = Report(after, count: 0).Files.ToDictionary(p => p.Key.Value, p => p.Value);
        reports[Target] = reports[Target] with { Declarations = (declarations ?? [new(Theorem, "theorem", "True", [])]).ToImmutableArray() };
        var registered = binding != "none";
        if (registered)
        {
            reports[owner] = reports[owner] with { Declarations = reports[owner].Declarations.Add(new(Theorem + ".unit", "def", "True", [])) };
            reports[Target] = reports[Target] with { Declarations = reports[Target].Declarations.Add(new(Theorem + ".realization", "def", "True", [])) };
        }
        var inputs = after.Where(p => p.Key == Target || p.Key == Registration || PolicyFiles().ContainsKey(p.Key))
            .OrderBy(p => p.Key, StringComparer.Ordinal).Select(p => new { path = p.Key, sha256 = Hash(p.Value) }).ToArray();
        object Record(string producer, bool validated) => new
        {
            key = InformationTemplateJson.KeyJson(key), registration_source_path = owner, statement_identity = Hash(Theorem),
            content_inputs = inputs.Where(i => i.path == Target || i.path == owner).ToArray(),
            binding_source_path = validated ? producer : null, state = validated ? "declared_validated" : "undeclared",
            diagnostic = validated ? null : $"IE-C050 ClosedTruthReadout key={key.Root}/{key.Catalog}/{key.Theorem} "
                + "reason=unclassified_form rule=dtr.missing_declaration site=\"\" readout=\"\" "
                + "provenance={\"argument_inputs\":[],\"extraction_inputs\":[],\"plan_identity\":null,"
                + "\"rule\":\"dtr.missing_declaration\",\"site\":\"\",\"template_key\":null}",
            escape_from = DeclaredTemplateEscapeRecordTests.FromSlot,
            escape_continues = DeclaredTemplateEscapeRecordTests.OpenSlot, bridge_kind = "legacy",
            unit_name = Theorem + ".unit", realization_name = Theorem + ".realization",
            certificate = validated ? new { key = InformationTemplateJson.KeyJson(key), evidence_ref = Hash("evidence"),
                plan_identity = Hash("plan"), descriptor_identity = Hash("descriptor"), actual_identity = Hash("actual"),
                argument_inputs = Array.Empty<object>(), extraction_inputs = Array.Empty<object>() } : null,
        };
        foreach (var path in new[] { Target, Registration })
        {
            var own = registered && owner == path;
            var records = new List<object>();
            if (own) records.Add(Record(path, binding is "inline" or "foreign"));
            if (binding == "sidecar" && path == Registration) records.Add(Record(path, true));
            if (malformed && path == Registration) records.Add(new { key = new { theorem = "Other.unrelated" }, certificate = "malformed" });
            reports[path] = reports[path] with { InformationTemplates = JsonSerializer.SerializeToElement(new
            {
                schema_version = 1, compatibility_version = ManifestVersion(after), inputs,
                inventory = own ? new[] { InformationTemplateJson.KeyJson(key) } : [],
                registered = own ? new[] { InformationTemplateJson.KeyJson(key) } : [], records,
            }) };
        }
        if (malformed && !selected) reports[Target] = reports[Target] with { InformationTemplates = JsonSerializer.SerializeToElement("malformed") };
        var snapshot = Tree(after);
        var report = RawLeanReportArtifact.Read(RawLeanReportArtifact.Write(snapshot, LeanAxiomReport.Create(reports)).AsSpan(), snapshot);
        return Context(before, after, report, changes);
    }

    private static string Hash(string text) => InformationTemplateJson.Sha256(Encoding.UTF8.GetBytes(text));
}
