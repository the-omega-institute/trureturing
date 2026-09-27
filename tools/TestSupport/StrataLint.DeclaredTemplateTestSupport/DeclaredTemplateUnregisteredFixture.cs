using static StrataLint.TestSupport.InformationTemplateFixture;
using System.Collections.Immutable;
using System.Runtime.CompilerServices;
using System.Text;
using System.Text.Json;
using StrataLint.Engine;
using static StrataLint.TestSupport.DeclaredTemplateFixture;

namespace StrataLint.TestSupport;

internal static class DeclaredTemplateUnregisteredFixture
{
    internal const string Target = DeclaredTemplateFixture.Target;
    internal const string Theorem = "D5.S0.Carrier.Target.target0";
    internal const string Source = "namespace D5.S0.Carrier.Target\ntheorem target0 : True := by trivial\nend D5.S0.Carrier.Target\n";
    internal const string TwoTheoremSource = "namespace D5.S0.Carrier.Target\ntheorem target0 : True := by trivial\n"
        + "theorem target0_second : True := by trivial\nend D5.S0.Carrier.Target\n";

    internal static ImmutableArray<RuleFinding> Findings(DeltaRuleContext context) => DeclaredTemplateBindingRule.Evaluate(context);

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
        const string mirror = "Reg/" + Target;
        var ownerMirror = binding is "mirror" or "undeclared";
        var owner = binding == "foreign" ? Registration : ownerMirror ? mirror : Target;
        var ownerModule = InformationTemplateEvidence.ModuleForSource(owner);
        var key = new InformationOccurrenceKey(ownerModule, ownerModule, Theorem, ownerModule + ".arena", ownerModule + ".catalog");
        var reports = Report(after, count: 0).Files.ToDictionary(p => p.Key.Value, p => p.Value);
        if (ownerMirror)
        {
            before[mirror] = after[mirror] = "import D5.S0.Carrier.Target\n";
            after["lean-report-inputs.json"] = before["lean-report-inputs.json"] = before["lean-report-inputs.json"]
                .Replace("\"D5/**/*.lean\"", "\"**/*.lean\"", StringComparison.Ordinal);
        }
        if (ownerMirror) reports[mirror] = new(["D5.S0.Carrier.Target"], []);
        reports[Target] = reports[Target] with { Declarations = (declarations ?? [new(Theorem, "theorem", "True", [])]).ToImmutableArray() };
        var registered = binding != "none";
        if (registered)
        {
            reports[owner] = reports[owner] with { Declarations = reports[owner].Declarations.Add(new(Theorem + ".unit", "def", "True", [])) };
            reports[Target] = reports[Target] with { Declarations = reports[Target].Declarations.Add(new(Theorem + ".realization", "def", "True", [])) };
        }
        object Record(string producer, bool validated) => new
        {
            key = InformationTemplateJson.KeyJson(key), registration_source_path = owner, statement_identity = Hash(Theorem),
            binding_source_path = validated ? producer : null, state = validated ? "declared_validated" : "undeclared",
            diagnostic = validated ? null : $"IE-C050 ClosedTruthReadout key={key.Root}/{key.Catalog}/{key.Theorem} "
                + "reason=unclassified_form rule=dtr.missing_declaration site=\"\" readout=\"\" "
                + "provenance={\"argument_inputs\":[],\"extraction_inputs\":[],\"plan_identity\":null,"
                + "\"rule\":\"dtr.missing_declaration\",\"site\":\"\",\"template_key\":null}",
            escape_from = InformationTemplateFixture.FromSlot,
            escape_continues = InformationTemplateFixture.OpenSlot, bridge_kind = "legacy",
            unit_name = Theorem + ".unit", realization_name = Theorem + ".realization",
            certificate = validated ? new { key = InformationTemplateJson.KeyJson(key), evidence_ref = Hash("evidence"),
                plan_identity = Hash("plan"), descriptor_identity = Hash("descriptor"), actual_identity = Hash("actual"),
                argument_inputs = Array.Empty<object>(), extraction_inputs = Array.Empty<object>() } : null,
        };
        foreach (var path in ownerMirror ? new[] { Target, Registration, mirror } : new[] { Target, Registration })
        {
            var own = registered && owner == path;
            var records = new List<object>();
            if (own) records.Add(Record(path, binding is "inline" or "foreign" or "mirror"));
            if (binding == "sidecar" && path == Registration) records.Add(Record(path, true));
            if (malformed && path == Registration) records.Add(new { key = new { theorem = "Other.unrelated" }, certificate = "malformed" });
            reports[path] = reports[path] with { InformationTemplates = JsonSerializer.SerializeToElement(new
            {
                schema_version = 1, compatibility_version = ManifestVersion(after),
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
