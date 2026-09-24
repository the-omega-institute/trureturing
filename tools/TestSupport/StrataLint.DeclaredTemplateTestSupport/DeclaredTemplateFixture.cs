using static StrataLint.TestSupport.InformationTemplateFixture;
using System.Collections.Immutable;
using System.Text;
using System.Text.Json;
using StrataLint.Engine;
using Trureturing.Truth;

namespace StrataLint.TestSupport;

// Wire fixtures model two imported-theorem registrations. They exercise the
// production reader and dispatch; they make no kernel-proof claim.
internal static class DeclaredTemplateFixture
{
    internal const string Registration = "D5/S0/Carrier/Registration.lean";
    internal const string Target = "D5/S0/Carrier/Target.lean";
    internal const string Judge = "tools/lean-inspector/LeanInformationAudit/Registry/Assessment.lean";
    private const string Module = "D5.S0.Carrier.Registration";
    internal const string TargetModule = "D5.S0.Carrier.Target";
    internal static Dictionary<string, string> Files()
    {
        var files = PolicyFiles();
        files[Judge] = "-- judge implementation\n";
        var engineering = System.Text.Json.Nodes.JsonNode.Parse(EngineeringRegistrationFixture.Manifest())!;
        engineering["rule_build_inputs"] = JsonSerializer.SerializeToNode(new[] { Judge });
        files[EngineeringRegistrationFixture.Path] = engineering.ToJsonString();
        files[Registration] = "import D5.S0.Carrier.Target\nimport LeanInformationAudit.Syntax\n";
        files[Target] = "-- synthetic imported theorem source\n";
        files[AdmissionPlanePolicy.FileMapPath] = "schema_version = 2\ninclude = [\"FILEMAP.inputs.toml\"]\n";
        files["Meta/FILEMAP.inputs.toml"] = "schema_version = 2\nfiles = [\n" + string.Join("\n",
            new[] { ("D5/**", "content"), ("Meta/**", "judge"), ("tools/**", "judge") }
                .Select(pair => "{ pattern = \"" + pair.Item1 + "\", admission_plane = \"" + pair.Item2
                    + "\", kind = \"data\", produced_by = \"none\", consumed_by = [\"StrataLint\"], "
                    + "verified_by = [\"StrataLint\"], artifact_id = \"none\", runtime_disposition = \"committed-source\" },"))
            + "\n]\n";
        return files;
    }

    internal static RepositorySnapshot Tree(Dictionary<string, string> files) =>
        Assert.IsType<SnapshotDecodeOutcome.Decoded>(SnapshotDecoder.Decode(
            RawRepositorySnapshot.Create(files.Select(p => RawRepositoryEntry.FromText(p.Key, p.Value))))).Snapshot;
    internal static string Text(ImmutableArray<byte> bytes) => Encoding.UTF8.GetString(bytes.AsSpan());
    private static string Hash(string text) => InformationTemplateJson.Sha256(Encoding.UTF8.GetBytes(text));
    internal static InformationOccurrenceKey Key(int n) => new(Module, Module, TargetModule + ".target" + n,
        Module + ".arena", Module + ".catalog");
    internal static LeanAxiomReport Report(Dictionary<string, string> files, int count = 2,
        bool declared = false, bool indirectJudgePath = false)
    {
        var snapshot = Tree(files);
        var keys = Enumerable.Range(0, count).Select(Key).ToArray();
        var reports = new Dictionary<string, LeanFileReport>();
        foreach (var path in new[] { Registration, Target })
        {
            var own = path == Registration ? keys : [];
            var wire = JsonSerializer.SerializeToElement(new
            {
                schema_version = 1, compatibility_version = ManifestVersion(files),
                inventory = own.Select(InformationTemplateJson.KeyJson),
                registered = own.Select(InformationTemplateJson.KeyJson),
                records = own.Select(key => new
                {
                    key = InformationTemplateJson.KeyJson(key), registration_source_path = Registration,
                    statement_identity = Hash(key.Theorem),
                    binding_source_path = declared ? Registration : null,
                    state = declared ? "declared_validated" : "undeclared",
                    diagnostic = declared ? null : $"IE-C050 ClosedTruthReadout key={key.Root}/{key.Catalog}/{key.Theorem} "
                        + "reason=unclassified_form rule=dtr.missing_declaration site=\"\" readout=\"\" "
                        + "provenance={\"argument_inputs\":[],\"extraction_inputs\":[],\"plan_identity\":null,"
                        + "\"rule\":\"dtr.missing_declaration\",\"site\":\"\",\"template_key\":null}",
                    escape_from = InformationTemplateFixture.FromSlot,
                    escape_continues = InformationTemplateFixture.OpenSlot, bridge_kind = "legacy",
                    unit_name = key.Theorem + ".unit", realization_name = key.Theorem + ".realization",
                    certificate = declared ? new
                    {
                        key = InformationTemplateJson.KeyJson(key), evidence_ref = Hash("evidence"),
                        plan_identity = Hash("plan"), descriptor_identity = Hash("descriptor"), actual_identity = Hash("actual"),
                        argument_inputs = Array.Empty<object>(), extraction_inputs = Array.Empty<object>(),
                    } : null,
                }),
            });
            var declarations = keys.Select(key => new LeanDeclaration(key.Theorem +
                (path == Registration ? ".unit" : ".realization"), "def", "True", [])).ToImmutableArray();
            string[] imports = path == Registration
                ? indirectJudgePath
                    ? ["LeanInformationAudit.Syntax"]
                    : [TargetModule, "LeanInformationAudit.Syntax"]
                : [];
            reports[path] = new(imports.ToImmutableArray(), declarations)
            { InformationTemplates = wire, InformationRegistrationErrors = [] };
        }
        if (indirectJudgePath)
            reports["tools/lean-inspector/LeanInformationAudit/Syntax.lean"] =
                new([TargetModule], []);
        var report = LeanAxiomReport.Create(reports);
        // Round-trip canonical raw bytes for every fixture, including the
        // indirect judge-import case. Admission never receives hand-attached
        // InformationTemplates in place of the production raw artifact loader.
        return RawLeanReportArtifact.Read(RawLeanReportArtifact.Write(snapshot, report).AsSpan(), snapshot);
    }

    internal static DeltaRuleContext Context(Dictionary<string, string> baseline, Dictionary<string, string> head,
        LeanAxiomReport report, string[] changes)
    {
        var prototype = new RuleFixture().Build();
        return DeltaRuleContext.Create(Tree(head), Tree(baseline), prototype.Policy,
            AcceptedLeanClosure.Create(report), RawChangeSet.Create(changes), prototype.MetaEvaluation);
    }

}
