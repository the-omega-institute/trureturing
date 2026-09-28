using System.Collections.Immutable;
using System.Text.Json;
using System.Text.Json.Nodes;
using StrataLint.Engine;

namespace StrataLint.DeclaredTemplate.Tests;

[Collection("Lean cache environment")]
public sealed class InstanceSupportEvidenceTests
{
    [Fact]
    public void support_material_navigation_preserves_utf8_names_and_debruijn_context()
    {
        var name = "C,(λ😀)";
        var atom = System.Text.Encoding.UTF8.GetByteCount(name) + ":" + name;
        var domain = "ea(ec(ns(n0," + atom + "),[l0]),eb(0))";
        var material = "statement-v1(uparams=[ns(n0,7:u,type=)],type="
            + "ep(bd,es(ls(l0)),ep(bc," + domain + ",ec(ns(n0,4:True),[]))))";
        var binding = JsonSerializer.SerializeToElement(new { support_entries = new[] {
            new { path = new[] { "body", "body" }, material = domain } } });
        var declaration = new LeanDeclaration("fixture", "theorem", material, []);
        InformationTemplateSourceMaterial.Check(binding, declaration);
        Assert.Throws<FormatException>(() => InformationTemplateSourceMaterial.Check(binding,
            declaration with { TypeRepresentation = material.Replace("ep(bc,", "ep(bd,", StringComparison.Ordinal) }));
        Assert.Throws<FormatException>(() => InformationTemplateSourceMaterial.Check(binding,
            declaration with { TypeRepresentation = material.Replace("eb(0)", "eb(1)", StringComparison.Ordinal) }));
    }

    [Fact]
    public void named_support_material_instantiates_only_admitted_universe_names()
    {
        static string Name(string value) => "ns(n0," + System.Text.Encoding.UTF8.GetByteCount(value) + ":" + value + ")";
        var original = Name("λ,😀");
        var parameter = Name("u,type=");
        var domain = "ea(ec(ns(n0,7:Fintype),[lp(" + original + ")]),eb(0))";
        var body = "ep(bd,es(ls(lp(" + original + "))),ep(bc," + domain + ",ec(ns(n0,4:True),[])))";
        var definition = new LeanDeclaration("claim", "def",
            "statement-v1(uparams=[" + original + "],type=es(l0),value=" + body + ")", []);
        var theorem = new LeanDeclaration("result", "theorem",
            "statement-v1(uparams=[" + parameter + "],type=ec(ns(n0,5:claim),[lp(" + parameter + ")]))", []);
        var binding = JsonSerializer.SerializeToElement(new {
            definition_entry = new { path = Array.Empty<string>() },
            support_entries = new[] { new { path = new[] { "body", "body" },
                material = domain.Replace(original, parameter, StringComparison.Ordinal) } }
        });
        InformationTemplateSourceMaterial.Check(binding, theorem, definition);
        Assert.Throws<FormatException>(() => InformationTemplateSourceMaterial.Check(binding, theorem));
        Assert.Throws<FormatException>(() => InformationTemplateSourceMaterial.Check(binding, theorem,
            definition with { TypeRepresentation = definition.TypeRepresentation.Replace("eb(0)", "eb(1)", StringComparison.Ordinal) }));
    }

    [Fact]
    public void native_fintype_support_passes_strict_material_and_import_join()
    {
        using var temporary = new TemporaryDirectory();
        var root = TestRepositoryLayout.FindRoot();
        var produced = TestProcessRunner.Run("/bin/bash", ["tools/scripts/worktree/lean-cache-run.sh", "python3", "-B",
            Path.Combine(root, "tools/lean-inspector/tests/test_instance_support.py"), temporary.Path],
            root, TestBudgets.ReportSupervisorHangGuard, 1024 * 1024);
        Assert.True(produced.ExitCode == 0, System.Text.Encoding.UTF8.GetString(produced.StandardOutput)
            + System.Text.Encoding.UTF8.GetString(produced.StandardError));
        var reportPath = Path.Combine(temporary.Path, "raw-lean-report.json");
        var fixture = File.ReadAllText(Path.Combine(root,
            "tools/lean-inspector/LeanInformationAuditRegTests/InstanceSupportNative.lean"));
        string FixtureInput(string name)
        {
            var marker = "def " + name + " : String := r####\"";
            var start = fixture.IndexOf(marker, StringComparison.Ordinal) + marker.Length;
            var end = fixture.IndexOf("\"####", start, StringComparison.Ordinal);
            return fixture[start..end];
        }
        var sourceRoot = Path.Combine(Path.GetDirectoryName(reportPath!)!, "sources");
        using var document = JsonDocument.Parse(File.ReadAllBytes(reportPath!));
        var entries = document.RootElement.GetProperty("modules").EnumerateArray().Select(row =>
        {
            var path = row.GetProperty("source_path").GetString()!;
            var source = File.ReadAllBytes(Path.Combine(sourceRoot, path));
            Assert.Equal(FixtureInput(path.StartsWith("Reg/", StringComparison.Ordinal) ? "registration" : "source"),
                System.Text.Encoding.UTF8.GetString(source));
            return new RawRepositoryEntry(path, ImmutableArray.CreateRange(source));
        }).Append(new RawRepositoryEntry("lean-report-inputs.json",
            ImmutableArray.CreateRange(File.ReadAllBytes(Path.Combine(root, "lean-report-inputs.json")))));
        var snapshot = Assert.IsType<SnapshotDecodeOutcome.Decoded>(SnapshotDecoder.Decode(
            RawRepositorySnapshot.Create(entries))).Snapshot;
        var report = RawLeanReportArtifact.ReadFile(reportPath!, snapshot, validateMaterials: true);
        using var encodingControls = JsonDocument.Parse(File.ReadAllBytes(
            Path.Combine(temporary.Path, "binding-identity-controls.json")));
        Assert.Equal(2, encodingControls.RootElement.GetArrayLength());
        foreach (var control in encodingControls.RootElement.EnumerateArray())
            InformationTemplateBindingIdentity.Check(control, report.Files.Values.SelectMany(f => f.Declarations));
        var path = RepoPath.CreateKnown("Reg/D5/InstanceSupportFixture.lean");
        var evidence = InformationTemplateEvidence.Collect(snapshot, report, [path]);
        Assert.Equal(11, evidence.Occurrences.Count);
        var rejectedNames = new[] { "eqSource", "swapLambdaSource", "swapSigmaSource" };
        var rejected = evidence.Occurrences.Where(pair => rejectedNames.Contains(pair.Key.Theorem.Split('.').Last())).ToArray();
        Assert.Equal(3, rejected.Length);
        Assert.All(rejected, pair => Assert.Equal(InformationTemplateBindingState.DeclaredUnresolved, pair.Value.State));
        Assert.All(evidence.Occurrences.Except(rejected).Select(pair => pair.Value), entry => {
            Assert.Equal(InformationTemplateBindingState.DeclaredValidated, entry.State);
            Assert.True(entry.HasFourSlots);
        });
        var occurrence = evidence.Occurrences.Single(pair => pair.Key.Theorem == "D5.InstanceSupportFixture.source").Value;
        Assert.Equal(InformationTemplateBindingState.DeclaredValidated, occurrence.State);
        Assert.True(occurrence.HasFourSlots);
        var binding = occurrence.SourceBinding!.Value;
        Assert.Equal(3, binding.GetProperty("telescope_size").GetInt32());
        Assert.Equal(new[] { 0 }, binding.GetProperty("coordinates").EnumerateArray().Select(x => x.GetInt32()));
        Assert.Equal(new[] { 1 }, binding.GetProperty("support").EnumerateArray().Select(x => x.GetInt32()));
        Assert.Equal(new[] { 0, 1 }, binding.GetProperty("parameter_slots").EnumerateArray().Select(x => x.GetInt32()));
        var support = Assert.Single(binding.GetProperty("support_entries").EnumerateArray());
        Assert.Equal("ea(ec(ns(n0,7:Fintype),[l0]),eb(0))", support.GetProperty("material").GetString());
        foreach (var file in report.Files.Values)
            foreach (var declaration in file.Declarations)
                Assert.All(declaration.Axioms, axiom => Assert.Contains(axiom,
                    new[] { "propext", "Classical.choice", "Quot.sound" }));

        var transitive = evidence.Occurrences.Single(pair => pair.Key.Theorem.EndsWith(".transitiveSource", StringComparison.Ordinal))
            .Value.SourceBinding!.Value;
        Assert.Equal(new[] { 1, 2 }, transitive.GetProperty("support").EnumerateArray().Select(x => x.GetInt32()));
        Assert.Equal(new[] { 0, 1, 2 }, transitive.GetProperty("parameter_slots").EnumerateArray().Select(x => x.GetInt32()));
        var named = evidence.Occurrences.Single(pair => pair.Key.Theorem.EndsWith(".namedSource", StringComparison.Ordinal)).Value;
        Assert.Equal("D5.InstanceSupportFixture.namedClaim", named.SourceDefinitionName);
        Assert.Equal(0, named.SourceBinding!.Value.GetProperty("telescope_size").GetInt32());
        Assert.Single(named.SourceBinding.Value.GetProperty("support_entries").EnumerateArray());

        foreach (var mutation in new[] { "empty-support", "omit-transitive-support", "evidence-reference" })
        {
            var raw = JsonNode.Parse(File.ReadAllBytes(reportPath))!;
            var module = raw["modules"]!.AsArray().Single(m => m!["source_path"]!.GetValue<string>() == path.Value)!;
            var theorem = "D5.InstanceSupportFixture." + (mutation == "omit-transitive-support" ? "transitiveSource" : "source");
            var row = module["information_templates"]!["records"]!.AsArray()
                .Single(r => r!["key"]!["theorem"]!.GetValue<string>() == theorem)!;
            var certificate = row["certificate"]!;
            var changed = certificate["source_binding"]!;
            if (mutation == "evidence-reference") certificate["evidence_ref"] = new string('0', 64);
            else
            {
                foreach (var field in new[] { "support", "support_paths", "support_entries" })
                    if (mutation == "empty-support") changed[field] = new JsonArray();
                    else changed[field]!.AsArray().RemoveAt(0);
                changed["parameter_slots"] = mutation == "empty-support" ? new JsonArray(0) : new JsonArray(0, 2);
                var tokens = changed["support_entries"]!.AsArray().Select(e =>
                    e!["index"]!.ToJsonString() + ":" + string.Join("/", e["path"]!.AsArray().Select(n => n!.GetValue<string>()))
                        + ":" + e["identity"]!.GetValue<string>());
                changed["support_identity"] = InformationTemplateJson.Sha256(
                    System.Text.Encoding.UTF8.GetBytes("DTR-source-support-v1:" + string.Join(",", tokens)));
            }
            var mutated = Path.Combine(temporary.Path, mutation + ".json");
            File.WriteAllBytes(mutated, Trureturing.Truth.StructuredCanonicalWriter.WriteJson(raw.ToJsonString()).AsSpan());
            File.Copy(reportPath + ".materials.zip", mutated + ".materials.zip");
            var error = Assert.Throws<FormatException>(() => InformationTemplateEvidence.Collect(snapshot,
                RawLeanReportArtifact.ReadFile(mutated, snapshot, validateMaterials: true), [path]));
            Assert.Contains("binding identity differs", error.Message, StringComparison.Ordinal);
        }

        foreach (var mutation in new[] { "support-order", "named-owner", "named-path", "named-body" })
        {
            var wire = JsonNode.Parse(report.Files[path].InformationTemplates!.Value.GetRawText())!;
            var name = "D5.InstanceSupportFixture." + (mutation == "support-order" ? "transitiveSource" : "namedSource");
            var row = wire["records"]!.AsArray().Single(r => r!["key"]!["theorem"]!.GetValue<string>() == name)!;
            var changed = row["certificate"]!["source_binding"]!;
            var files = report.Files.ToDictionary(pair => pair.Key.Value, pair => pair.Value);
            switch (mutation)
            {
                case "support-order":
                    // Reorder the entire self-consistent block, including its
                    // identity, so lexical order is checked by the consumer.
                    foreach (var field in new[] { "support", "support_paths", "support_entries" })
                        changed[field] = new JsonArray(changed[field]!.AsArray().Reverse().Select(n => n!.DeepClone()).ToArray());
                    var tokens = changed["support_entries"]!.AsArray().Select(e =>
                        e!["index"]!.ToJsonString() + ":" + string.Join("/", e["path"]!.AsArray().Select(n => n!.GetValue<string>()))
                            + ":" + e["identity"]!.GetValue<string>());
                    changed["support_identity"] = InformationTemplateJson.Sha256(
                        System.Text.Encoding.UTF8.GetBytes("DTR-source-support-v1:" + string.Join(",", tokens)));
                    break;
                case "named-owner": changed["definition_entry"]!["owner"] = "D5.Other"; break;
                case "named-path": changed["definition_entry"]!["path"] = new JsonArray("arg"); break;
                case "named-body":
                    var sourcePath = "D5/InstanceSupportFixture.lean";
                    files[sourcePath] = files[sourcePath] with { Declarations = files[sourcePath].Declarations.Select(d =>
                        d.Name == "D5.InstanceSupportFixture.namedClaim" ? d with {
                            TypeRepresentation = d.LoadTypeRepresentation().Replace("ep(bc,", "ep(bd,", StringComparison.Ordinal)
                        } : d).ToImmutableArray() };
                    break;
            }
            files[path.Value] = files[path.Value] with { InformationTemplates = JsonSerializer.SerializeToElement(wire) };
            Assert.Throws<FormatException>(() => InformationTemplateEvidence.Collect(snapshot,
                LeanAxiomReport.Create(files), [path]));
        }

        foreach (var mutation in new[] { "removed-block", "material", "missing", "sibling", "order", "actual", "mode" })
        {
            var wire = JsonNode.Parse(report.Files[path].InformationTemplates!.Value.GetRawText())!;
            var row = wire["records"]!.AsArray().Single(r => r!["key"]!["theorem"]!.GetValue<string>() == "D5.InstanceSupportFixture.source")!;
            var changed = row["certificate"]!["source_binding"]!;
            switch (mutation)
            {
                case "removed-block":
                    foreach (var field in new[] { "support", "support_paths", "support_entries", "support_identity", "parameter_slots" })
                        changed.AsObject().Remove(field);
                    break;
                case "material":
                    var text = "ec(ns(n0,3:Nat),[])";
                    var hash = InformationTemplateJson.Sha256(System.Text.Encoding.UTF8.GetBytes(text));
                    changed["support_entries"]![0]!["material"] = text;
                    changed["support_entries"]![0]!["identity"] = hash;
                    changed["support_identity"] = InformationTemplateJson.Sha256(
                        System.Text.Encoding.UTF8.GetBytes("DTR-source-support-v1:1:body/body:" + hash));
                    break;
                case "missing": changed.AsObject().Remove("support_entries"); break;
                case "sibling": changed["support_paths"]![0] = new JsonArray("arg", "body"); break;
                case "order": changed["parameter_slots"] = new JsonArray(1, 0); break;
                case "actual": row["escape_from"]!["object_identity"] = new string('0', 64); break;
                case "mode":
                    changed["support"] = new JsonArray(2);
                    changed["support_paths"]![0] = new JsonArray("body", "body", "body");
                    changed["support_entries"]![0]!["index"] = 2;
                    changed["support_entries"]![0]!["path"] = new JsonArray("body", "body", "body");
                    changed["parameter_slots"] = new JsonArray(0, 2);
                    break;
            }
            var files = report.Files.ToDictionary(pair => pair.Key.Value, pair => pair.Value);
            files[path.Value] = report.Files[path] with { InformationTemplates = JsonSerializer.SerializeToElement(wire) };
            Assert.Throws<FormatException>(() => InformationTemplateEvidence.Collect(snapshot,
                LeanAxiomReport.Create(files), [path]));
        }
    }
}
