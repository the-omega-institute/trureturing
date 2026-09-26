using System.Collections.Immutable;
using System.Text;
using System.Text.Json;
using System.Text.Json.Nodes;
using StrataLint.Engine;

namespace StrataLint.DeclaredTemplate.Tests;

// These are strict wire/ownership fixtures. Kernel behavior is exercised by the
// Lean enrollment and registration controls, not by fabricated C# proofs.
public sealed class InformationTemplateEvidenceTests
{
    private const string PathA = "Reg/D5/S0/Carrier/Probe.lean";
    private const string ModuleA = "Reg.D5.S0.Carrier.Probe";
    private const string PathB = "Reg/D5/S0/Carrier/Binding.lean";
    private const string TextA = "-- synthetic evidence loader source A\n";
    private const string TextB = "import Reg.D5.S0.Carrier.Probe\n-- synthetic foreignClaim source\n";
    private static readonly InformationOccurrenceKey Key = new(ModuleA, ModuleA,
        ModuleA + ".target", ModuleA + ".arena", ModuleA + ".catalog");
    private static readonly string Unit = ModuleA + ".target.__information_unit";
    private static readonly string Realization = ModuleA + ".target.__primitive_realization";
    private const string MissingDiagnostic = "IE-C050 ClosedTruthReadout "
        + "key=Reg.D5.S0.Carrier.Probe/Reg.D5.S0.Carrier.Probe.catalog/Reg.D5.S0.Carrier.Probe.target "
        + "reason=unclassified_form rule=dtr.missing_declaration site=\"\" readout=\"\" "
        + "provenance={\"argument_inputs\":[],\"extraction_inputs\":[],\"plan_identity\":null,"
        + "\"rule\":\"dtr.missing_declaration\",\"site\":\"\",\"template_key\":null}";
    private static string Hash(string text) => InformationTemplateJson.Sha256(Encoding.UTF8.GetBytes(text));
    private static object Input(string path, string text) => new { path, sha256 = Hash(text) };

    private static RepositorySnapshot Snapshot(params (string Path, string Text)[] entries)
    {
        var files = InformationTemplateFixture.PolicyFiles();
        foreach (var (path, text) in entries) files[path] = text;
        return DeclaredTemplateFixture.Tree(files);
    }

    private static JsonElement Wire(bool declared = false, bool foreignClaim = false, int? compatibility = null) =>
        JsonSerializer.SerializeToElement(new
        {
            schema_version = 1,
            compatibility_version = compatibility ?? InformationTemplateFixture.ManifestVersion(InformationTemplateFixture.PolicyFiles()),
            inventory = foreignClaim ? [] : new[] { InformationTemplateJson.KeyJson(Key) },
            registered = foreignClaim ? [] : new[] { InformationTemplateJson.KeyJson(Key) },
            records = new[] { new
            {
                key = InformationTemplateJson.KeyJson(Key),
                escape_from = InformationTemplateFixture.FromSlot,
                escape_continues = InformationTemplateFixture.OpenSlot, bridge_kind = "legacy",
                unit_name = Unit,
                realization_name = Realization,
                registration_source_path = PathA,
                statement_identity = Hash("fixture statement A"),
                binding_source_path = declared ? foreignClaim ? PathB : PathA : null,
                state = declared ? "declared_validated" : "undeclared",
                diagnostic = declared ? null : MissingDiagnostic,
                certificate = declared ? new
                {
                    key = InformationTemplateJson.KeyJson(Key),
                    evidence_ref = Hash("fixture binding A"),
                    plan_identity = Hash("fixture plan"),
                    descriptor_identity = Hash("fixture descriptor"),
                    actual_identity = Hash("fixture actual"),
                    argument_inputs = System.Array.Empty<object>(),
                    extraction_inputs = System.Array.Empty<object>(),
                } : null,
            } },
        });

    private static System.Text.Json.Nodes.JsonObject SourceWire()
    {
        var wire = JsonSerializer.SerializeToNode(Wire(declared: true))!.AsObject();
        var row = wire["records"]![0]!;
        row["bridge_kind"] = "source-equivalence";
        row["escape_from"] = JsonSerializer.SerializeToNode(new {
            name = Key.Theorem, type_identity = Hash("fixture statement A"), object_identity = Hash("fixture actual") });
        row["certificate"]!["source_binding"] = JsonSerializer.SerializeToNode(new {
            source_owner = "D5.S0.Carrier.Probe", source_name = Key.Theorem,
            source_type_identity = Hash("fixture statement A"), telescope_size = 13, level_count = 2,
            coordinates = new[] { 0, 1, 11 },
            coordinate_paths = new[] { 0, 1, 11 }.Select(i => Enumerable.Repeat("body", i + 1).ToArray()).ToArray(), registration_identity = Hash("fixture registration"),
            readouts = new[] { new { path = Enumerable.Repeat("body", 17).Concat(new[] { "arg" }).ToArray(),
                state_binder = 16, scope_size = 17,
                scope_paths = Enumerable.Range(1, 17).Select(i => Enumerable.Repeat("body", i).ToArray()).ToArray(),
                occurrence_identity = Hash("fixture original projection") } } });
        return wire;
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void explicit_source_operands_preserve_strict_scope_shape(bool predicate)
    {
        var wire = SourceWire();
        var binding = wire["records"]![0]!["certificate"]!["source_binding"]!;
        binding["coordinates"] = new JsonArray();
        binding["coordinate_paths"] = new JsonArray();
        var readout = binding["readouts"]![0]!;
        readout["scope_size"] = 0;
        readout["scope_paths"] = new JsonArray();
        readout["state_binder"] = 0;
        if (predicate)
        {
            readout["state_operand"] = new JsonArray("fn", "arg");
            readout["boolean_predicate"] = true;
        }
        else readout["function_operand"] = true;
        InformationTemplateModuleEvidence Read() => InformationTemplateEvidence.Read(
            JsonSerializer.SerializeToElement(wire), PathA, Snapshot((PathA, TextA)));
        Assert.True(Assert.Single(Read().Records).HasFourSlots);
        readout["state_binder"] = 1;
        Assert.Throws<FormatException>(() => Read());
        readout["state_binder"] = 0;
        if (predicate) readout["state_operand"] = new JsonArray("body");
        else readout["function_operand"] = false;
        Assert.Throws<FormatException>(() => Read());
    }

    [Fact]
    public void finite_source_projection_requires_all_source_and_projection_dependencies()
    {
        var wire = SourceWire();
        var certificate = wire["records"]![0]!["certificate"]!;
        var family = ModuleA + ".familyArena";
        var bridge = ModuleA + ".legacyBridge";
        certificate["source_binding"]!["finite_projection"] = JsonSerializer.SerializeToNode(new {
            family_arena = family, bridge });
        certificate["extraction_inputs"] = JsonSerializer.SerializeToNode(new[] {
                family, bridge, Key.Theorem, Realization, Key.ObjectArena }
            .Select(name => new { name, owner = ModuleA, type_identity = Hash(name), body_identity = "" }));
        InformationTemplateModuleEvidence Read() => InformationTemplateEvidence.Read(
            JsonSerializer.SerializeToElement(wire), PathA, Snapshot((PathA, TextA)));
        Assert.Equal(5, Assert.Single(Read().Records).SourceProjectionOwners!.Count);
        var arenaDependency = certificate["extraction_inputs"]![4]!.DeepClone();
        certificate["extraction_inputs"]!.AsArray().RemoveAt(4);
        Assert.Throws<FormatException>(() => Read());
        certificate["extraction_inputs"]!.AsArray().Add(arenaDependency);
        certificate["extraction_inputs"]!.AsArray().RemoveAt(1);
        Assert.Throws<FormatException>(() => Read());
        certificate["source_binding"]!["finite_projection"]!["bridge"] = Key.Theorem;
        Assert.Throws<FormatException>(() => Read());
    }

    [Fact]
    public void source_bound_complete_telescope_wire_accepted()
    {
        var evidence = InformationTemplateEvidence.Read(JsonSerializer.SerializeToElement(SourceWire()),
            PathA, Snapshot((PathA, TextA)));
        var row = Assert.Single(evidence.Records);
        Assert.True(row.HasFourSlots);
        Assert.Equal("D5.S0.Carrier.Probe", row.SourceOwner);
    }

    [Theory]
    [InlineData(false, false, true)]
    [InlineData(true, false, false)]
    [InlineData(false, true, false)]
    public void source_theorem_owner_is_joined_through_actual_imports(bool wrongOwner, bool absentImport, bool accepted)
    {
        const string sourcePath = "D5/S0/Carrier/Probe.lean";
        var snapshot = Snapshot((PathA, TextA), (sourcePath, "-- source fixture\n"));
        var wire = SourceWire();
        if (wrongOwner) wire["records"]![0]!["certificate"]!["source_binding"]!["source_owner"] = "D5.Other";
        var evidence = InformationTemplateEvidence.Read(JsonSerializer.SerializeToElement(wire), PathA, snapshot);
        var module = Module(evidence) with { Imports = absentImport ? [] : ["D5.S0.Carrier.Probe"] };
        var report = LeanAxiomReport.Create(new Dictionary<string, LeanFileReport> {
            [PathA] = module, [sourcePath] = new([], [new(Key.Theorem, "theorem", "source fixture statement", [])]) });
        if (accepted) Assert.Single(Collect(snapshot, report).Inventory);
        else Assert.Throws<FormatException>(() => Collect(snapshot, report));
    }

    [Theory]
    [InlineData("source_name")]
    [InlineData("source_type_identity")]
    [InlineData("source_owner")]
    [InlineData("coordinates")]
    [InlineData("telescope_size")]
    [InlineData("level_count")]
    [InlineData("coordinate_paths")]
    [InlineData("scope_paths")]
    [InlineData("readouts")]
    [InlineData("state_binder")]
    [InlineData("path")]
    [InlineData("registration_identity")]
    [InlineData("missing")]
    [InlineData("residual")]
    public void source_bound_corrupt_scope_is_rejected(string field)
    {
        var wire = SourceWire();
        var row = wire["records"]![0]!;
        var source = row["certificate"]!["source_binding"]!;
        switch (field)
        {
            case "source_name": source[field] = "D5.other"; break;
            case "source_type_identity": source[field] = Hash("stale statement"); break;
            case "source_owner": source[field] = "Reg.WrongOwner"; break;
            case "coordinates": source[field] = JsonSerializer.SerializeToNode(new[] { 0, 11, 1 }); break;
            case "telescope_size": source[field] = 65; break;
            case "coordinate_paths": source[field] = JsonSerializer.SerializeToNode(new[] { new[] { "arg", "body" } }); break;
            case "scope_paths": source["readouts"]![0]![field] = new System.Text.Json.Nodes.JsonArray(); break;
            case "level_count": source[field] = 65; break;
            case "readouts": source[field] = new System.Text.Json.Nodes.JsonArray(); break;
            case "state_binder": source["readouts"]![0]![field] = 17; break;
            case "path": source["readouts"]![0]![field] = JsonSerializer.SerializeToNode(new[] { "normalize" }); break;
            case "registration_identity": source[field] = "missing"; break;
            case "missing": row["certificate"]!.AsObject().Remove("source_binding"); break;
            case "residual": row["escape_continues"] = null; break;
        }
        Assert.Throws<FormatException>(() => InformationTemplateEvidence.Read(JsonSerializer.SerializeToElement(wire),
            PathA, Snapshot((PathA, TextA))));
    }

    [Theory]
    [InlineData("valid")]
    [InlineData("missing")]
    [InlineData("owner")]
    [InlineData("name")]
    [InlineData("type_identity")]
    [InlineData("body_identity")]
    [InlineData("unknown")]
    [InlineData("null")]
    [InlineData("reference_identity")]
    [InlineData("missing-path")]
    [InlineData("wrong-path")]
    [InlineData("deep-path")]
    [InlineData("sibling-readout")]
    public void explicit_definition_entry_is_strict_and_bound_to_extraction(string mutation)
    {
        var wire = SourceWire();
        var certificate = wire["records"]![0]!["certificate"]!;
        var source = certificate["source_binding"]!;
        var entry = JsonSerializer.SerializeToNode(new {
            owner = "D5.S0.Carrier.Probe", name = "D5.S0.Carrier.Probe.claim",
            type_identity = Hash("Prop"), body_identity = Hash("original definition body") });
        source["definition_entry"] = entry!.DeepClone();
        source["definition_entry"]!["path"] = new JsonArray();
        source["definition_entry"]!["reference_identity"] = source["source_type_identity"]!.DeepClone();
        certificate["extraction_inputs"] = new System.Text.Json.Nodes.JsonArray(entry!.DeepClone());
        switch (mutation)
        {
            case "missing": source.AsObject().Remove("definition_entry"); break;
            case "owner": source["definition_entry"]![mutation] = "D5.Other"; break;
            case "name": source["definition_entry"]![mutation] = "D5.S0.Carrier.Probe.otherClaim"; break;
            case "type_identity": case "body_identity": case "reference_identity":
                source["definition_entry"]![mutation] = Hash("stale definition"); break;
            case "unknown": source["definition_entry"]!["normalize"] = true; break;
            case "null": source["definition_entry"] = null; break;
            case "missing-path": source["definition_entry"]!.AsObject().Remove("path"); break;
            case "wrong-path": source["definition_entry"]!["path"] = new JsonArray("body"); break;
            case "deep-path": source["definition_entry"]!["path"] = new JsonArray("arg", "arg"); break;
            case "sibling-readout": source["definition_entry"]!["path"] = new JsonArray("arg"); break;
        }
        InformationTemplateModuleEvidence Read() => InformationTemplateEvidence.Read(
            JsonSerializer.SerializeToElement(wire), PathA, Snapshot((PathA, TextA)));
        if (mutation == "valid")
            Assert.Equal("D5.S0.Carrier.Probe.claim", Assert.Single(Read().Records).SourceDefinitionName);
        else Assert.Throws<FormatException>(Read);
    }

    [Fact]
    public void source_binding_cannot_be_attached_to_a_legacy_certificate()
    {
        var wire = SourceWire();
        wire["records"]![0]!["bridge_kind"] = "legacy";
        Assert.Throws<FormatException>(() => InformationTemplateEvidence.Read(JsonSerializer.SerializeToElement(wire),
            PathA, Snapshot((PathA, TextA))));
    }

    private static LeanFileReport Module(InformationTemplateModuleEvidence evidence, bool foreignClaim = false) =>
        new(foreignClaim ? [ModuleA] : [], foreignClaim ? [] :
            [new(Unit, "def", "fixture unit", []), new(Realization, "def", "fixture realization", [])])
        { InformationTemplates = evidence.Wire };

    [Theory]
    [InlineData("Reg/D5/S0/Carrier/Probe.lean", "Reg.D5.S0.Carrier.Probe")]
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
    public void evidence_without_source_hash_lists_is_accepted()
    {
        var wire = JsonSerializer.SerializeToNode(Wire())!.AsObject();
        wire.Remove("inputs");
        foreach (var record in wire["records"]!.AsArray()) record!.AsObject().Remove("content_inputs");
        var evidence = InformationTemplateEvidence.Read(JsonSerializer.SerializeToElement(wire), PathA,
            Snapshot((PathA, TextA + "-- changed after extraction\n")));
        Assert.Single(evidence.Records);
    }

    [Theory]
    [InlineData("lean-report-inputs.json")]
    [InlineData("lean-toolchain")]
    [InlineData("lake-manifest.json")]
    public void retired_policy_input_is_malformed(string path)
    {
        var wire = JsonSerializer.SerializeToNode(Wire())!.AsObject();
        wire["inputs"] = JsonSerializer.SerializeToNode(new[] {
            Input(path, InformationTemplateFixture.PolicyFiles()[path]) });
        var error = Assert.Throws<FormatException>(() => InformationTemplateEvidence.Read(
            JsonSerializer.SerializeToElement(wire), PathA, Snapshot((PathA, TextA))));
        Assert.StartsWith("DTR-Evidence:", error.Message);
    }


    [Theory]
    [InlineData("legacy", true)]
    [InlineData("forward", true)]
    [InlineData("witness", true)]
    [InlineData("unknown", false)]
    public void strict_bridge_vocabulary(string kind, bool accepted)
    {
        var wire = JsonSerializer.SerializeToNode(Wire(declared: true))!.AsObject();
        wire["records"]![0]!["bridge_kind"] = kind;
        if (accepted)
        {
            var evidence = InformationTemplateEvidence.Read(JsonSerializer.SerializeToElement(wire), PathA, Snapshot((PathA, TextA)));
            Assert.Equal(kind, Assert.Single(evidence.Records).BridgeKind);
        }
        else
        {
            var error = Assert.Throws<FormatException>(() => InformationTemplateEvidence.Read(
                JsonSerializer.SerializeToElement(wire), PathA, Snapshot((PathA, TextA))));
            Assert.Equal("DTR-Evidence: unknown bridge_kind", error.Message);
        }
    }

    [Fact]
    public void raw_report_retains_binding_inventory()
    {
        var module = RawReport().Files[RepoPath.CreateKnown(PathA)];
        var evidence = InformationTemplateEvidence.Read(module.InformationTemplates!.Value, PathA, Snapshot((PathA, TextA)));
        Assert.Equal(Key, Assert.Single(evidence.Records).Key);
    }

    [Theory]
    [InlineData(3)]
    [InlineData(4)]
    public void binding_loader_required(int retiredVersion)
    {
        var report = RawReport(compatibility: retiredVersion);
        Assert.Throws<FormatException>(() => InformationTemplateEvidence.Read(
            report.Files[RepoPath.CreateKnown(PathA)].InformationTemplates!.Value, PathA, Snapshot((PathA, TextA))));
    }

    [Fact]
    public void fresh_imported_record_accepted()
    {
        var snapshot = Snapshot((PathA, TextA));
        var evidence = InformationTemplateEvidence.Read(Wire(), PathA, snapshot);
        var universe = Collect(snapshot,
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
            var universe = Collect(snapshot,
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
        var error = Assert.Throws<FormatException>(() => Collect(snapshot,
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
            universe = Collect(snapshot, LeanAxiomReport.Create(
                new Dictionary<string, LeanFileReport>
                {
                    [PathA] = new([], [new(unit, "def", "fixture unit", []),
                        new(realization, "def", "fixture realization", [])]) { InformationTemplates = evidence.Wire },
                }));
        });
        Assert.True(error is null, "[FAIL] generated_name_with_nested_quote_accepted: " + error?.Message);
        Assert.Equal(unit, Assert.Single(universe!.Occurrences).Value.UnitName);
    }

    [Theory]
    [InlineData("argument_inputs", "valid")]
    [InlineData("extraction_inputs", "valid")]
    [InlineData("extraction_inputs", "owner")]
    [InlineData("extraction_inputs", "unrelated-name")]
    [InlineData("extraction_inputs", "missing-declaration")]
    [InlineData("extraction_inputs", "ambiguous-declaration")]
    [InlineData("extraction_inputs", "duplicate-dependency")]
    [InlineData("extraction_inputs", "type-identity")]
    [InlineData("extraction_inputs", "body-identity")]
    public void generated_realization_dependency_resolves_exact_imported_declaration(string field, string mutation)
    {
        var realization = ModuleA + ".target.Fixture.Root/Fixture.arena/«catalog-name».__primitive_realization";
        var snapshot = Snapshot((PathA, TextA));
        var wire = JsonSerializer.SerializeToNode(Wire(declared: true))!.AsObject();
        wire["records"]![0]!["realization_name"] = realization;
        var dependency = JsonSerializer.SerializeToNode(new {
            name = mutation == "unrelated-name" ? realization + ".other" : realization,
            owner = mutation == "owner" ? "Reg.Other" : ModuleA,
            type_identity = mutation == "type-identity" ? "invalid" : Hash("fixture type"),
            body_identity = mutation == "body-identity" ? "invalid" : Hash("fixture body"),
        })!;
        var dependencies = new JsonArray(dependency);
        if (mutation == "duplicate-dependency") dependencies.Add(dependency.DeepClone());
        wire["records"]![0]!["certificate"]![field] = dependencies;
        var declarations = new List<LeanDeclaration> { new(Unit, "def", "fixture unit", []) };
        if (mutation != "missing-declaration") declarations.Add(new(realization, "def", "fixture realization", []));
        if (mutation == "ambiguous-declaration") declarations.Add(new(realization, "def", "different declaration", [])
            { NameKey = "ns(n0,9:different)" });
        InformationTemplateUniverse Read()
        {
            var evidence = InformationTemplateEvidence.Read(JsonSerializer.SerializeToElement(wire), PathA, snapshot);
            return Collect(snapshot, LeanAxiomReport.Create(new Dictionary<string, LeanFileReport> {
                [PathA] = new([], declarations.ToImmutableArray()) { InformationTemplates = evidence.Wire },
            }));
        }
        if (mutation == "valid") Assert.True(Assert.Single(Read().Occurrences).Value.HasFourSlots);
        else Assert.Throws<FormatException>(Read);
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
        var error = Record.Exception(() => Collect(snapshot,
            LeanAxiomReport.Create(new Dictionary<string, LeanFileReport> { [PathA] = module })));
        Assert.True(error is FormatException && error.Message.Contains("retained unit/realization owner", StringComparison.Ordinal),
            "[FAIL] ambiguous_generated_" + (realization ? "realization" : "unit") + "_rejected");
    }

    private static InformationTemplateUniverse ImportedRealization(bool imported)
    {
        const string bridgeSource = "-- independently owned realization fixture\n";
        var registrationSource = imported ? "import Reg.D5.S0.Carrier.Binding\n" + TextA : TextA;
        var snapshot = Snapshot((PathA, registrationSource), (PathB, bridgeSource));
        var wire = JsonSerializer.SerializeToNode(Wire())!.AsObject();
        var owner = InformationTemplateEvidence.Read(JsonSerializer.SerializeToElement(wire), PathA, snapshot);
        var bridge = InformationTemplateEvidence.Read(JsonSerializer.SerializeToElement(new
        {
            schema_version = 1, compatibility_version = InformationTemplateFixture.ManifestVersion(InformationTemplateFixture.PolicyFiles()),
            inventory = System.Array.Empty<object>(), registered = System.Array.Empty<object>(),
            records = System.Array.Empty<object>(),
        }), PathB, snapshot);
        return Collect(snapshot, LeanAxiomReport.Create(
            new Dictionary<string, LeanFileReport>
            {
                [PathA] = new(imported ? ["Reg.D5.S0.Carrier.Binding"] : [],
                    [new(Unit, "def", "fixture unit", [])]) { InformationTemplates = owner.Wire },
                [PathB] = new([], [new(Realization, "theorem", "fixture realization", [])])
                    { InformationTemplates = bridge.Wire },
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
    public void unselected_foreign_claim_cannot_supply_a_declaration()
    {
        var snapshot = Snapshot((PathA, TextA), (PathB, TextB));
        var report = LeanAxiomReport.Create(new Dictionary<string, LeanFileReport>
        {
            [PathA] = Module(InformationTemplateEvidence.Read(Wire(), PathA, snapshot)),
            [PathB] = Module(InformationTemplateEvidence.Read(Wire(declared: true, foreignClaim: true), PathB, snapshot), foreignClaim: true),
        });
        var universe = Collect(snapshot, report);
        Assert.Single(universe.Occurrences);
        Assert.Null(universe.Occurrences[Key].BindingSourcePath);
        Assert.Equal(InformationTemplateBindingState.Undeclared, universe.Occurrences[Key].State);
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
        Assert.StartsWith("DTR-Evidence:", error.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void persisted_evidence_does_not_revalidate_source_bytes()
    {
        var evidence = InformationTemplateEvidence.Read(Wire(), PathA,
            Snapshot((PathA, TextA + "-- changed\n")));
        Assert.Single(evidence.Records);
    }

    [Fact]
    public void persisted_replay_rejected()
    {
        // A's inline binding cannot be replayed under B's producer owner.
        var wire = JsonSerializer.SerializeToNode(Wire(declared: true))!.AsObject();
        var error = Assert.Throws<FormatException>(() => InformationTemplateEvidence.Read(
            JsonSerializer.SerializeToElement(wire), PathB, Snapshot((PathA, TextA), (PathB, TextB))));
        Assert.Equal("DTR-Evidence: binding owner/diagnostic is missing or wrong", error.Message);
    }

    [Fact]
    public void binding_producer_cannot_disappear()
    {
        var snapshot = Snapshot((PathA, TextA));
        var report = LeanAxiomReport.Create(new Dictionary<string, LeanFileReport> { [PathA] = new([], []) });
        Assert.Throws<FormatException>(() => Collect(snapshot, report));
    }

    [Fact]
    public void inventory_hidden_root_rejected()
    {
        var snapshot = Snapshot((PathA, TextA), (PathB, TextB));
        var report = LeanAxiomReport.Create(new Dictionary<string, LeanFileReport>
        {
            [PathA] = Module(InformationTemplateEvidence.Read(Wire(), PathA, snapshot)),
        });
        Assert.Throws<FormatException>(() => InformationTemplateEvidence.Collect(snapshot, report,
            [RepoPath.CreateKnown(PathA), RepoPath.CreateKnown(PathB)]));
    }

    [Fact]
    public void unselected_foreign_claim_cannot_overwrite_inline_declaration()
    {
        var snapshot = Snapshot((PathA, TextA), (PathB, TextB));
        var report = LeanAxiomReport.Create(new Dictionary<string, LeanFileReport>
        {
            [PathA] = Module(InformationTemplateEvidence.Read(Wire(declared: true), PathA, snapshot)),
            [PathB] = Module(InformationTemplateEvidence.Read(Wire(declared: true, foreignClaim: true), PathB, snapshot), foreignClaim: true),
        });
        var result = Collect(snapshot, report);
        Assert.Equal(PathA, result.Occurrences[Key].BindingSourcePath);
    }
    private static InformationTemplateUniverse Collect(RepositorySnapshot snapshot, LeanAxiomReport report) =>
        InformationTemplateEvidence.Collect(snapshot, report, [RepoPath.CreateKnown(PathA)]);

    [Theory]
    [InlineData("Fixture.α₁.lemma?")]
    [InlineData("Fixture.«中文.name».value")]
    [InlineData("Fixture.«».23")]
    public void canonical_lean_name_roundtrip(string name) =>
        Assert.Equal(name, InformationTemplateJson.Name(name));

    [Theory]
    [InlineData("Fixture.«alpha»")]
    [InlineData("Fixture.中文")]
    [InlineData("Fixture.α.01")]
    [InlineData("Fixture.«missing")]
    [InlineData("Fixture.«name»tail")]
    [InlineData("Fixture.")]
    public void noncanonical_lean_name_rejected(string name) =>
        Assert.Throws<FormatException>(() => InformationTemplateJson.Name(name));
    [Theory]
    [InlineData(false, "valid")]
    [InlineData(true, "valid")]
    [InlineData(true, "permuted-universes")]
    [InlineData(true, "instantiated-universe")]
    [InlineData(true, "metadata-wrapper")]
    [InlineData(true, "missing-material")]
    [InlineData(true, "wrong-polarity")]
    public void named_reference_uses_raw_rigid_universes_and_structural_names(bool negated, string mutation)
    {
        // Synthetic statement-v1 materials exercise the bounded grammar beyond
        // the native clients' zero universes: UTF-8, quoted dots and a num node.
        const string nameKey = "ns(nn(ns(ns(ns(n0,2:D5),5:Probe),4:x.λ),7),5:claim)";
        const string referenceHash = "65960cfc15c52484d5f0825d7c9279debbdd37c841d4c3eddb3f9461b8cf9df9";
        const string negativeHash = "707564a4041c1bf2627e069ead2754a3de3c4bfc60642f419a2e2ec671a61f91";
        const string parameters = "ns(n0,1:u),ns(n0,1:v)";
        var levels = mutation switch {
            "permuted-universes" => "lp(ns(n0,1:v)),lp(ns(n0,1:u))",
            "instantiated-universe" => "l0,lp(ns(n0,1:v))",
            _ => "lp(ns(n0,1:u)),lp(ns(n0,1:v))",
        };
        var rawReference = "ec(" + nameKey + ",[" + levels + "])";
        var rawType = negated && mutation != "wrong-polarity"
            ? "ea(ec(ns(n0,3:Not),[])," + rawReference + ")" : rawReference;
        if (mutation == "metadata-wrapper") rawType = "ed(" + rawType + ")";
        var theorem = new LeanDeclaration("D5.Probe.result", "theorem",
            mutation == "missing-material" ? "unavailable"
                : "statement-v1(uparams=[" + parameters + "],type=" + rawType + ")", []);
        var definition = new LeanDeclaration("D5.Probe.«x.λ».7.claim", "def",
            "statement-v1(uparams=[ns(n0,1:a),ns(n0,1:b)],type=es(l0),value=fixture)", []) {
            NameKey = nameKey };
        var binding = JsonSerializer.SerializeToElement(new {
            level_count = 2,
            definition_entry = new { path = negated ? new[] { "arg" } : Array.Empty<string>(),
                reference_identity = referenceHash },
        });
        void Check() => InformationTemplateDefinitionReference.Check(binding,
            negated ? negativeHash : referenceHash, theorem, definition);
        if (mutation == "valid") Check();
        else Assert.Throws<FormatException>(Check);
    }

}
