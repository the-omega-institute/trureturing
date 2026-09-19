using System.Collections.Immutable;
using System.Text;
using System.Text.Json;
using System.Text.Json.Nodes;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class InformationFamilyEvidenceTests
{
    private const string Source = "D5.S0.Carrier.Probe.target";
    private const string Path = "D5/S0/Carrier/Probe.lean";
    private const string Hash = "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa";
    private static readonly InformationOccurrenceKey Key = new("D5.S0.Carrier.Binding", "D5.S0.Carrier.Binding",
        Source, "D5.S0.Carrier.Binding.arena", "D5.S0.Carrier.Binding.arena", "dependent-family-v1");

    private static JsonObject Fixture()
    {
        var occurrence = new { path = new[] { "body", "arg" }, context_size = 3,
            context_identity = Hash, raw_identity = Hash, fiber_identity = Hash };
        var material = JsonSerializer.SerializeToNode(new
        {
            mode = "dependent-family-v1", source_name = Source, source_path = Path, source_sha256 = Hash,
            statement_identity = Hash, source_type_identity = Hash,
            rigid_levels = new[] { "u", "v" },
            telescope = new[] {
                new { ordinal = 0, binder_info = "Lean.BinderInfo.implicit", domain_identity = Hash },
                new { ordinal = 1, binder_info = "Lean.BinderInfo.instImplicit", domain_identity = Hash },
                new { ordinal = 2, binder_info = "Lean.BinderInfo.default", domain_identity = Hash },
            }, coordinates = new[] { 0, 2 }, state = occurrence, output = occurrence,
            signature_identity = Hash, state_field_identity = Hash, output_field_identity = Hash,
            law_identity = Hash, realization_identity = Hash, registration_identity = Hash,
            bridge_identity = Hash, variation_identity = Hash, sensitivity_identity = Hash,
            continuation = "open", plan_identity = Hash, descriptor_identity = Hash, actual_identity = Hash,
            template_arguments = System.Array.Empty<object>(),
        })!;
        var identity = InformationFamilyEvidence.Identity(JsonSerializer.SerializeToElement(material));
        var record = new JsonObject
        {
            ["family_binding"] = new JsonObject { ["identity"] = identity, ["material"] = material },
            ["escape_from"] = new JsonObject { ["kind"] = "source-occurrence", ["source"] = Source, ["scope_identity"] = identity },
            ["certificate"] = new JsonObject { ["plan_identity"] = Hash, ["descriptor_identity"] = Hash, ["actual_identity"] = Hash,
                ["argument_inputs"] = new JsonArray(), ["extraction_inputs"] = new JsonArray() },
        };
        record["certificate"]!["evidence_ref"] = InformationFamilyEvidence.BindingIdentity(Key, Hash,
            identity, JsonSerializer.SerializeToElement(record["certificate"]));
        return record;
    }

    private static InformationFamilyBinding? Read(JsonObject record, InformationOccurrenceKey? key = null) =>
        InformationFamilyEvidence.Read(JsonSerializer.SerializeToElement(record), key ?? Key, Hash,
            InformationTemplateBindingState.DeclaredValidated, [new(Path, Hash)], new("open", null, null, null));

    [Fact]
    public void family_source_scope_and_separate_argument_map_are_retained()
    {
        var family = Assert.IsType<InformationFamilyBinding>(Read(Fixture()));
        Assert.Equal(new[] { 0, 2 }, family.Coordinates);
        Assert.Equal(Source, family.Source);
        Assert.Equal(new[] { "body", "arg" }, family.StatePath);
    }

    [Theory]
    [InlineData("dropped-source")]
    [InlineData("dropped-levels")]
    [InlineData("captured-coordinate")]
    [InlineData("dictionary-coordinate")]
    [InlineData("duplicate-coordinate")]
    [InlineData("substituted-origin")]
    [InlineData("raw-missing-origin")]
    [InlineData("stale-law")]
    [InlineData("stale-witness")]
    [InlineData("cross-mode")]
    [InlineData("copied-extraction")]
    [InlineData("unknown-binding")]
    public void family_mutations_fail_closed(string mutation)
    {
        var record = Fixture();
        var material = record["family_binding"]!["material"]!.AsObject();
        switch (mutation)
        {
            case "dropped-source": material.Remove("source_name"); break;
            case "dropped-levels": material.Remove("rigid_levels"); break;
            case "captured-coordinate": material["coordinates"] = new JsonArray(0, 3); break;
            case "dictionary-coordinate": material["coordinates"] = new JsonArray(0, 1); break;
            case "duplicate-coordinate": material["coordinates"] = new JsonArray(0, 0); break;
            case "substituted-origin": record["escape_from"]!["source"] = "Other.theorem"; break;
            case "raw-missing-origin": record["escape_from"] = null; break;
            case "stale-law": material["law_identity"] = new string('b', 64); break;
            case "stale-witness": material["sensitivity_identity"] = new string('b', 64); break;
            case "cross-mode": material["mode"] = "fixed-state-v1"; break;
            case "copied-extraction": record["certificate"]!["actual_identity"] = new string('b', 64); break;
            case "unknown-binding": material["unknown"] = true; break;
        }
        Assert.Throws<FormatException>(() => Read(record));
    }

    [Fact]
    public void rehashed_family_material_cannot_reuse_the_native_certificate()
    {
        var record = Fixture();
        record["family_binding"]!["material"]!["variation_identity"] = new string('b', 64);
        var identity = InformationFamilyEvidence.Identity(JsonSerializer.SerializeToElement(record["family_binding"]!["material"]));
        record["family_binding"]!["identity"] = identity;
        record["escape_from"]!["scope_identity"] = identity;
        Assert.Throws<FormatException>(() => Read(record));
    }

    [Fact]
    public void family_evidence_cannot_be_read_as_fixed_mode() =>
        Assert.Throws<FormatException>(() => Read(Fixture(), Key with { Mode = "fixed-state-v1" }));

    [Fact]
    public void mode_is_part_of_occurrence_identity()
    {
        Assert.NotEqual(Key, Key with { Mode = "fixed-state-v1" });
        var wire = InformationTemplateJson.KeyJson(Key);
        Assert.Equal(Key, InformationTemplateJson.ReadKey(wire));
        var node = JsonNode.Parse(wire.GetRawText())!.AsObject();
        node.Remove("mode");
        Assert.Throws<FormatException>(() => InformationTemplateJson.ReadKey(JsonSerializer.SerializeToElement(node)));
    }
}
