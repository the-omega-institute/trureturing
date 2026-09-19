using System.Collections.Immutable;
using System.Text;
using System.Text.Encodings.Web;
using System.Text.Json;

namespace StrataLint.Engine;

internal sealed record InformationFamilyBinding(string Source, string SourcePath, string Identity,
    ImmutableArray<int> Coordinates, ImmutableArray<string> StatePath, ImmutableArray<string> OutputPath);

// This reader validates current native evidence, never proves a family claim.
// Source bytes and exact wire bindings remain mandatory for selected delta rows.
internal static class InformationFamilyEvidence
{
    internal static InformationFamilyBinding? Read(JsonElement record, InformationOccurrenceKey key,
        string statement, InformationTemplateBindingState state,
        ImmutableArray<InformationTemplateContentInput> inputs, InformationEscapeContinuation? continuation)
    {
        var value = record.GetProperty("family_binding");
        var origin = record.GetProperty("escape_from");
        if (state != InformationTemplateBindingState.DeclaredValidated)
        {
            if (value.ValueKind != JsonValueKind.Null || origin.ValueKind != JsonValueKind.Null)
                throw new FormatException("DTR-Evidence: unresolved family carries validated scope");
            return null;
        }
        if (key.Mode != "dependent-family-v1" || continuation?.Kind != "open")
            throw new FormatException("DTR-Evidence: family mode/continuation mismatch");
        InformationTemplateJson.Fields(value, "identity", "material");
        var identity = Hash(value, "identity");
        var material = value.GetProperty("material");
        InformationTemplateJson.Fields(material, "mode", "source_name", "source_path", "source_sha256",
            "statement_identity", "source_type_identity", "rigid_levels", "telescope", "coordinates",
            "state", "output", "signature_identity", "state_field_identity", "output_field_identity",
            "law_identity", "realization_identity", "registration_identity", "bridge_identity",
            "variation_identity", "sensitivity_identity", "continuation", "plan_identity",
            "descriptor_identity", "actual_identity", "template_arguments");
        var source = InformationTemplateJson.Name(Text(material, "source_name"));
        var path = Text(material, "source_path");
        if (source != key.Theorem || Text(material, "mode") != key.Mode
            || Text(material, "continuation") != "open" || Hash(material, "statement_identity") != statement
            || Hash(material, "source_type_identity") != statement
            || !inputs.Contains(new(path, Hash(material, "source_sha256"))))
            throw new FormatException("DTR-Evidence: family source binding mismatch");
        InformationTemplateJson.Fields(origin, "kind", "source", "scope_identity");
        if (Text(origin, "kind") != "source-occurrence" || Text(origin, "source") != source
            || Hash(origin, "scope_identity") != identity)
            throw new FormatException("DTR-Evidence: family origin binding mismatch");
        var levels = Array(material, "rigid_levels", 64).Select(e =>
            InformationTemplateJson.Name(e.GetString() ?? "")).ToArray();
        if (levels.Distinct(StringComparer.Ordinal).Count() != levels.Length)
            throw new FormatException("DTR-Evidence: duplicate rigid family levels");
        var telescope = Array(material, "telescope", 64).ToArray();
        for (var i = 0; i < telescope.Length; i++)
        {
            var binder = telescope[i];
            InformationTemplateJson.Fields(binder, "ordinal", "binder_info", "domain_identity");
            if (Nat(binder.GetProperty("ordinal"), 63) != i
                || Text(binder, "binder_info") is not ("Lean.BinderInfo.default" or "Lean.BinderInfo.implicit"
                    or "Lean.BinderInfo.strictImplicit" or "Lean.BinderInfo.instImplicit"))
                throw new FormatException("DTR-Evidence: family telescope order/kind");
            Hash(binder, "domain_identity");
        }
        var coordinates = Array(material, "coordinates", 64).Select(e => Nat(e, telescope.Length - 1)).ToImmutableArray();
        var previous = -1;
        foreach (var coordinate in coordinates)
        {
            if (coordinate <= previous || Text(telescope[coordinate], "binder_info") == "Lean.BinderInfo.instImplicit")
                throw new FormatException("DTR-Evidence: family coordinate order/kind");
            previous = coordinate;
        }
        var statePath = Occurrence(material.GetProperty("state"), coordinates);
        var outputPath = Occurrence(material.GetProperty("output"), coordinates);
        foreach (var field in new[] { "signature_identity", "state_field_identity", "output_field_identity",
            "law_identity", "realization_identity", "registration_identity", "bridge_identity",
            "variation_identity", "sensitivity_identity" }) Hash(material, field);
        var certificate = record.GetProperty("certificate");
        foreach (var field in new[] { "plan_identity", "descriptor_identity", "actual_identity" })
            if (Hash(material, field) != Hash(certificate, field))
                throw new FormatException("DTR-Evidence: family extraction certificate mismatch");
        var arguments = Array(material, "template_arguments", 64).ToArray();
        for (var i = 0; i < arguments.Length; i++)
        {
            InformationTemplateJson.Fields(arguments[i], "ordinal", "identity", "kind");
            if (Nat(arguments[i].GetProperty("ordinal"), 63) != i
                || Text(arguments[i], "kind") is not ("LeanInformationAudit.TemplateAudit.SlotKind.carrier"
                    or "LeanInformationAudit.TemplateAudit.SlotKind.data" or "LeanInformationAudit.TemplateAudit.SlotKind.function"
                    or "LeanInformationAudit.TemplateAudit.SlotKind.predicate" or "LeanInformationAudit.TemplateAudit.SlotKind.dictionary"
                    or "LeanInformationAudit.TemplateAudit.SlotKind.proof" or "LeanInformationAudit.TemplateAudit.SlotKind.interface"))
                throw new FormatException("DTR-Evidence: family executable argument map");
            Hash(arguments[i], "identity");
        }
        if (Identity(material) != identity) throw new FormatException("DTR-Evidence: stale family evidence identity");
        if (BindingIdentity(key, statement, identity, certificate) != Hash(certificate, "evidence_ref"))
            throw new FormatException("DTR-Evidence: family certificate binding mismatch");
        return new(source, path, identity, coordinates, statePath, outputPath);
    }

    // Recompute the current native certificate framing for this mode. Rehashing
    // only a copied family material cannot reuse another native certificate.
    internal static string BindingIdentity(InformationOccurrenceKey key, string statement,
        string familyIdentity, JsonElement certificate)
    {
        using var stream = new MemoryStream();
        void Token(string value)
        {
            var bytes = Encoding.UTF8.GetBytes(value);
            stream.Write(Encoding.ASCII.GetBytes(bytes.Length.ToString(System.Globalization.CultureInfo.InvariantCulture) + ":"));
            stream.Write(bytes);
            if (stream.Length > 524288) throw new FormatException("DTR-Evidence: family certificate byte budget");
        }
        void Name(string value)
        {
            InformationTemplateJson.Name(value);
            var parts = new List<(string Kind, string Value)>();
            for (var index = 0; index < value.Length;)
            {
                var quoted = value[index] == '«';
                var end = value.IndexOf(quoted ? '»' : '.', index);
                if (end < 0) end = value.Length;
                var part = value[(index + (quoted ? 1 : 0))..end];
                parts.Add((!quoted && part.All(char.IsAsciiDigit) ? "num" : "str", part));
                index = end + (quoted ? 2 : 1);
            }
            if (parts.Count > 256) throw new FormatException("DTR-Evidence: family certificate name depth");
            foreach (var part in parts.AsEnumerable().Reverse()) Token(part.Kind);
            Token("anonymous");
            foreach (var part in parts) Token(part.Value);
        }
        Token("DTR-binding-evidence-v3");
        foreach (var name in new[] { key.Root, key.RegistrationModule, key.Theorem, key.ObjectArena, key.Catalog }) Name(name);
        Token(key.Mode); Token(statement);
        foreach (var field in new[] { "plan_identity", "descriptor_identity", "actual_identity" }) Token(Hash(certificate, field));
        Token("family-forward"); Token(familyIdentity); Token("missing-from");
        Token("open"); Token("anonymous"); Token(""); Token("anonymous");
        foreach (var field in new[] { "argument_inputs", "extraction_inputs" })
        {
            var inputs = Array(certificate, field, 4096).ToArray();
            Token(inputs.Length.ToString(System.Globalization.CultureInfo.InvariantCulture));
            foreach (var input in inputs)
            {
                Name(Text(input, "name")); Name(Text(input, "owner"));
                Token(Hash(input, "type_identity"));
                Token(input.GetProperty("body_identity").GetString() ?? throw new FormatException("DTR-Evidence: dependency body"));
            }
        }
        return InformationTemplateJson.Sha256(stream.ToArray());
    }

    private static ImmutableArray<string> Occurrence(JsonElement value, ImmutableArray<int> coordinates)
    {
        InformationTemplateJson.Fields(value, "path", "context_identity", "raw_identity", "fiber_identity", "context_size");
        foreach (var field in new[] { "context_identity", "raw_identity", "fiber_identity" }) Hash(value, field);
        var size = Nat(value.GetProperty("context_size"), 256);
        if (coordinates.Any(i => i >= size)) throw new FormatException("DTR-Evidence: captured family coordinate");
        return Array(value, "path", 256).Select(e => e.GetString() switch
        {
            "fn" => "fn", "arg" => "arg", "body" => "body", "domain" => "domain", "type" => "type", "value" => "value",
            _ => throw new FormatException("DTR-Evidence: unknown family source path edge"),
        }).ToImmutableArray();
    }

    internal static string Identity(JsonElement material)
    {
        using var stream = new MemoryStream();
        stream.Write(Encoding.UTF8.GetBytes("DTR-family-evidence-v1:"));
        using (var writer = new Utf8JsonWriter(stream, new() { Encoder = JavaScriptEncoder.UnsafeRelaxedJsonEscaping }))
            Write(writer, material, 0);
        if (stream.Length > 524288) throw new FormatException("DTR-Evidence: family material byte budget");
        return InformationTemplateJson.Sha256(stream.ToArray());
    }

    private static void Write(Utf8JsonWriter writer, JsonElement value, int depth)
    {
        if (depth > 32) throw new FormatException("DTR-Evidence: family material depth budget");
        switch (value.ValueKind)
        {
            case JsonValueKind.Object:
                writer.WriteStartObject();
                foreach (var property in value.EnumerateObject().OrderBy(p => p.Name, StringComparer.Ordinal))
                {
                    writer.WritePropertyName(property.Name);
                    Write(writer, property.Value, depth + 1);
                }
                writer.WriteEndObject();
                break;
            case JsonValueKind.Array:
                writer.WriteStartArray();
                foreach (var item in value.EnumerateArray()) Write(writer, item, depth + 1);
                writer.WriteEndArray();
                break;
            default: value.WriteTo(writer); break;
        }
    }

    private static IEnumerable<JsonElement> Array(JsonElement value, string field, int bound)
    {
        var array = value.GetProperty(field);
        if (array.ValueKind != JsonValueKind.Array || array.GetArrayLength() > bound)
            throw new FormatException("DTR-Evidence: family array budget/kind");
        return array.EnumerateArray();
    }

    private static int Nat(JsonElement value, int bound)
    {
        if (!value.TryGetInt32(out var n) || n < 0 || n > bound
            || value.GetRawText() != n.ToString(System.Globalization.CultureInfo.InvariantCulture))
            throw new FormatException("DTR-Evidence: family ordinal/bound");
        return n;
    }

    private static string Text(JsonElement value, string field) => InformationTemplateJson.String(value, field);
    private static string Hash(JsonElement value, string field) => InformationTemplateJson.Hash(Text(value, field), 64);
}
