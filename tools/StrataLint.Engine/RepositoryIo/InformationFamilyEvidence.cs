using System.Collections.Immutable;
using System.Text;
using System.Text.Json;

namespace StrataLint.Engine;

internal sealed record InformationFamilyBinding(string Source, string SourcePath, string Identity,
    ImmutableArray<int> Coordinates, ImmutableArray<string> StatePath, ImmutableArray<string> OutputPath,
    string RegistrationIdentity, int LevelArity, JsonElement RegistrationInput,
    string StatementIdentity, string LawIdentity, string ArenaName);

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
            "law_identity", "realization_identity", "registration_name", "registration_identity", "bridge_identity",
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
        var registration = InformationTemplateJson.Name(Text(material, "registration_name"));
        if (Text(record, "unit_name") != registration || Text(record, "realization_name") != registration)
            throw new FormatException("DTR-Evidence: family registration identity mismatch");
        var certificate = record.GetProperty("certificate");
        var registrationInputs = Array(certificate, "extraction_inputs", 4096)
            .Where(input => Text(input, "name") == registration).ToArray();
        if (registrationInputs.Length != 1)
            throw new FormatException("DTR-Evidence: family registration extraction input missing/ambiguous");
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
        return new(source, path, identity, coordinates, statePath, outputPath,
            Hash(material, "registration_identity"), levels.Length, registrationInputs[0].Clone(),
            Hash(material, "statement_identity"), Hash(material, "law_identity"), key.ObjectArena);
    }

    // This is an independent join against the native declaration report, not
    // another digest of editable certificate material. Its schema fixes the
    // proof-erased type/body and raw constant identity domains explicitly.
    internal static void CheckDeclaration(InformationFamilyBinding family, RepoPath owner,
        LeanDeclaration declaration)
    {
        if (declaration.FamilyRegistration is not { } native)
            throw new FormatException("DTR-Evidence: family registration declaration identity missing");
        InformationTemplateJson.Fields(native, "schema", "owner", "type_identity", "body_identity",
            "registration_identity", "level_arity", "family_relation");
        var input = family.RegistrationInput;
        if (Text(native, "schema") != "dtr-family-declaration-v1"
            || Text(native, "owner") != InformationTemplateEvidence.ModuleForSource(owner.Value)
            || Text(input, "name") != declaration.Name || Text(input, "owner") != Text(native, "owner")
            || Hash(input, "type_identity") != Hash(native, "type_identity")
            || Hash(input, "body_identity") != Hash(native, "body_identity")
            || family.RegistrationIdentity != Hash(native, "registration_identity")
            || family.LevelArity != Nat(native.GetProperty("level_arity"), 64))
            throw new FormatException("DTR-Evidence: family registration declaration identity mismatch");
        var relation = native.GetProperty("family_relation");
        if (relation.ValueKind != JsonValueKind.Object)
            throw new FormatException("DTR-Evidence: family source relation missing");
        InformationTemplateJson.Fields(relation, "mode", "source_name", "source_statement_identity",
            "arena_name", "arena_identity", "law_identity", "registration_name", "exact_source_law");
        if (Text(relation, "mode") != "dependent-family-v1"
            || InformationTemplateJson.Name(Text(relation, "source_name")) != family.Source
            || Hash(relation, "source_statement_identity") != family.StatementIdentity
            || InformationTemplateJson.Name(Text(relation, "arena_name")) != family.ArenaName
            || Hash(relation, "law_identity") != family.LawIdentity
            || InformationTemplateJson.Name(Text(relation, "registration_name")) != declaration.Name
            || relation.GetProperty("exact_source_law").ValueKind != JsonValueKind.True)
            throw new FormatException("DTR-Evidence: family source relation mismatch");
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

    // Match Lean.Json.compress: scalar UTF-8 (including supplementary scalars),
    // lowercase control escapes, and only quote, backslash, LF and CR short escapes.
    internal static string Identity(JsonElement material)
    {
        var text = new StringBuilder("DTR-family-evidence-v1:");
        Write(text, material, 0);
        var bytes = new UTF8Encoding(false, true).GetBytes(text.ToString());
        if (bytes.Length > 524288) throw new FormatException("DTR-Evidence: family material byte budget");
        return InformationTemplateJson.Sha256(bytes);
    }

    private static void String(StringBuilder text, string value)
    {
        text.Append('"');
        foreach (var c in value)
            switch (c)
            {
                case '"': text.Append("\\\""); break;
                case '\\': text.Append("\\\\"); break;
                case '\n': text.Append("\\n"); break;
                case '\r': text.Append("\\r"); break;
                default:
                    if (c < 0x20) text.Append("\\u").Append(((int)c).ToString("x4", System.Globalization.CultureInfo.InvariantCulture));
                    else text.Append(c);
                    break;
            }
        text.Append('"');
    }

    private static void Write(StringBuilder text, JsonElement value, int depth)
    {
        if (depth > 32 || text.Length > 524288)
            throw new FormatException("DTR-Evidence: family material depth/byte budget");
        var separator = false;
        switch (value.ValueKind)
        {
            case JsonValueKind.Object:
                text.Append('{');
                foreach (var property in value.EnumerateObject().OrderBy(p => p.Name, StringComparer.Ordinal))
                {
                    if (separator) text.Append(',');
                    separator = true;
                    String(text, property.Name);
                    text.Append(':');
                    Write(text, property.Value, depth + 1);
                }
                text.Append('}');
                break;
            case JsonValueKind.Array:
                text.Append('[');
                foreach (var item in value.EnumerateArray())
                {
                    if (separator) text.Append(',');
                    separator = true;
                    Write(text, item, depth + 1);
                }
                text.Append(']');
                break;
            case JsonValueKind.String: String(text, value.GetString()!); break;
            default: text.Append(value.GetRawText()); break;
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
        if (value.ValueKind != JsonValueKind.Number || !value.TryGetInt32(out var n) || n < 0 || n > bound
            || value.GetRawText() != n.ToString(System.Globalization.CultureInfo.InvariantCulture))
            throw new FormatException("DTR-Evidence: family ordinal/bound");
        return n;
    }

    private static string Text(JsonElement value, string field) => InformationTemplateJson.String(value, field);
    private static string Hash(JsonElement value, string field) => InformationTemplateJson.Hash(Text(value, field), 64);
}
