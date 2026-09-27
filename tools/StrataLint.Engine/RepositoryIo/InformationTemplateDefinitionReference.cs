using System.Globalization;
using System.Text;
using System.Text.Json;

namespace StrataLint.Engine;

// The named-entry grammar is only a nullary Prop constant, at the root or
// directly under literal Not. Its complete raw type is already in statement-v1
// materials; no expression normalization, proof inspection or new wire is needed.
internal static class InformationTemplateDefinitionReference
{
    internal static void Check(JsonElement binding, string statement,
        LeanDeclaration theorem, LeanDeclaration definition)
    {
        var entry = binding.GetProperty("definition_entry");
        var negated = entry.GetProperty("path").GetArrayLength() == 1;
        var material = theorem.LoadTypeRepresentation();
        var (parameters, typeStart) = Parameters(material);
        var definitionMaterial = definition.LoadTypeRepresentation();
        var (definitionParameters, definitionTypeStart) = Parameters(definitionMaterial);
        var components = CanonicalLeanNameDecoder.ComponentsPrefix(definition.NameKey, 0, out var consumed);
        if (consumed != definition.NameKey.Length || components.Length == 0
            || parameters.Length != binding.GetProperty("level_count").GetInt32()
            || parameters.Length != definitionParameters.Length
            || !definitionMaterial.AsSpan(definitionTypeStart)
                .StartsWith("es(l0),value=", StringComparison.Ordinal))
            throw new FormatException("DTR-Evidence: source definition raw declaration differs");
        var levels = string.Join(",", parameters.Select(p => "lp(" + p + ")"));
        var reference = "ec(" + definition.NameKey + ",[" + levels + "])";
        var expectedType = negated ? "ea(ec(ns(n0,3:Not),[])," + reference + ")" : reference;
        if (!material.AsSpan(typeStart).SequenceEqual((expectedType + ")").AsSpan()))
            throw new FormatException("DTR-Evidence: source definition raw occurrence differs");

        // Recompute the producer's compactRawIdentity on this bounded grammar.
        // The independent input is the source theorem's loaded, addressed type
        // material and the unique imported definition, not extraction_inputs or
        // another asserted identity in the registration certificate.
        if (Identity(components, parameters.Length, false)
                != entry.GetProperty("reference_identity").GetString()
            || Identity(components, parameters.Length, negated) != statement)
            throw new FormatException("DTR-Evidence: source definition reference identity differs from current declaration");
    }

    private static (string[] Parameters, int TypeStart) Parameters(string material)
    {
        const string prefix = "statement-v1(uparams=[";
        if (!material.StartsWith(prefix, StringComparison.Ordinal))
            throw new FormatException("DTR-Evidence: source definition requires raw statement material");
        var position = prefix.Length;
        var parameters = new List<string>();
        if (position < material.Length && material[position] != ']')
        {
            while (true)
            {
                if (parameters.Count == 64)
                    throw new FormatException("DTR-Evidence: source definition universe bound");
                _ = CanonicalLeanNameDecoder.ComponentsPrefix(material, position, out var consumed);
                parameters.Add(material.Substring(position, consumed));
                position += consumed;
                if (position == material.Length || material[position] != ',') break;
                position++;
            }
        }
        const string suffix = "],type=";
        if (!material.AsSpan(position).StartsWith(suffix, StringComparison.Ordinal)
            || parameters.Distinct(StringComparer.Ordinal).Count() != parameters.Count)
            throw new FormatException("DTR-Evidence: source definition universe parameters differ");
        return (parameters.ToArray(), position + suffix.Length);
    }

    private static string Identity((string Kind, string Value)[] name, int levels, bool negated)
    {
        var bytes = new StringBuilder();
        var tokens = new Dictionary<string, int>(StringComparer.Ordinal);
        void Emit(string token)
        {
            if (tokens.TryGetValue(token, out var index))
                bytes.Append('@').Append(index.ToString(CultureInfo.InvariantCulture)).Append(':');
            else
            {
                bytes.Append(Encoding.UTF8.GetByteCount(token).ToString(CultureInfo.InvariantCulture))
                    .Append(':').Append(token);
                tokens.Add(token, tokens.Count);
            }
        }
        void Constant((string Kind, string Value)[] parts, int levelCount)
        {
            Emit("expr-node");
            Emit("const");
            foreach (var part in parts.Reverse()) Emit(part.Kind == "ns" ? "str" : "num");
            Emit("anonymous");
            foreach (var part in parts) Emit(part.Value);
            Emit(levelCount.ToString(CultureInfo.InvariantCulture));
            for (var i = 0; i < levelCount; i++)
            {
                Emit("parameter");
                Emit(i.ToString(CultureInfo.InvariantCulture));
            }
        }
        Emit("DTR-source-expr-dag-v1");
        if (negated)
        {
            Emit("expr-node");
            Emit("app");
            Constant([("ns", "Not")], 0);
        }
        Constant(name, levels);
        return InformationTemplateJson.Sha256(Encoding.UTF8.GetBytes(bytes.ToString()));
    }
}
