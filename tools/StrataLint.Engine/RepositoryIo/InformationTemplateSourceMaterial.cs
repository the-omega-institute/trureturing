using System.Globalization;
using System.Text.Json;

namespace StrataLint.Engine;

// Structural navigation of the canonical producer material only. Names use the
// existing UTF-8 length-aware decoder; de Bruijn indices remain in their original
// lexical context. This does not infer types or normalize Lean expressions.
internal static class InformationTemplateSourceMaterial
{
    internal static void Check(JsonElement binding, LeanDeclaration theorem, LeanDeclaration? definition = null)
    {
        if (!binding.TryGetProperty("support_entries", out var entries) || entries.GetArrayLength() == 0) return;
        var material = theorem.LoadTypeRepresentation();
        var (parameters, start) = InformationTemplateDefinitionReference.Parameters(material);
        string[] prefix = [];
        var levels = new Dictionary<string, string>(StringComparer.Ordinal);
        if (binding.TryGetProperty("definition_entry", out var entryPoint))
        {
            if (definition is null)
                throw new FormatException("DTR-Evidence: source support definition was not admitted");
            material = definition.LoadTypeRepresentation();
            var (definitionParameters, typeStart) = InformationTemplateDefinitionReference.Parameters(material);
            const string body = "es(l0),value=";
            if (definitionParameters.Length != parameters.Length
                || !material.AsSpan(typeStart).StartsWith(body, StringComparison.Ordinal))
                throw new FormatException("DTR-Evidence: source support definition body differs");
            start = typeStart + body.Length;
            prefix = entryPoint.GetProperty("path").EnumerateArray().Select(x => x.GetString()!).ToArray();
            for (var i = 0; i < parameters.Length; i++) levels.Add(definitionParameters[i], parameters[i]);
        }
        var parser = new Parser(material, start, levels);
        var root = parser.Expression();
        foreach (var entry in entries.EnumerateArray())
        {
            var path = entry.GetProperty("path").EnumerateArray().Select(x => x.GetString()!).ToArray();
            if (path.Length <= prefix.Length || !path.Take(prefix.Length).SequenceEqual(prefix))
                throw new FormatException("DTR-Evidence: source support definition path differs");
            path = path[prefix.Length..];
            var node = root;
            foreach (var step in path.SkipLast(1)) node = node.Child(step);
            if (path.Length == 0 || path[^1] != "body" || node.Tag is not ("ep" or "el")
                || node.Mode != "bc")
                throw new FormatException("DTR-Evidence: source support binder mode differs");
            var domain = node.Child("domain");
            if (parser.Material(domain) != InformationTemplateJson.String(entry, "material"))
                throw new FormatException("DTR-Evidence: source support material differs from addressed binder");
        }
    }

    private sealed record Node(string Tag, string? Mode, int Start, int End, Node[] Children)
    {
        internal Node Child(string step)
        {
            var index = (Tag, step) switch
            {
                ("ea", "fn") => 0, ("ea", "arg") => 1,
                ("ep" or "el", "domain") => 0, ("ep" or "el", "body") => 1,
                ("ee", "type") => 0, ("ee", "value") => 1, ("ee", "body") => 2,
                ("ed" or "ej", "body") => 0,
                _ => throw new FormatException("DTR-Evidence: source support path differs"),
            };
            return Children[index];
        }
    }

    private sealed class Parser(string text, int position, Dictionary<string, string> levels)
    {
        private int work = 524288;
        private readonly List<(int Start, int End, string Value)> substitutions = [];
        internal string Material(Node node)
        {
            var result = new System.Text.StringBuilder();
            var start = node.Start;
            foreach (var (from, to, value) in substitutions.Where(s => s.Start >= node.Start && s.End <= node.End))
            {
                result.Append(text.AsSpan(start, from - start)).Append(value);
                start = to;
            }
            return result.Append(text.AsSpan(start, node.End - start)).ToString();
        }
        private void Debit(int depth)
        {
            if (--work < 0 || depth > 256) throw Error();
        }
        private static FormatException Error() => new("DTR-Evidence: invalid canonical source material");
        private bool Take(string token)
        {
            if (!text.AsSpan(position).StartsWith(token, StringComparison.Ordinal)) return false;
            position += token.Length;
            return true;
        }
        private void Need(string token) { if (!Take(token)) throw Error(); }
        private string Number()
        {
            var start = position;
            while (position < text.Length && char.IsAsciiDigit(text[position])) position++;
            if (position == start || position > start + 1 && text[start] == '0') throw Error();
            return text[start..position];
        }
        private void Name()
        {
            _ = CanonicalLeanNameDecoder.ComponentsPrefix(text, position, out var size);
            position += size;
        }
        private void Level(int depth)
        {
            Debit(depth);
            if (Take("l0")) return;
            if (Take("ls(")) Level(depth + 1);
            else if (Take("lm(") || Take("li(")) { Level(depth + 1); Need(","); Level(depth + 1); }
            else if (Take("lp("))
            {
                var start = position;
                Name();
                if (levels.TryGetValue(text[start..position], out var name))
                    substitutions.Add((start, position, name));
            }
            else if (Take("lv(")) Name();
            else throw Error();
            Need(")");
        }
        internal Node Expression(int depth = 0)
        {
            Debit(depth);
            var start = position;
            if (position + 3 > text.Length) throw Error();
            var tag = text.Substring(position, 2);
            position += 2;
            Need("(");
            string? mode = null;
            var children = new List<Node>();
            void Expr() => children.Add(Expression(depth + 1));
            switch (tag)
            {
                case "eb": Number(); break;
                case "ef": case "em": Name(); break;
                case "es": Level(depth + 1); break;
                case "ec":
                    Name(); Need(",[");
                    if (!Take("]")) { do { Level(depth + 1); } while (Take(",")); Need("]"); }
                    break;
                case "ea": Expr(); Need(","); Expr(); break;
                case "ep": case "el":
                    if (position + 2 > text.Length) throw Error();
                    mode = text.Substring(position, 2); position += 2;
                    if (mode is not ("bd" or "bi" or "bs" or "bc")) throw Error();
                    Need(","); Expr(); Need(","); Expr(); break;
                case "ee":
                    if (Number() is not ("0" or "1")) throw Error();
                    Need(","); Expr(); Need(","); Expr(); Need(","); Expr(); break;
                case "ed": Expr(); break;
                case "ej": Name(); Need(","); Number(); Need(","); Expr(); break;
                case "ei":
                    if (Take("ln(")) Number();
                    else if (Take("lt("))
                    {
                        if (!int.TryParse(Number(), NumberStyles.None, CultureInfo.InvariantCulture, out var count)) throw Error();
                        Need(":");
                        while (count > 0)
                        {
                            if (System.Text.Rune.DecodeFromUtf16(text.AsSpan(position), out var rune, out var size)
                                != System.Buffers.OperationStatus.Done || rune.Utf8SequenceLength > count) throw Error();
                            position += size; count -= rune.Utf8SequenceLength;
                        }
                    }
                    else throw Error();
                    Need(")"); break;
                default: throw Error();
            }
            Need(")");
            return new(tag, mode, start, position, children.ToArray());
        }
    }
}
