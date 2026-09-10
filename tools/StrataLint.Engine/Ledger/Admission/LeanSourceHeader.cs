using System.Collections.Immutable;
using System.Text;

namespace StrataLint.Engine;

internal sealed record LeanSourceImport(string Module, bool ImportAll, bool IsExported, bool IsMeta);

// The header language is fixed by Lean.Parser.Module.header. Stop before the body:
// notation-sensitive terms cannot affect import adjacency or its input address.
internal sealed record LeanSourceHeader(bool IsModule, bool Prelude,
    ImmutableArray<LeanSourceImport> Imports, int End)
{
    internal static LeanSourceHeader Read(string source)
    {
        var cursor = new HeaderCursor(source);
        var module = cursor.Take("module");
        var prelude = cursor.Take("prelude");
        var imports = ImmutableArray.CreateBuilder<LeanSourceImport>();
        if (!prelude)
        {
            imports.Add(new("Init", false, true, false));
            imports.Add(new("Init", false, true, true));
        }
        while (true)
        {
            var start = cursor.Position;
            var exported = cursor.Take("public");
            var meta = cursor.Take("meta");
            if (!cursor.Take("import"))
            {
                cursor.Position = start;
                break;
            }

            var all = cursor.Take("all");
            var name = cursor.Name();
            if (name.Length == 0 || (!module && (exported || meta || all)) || exported && all)
                throw new LeanSourceExtractionException("Lean import header is malformed.", cursor.Line);
            imports.Add(new(name, all, !module || exported, meta));
        }

        return new(module, prelude, imports.ToImmutable(), Encoding.UTF8.GetByteCount(source[..cursor.Position]));
    }

    private sealed class HeaderCursor(string source)
    {
        internal int Position { get; set; }
        internal int Line => 1 + source.AsSpan(0, Position).Count('\n');

        internal bool Take(string word)
        {
            Trivia();
            if (!source.AsSpan(Position).StartsWith(word, StringComparison.Ordinal)) return false;
            var end = Position + word.Length;
            if (end < source.Length && (char.IsLetterOrDigit(source[end]) || source[end] is '_' or '\'' or '.'))
                return false;
            Position = end;
            Trivia();
            return true;
        }

        internal string Name()
        {
            Trivia();
            var start = Position;
            while (Position < source.Length)
            {
                var c = source[Position];
                if (c == '«')
                {
                    Position++;
                    while (Position < source.Length && source[Position] != '»') Position++;
                    if (Position == source.Length)
                        throw new LeanSourceExtractionException("Lean import name is unterminated.", Line);
                    Position++;
                }
                else if (char.IsLetterOrDigit(c) || c is '_' or '\'' or '.' or '!' or '?') Position++;
                else break;
            }

            var raw = source[start..Position];
            var parts = LeanSourceTokenizer.IdentifierParts(raw);
            if (parts.IsEmpty) return string.Empty;
            Trivia();
            return LeanSourceTokenizer.IdentifierText(parts);
        }

        private void Trivia()
        {
            while (Position < source.Length)
            {
                if (char.IsWhiteSpace(source[Position]) || Position == 0 && source[Position] == '\uFEFF')
                    Position++;
                else if (source.AsSpan(Position).StartsWith("--", StringComparison.Ordinal))
                {
                    while (Position < source.Length && source[Position] != '\n') Position++;
                }
                else if (source.AsSpan(Position).StartsWith("/-", StringComparison.Ordinal)
                    && !source.AsSpan(Position).StartsWith("/-!", StringComparison.Ordinal)
                    && !source.AsSpan(Position).StartsWith("/--", StringComparison.Ordinal))
                {
                    var line = Line;
                    var depth = 1;
                    Position += 2;
                    while (Position < source.Length && depth > 0)
                    {
                        if (source.AsSpan(Position).StartsWith("/-", StringComparison.Ordinal))
                        { depth++; Position += 2; }
                        else if (source.AsSpan(Position).StartsWith("-/", StringComparison.Ordinal))
                        { depth--; Position += 2; }
                        else Position++;
                    }
                    if (depth != 0) throw new LeanSourceExtractionException("Lean block comment is unterminated.", line);
                }
                else break;
            }
        }
    }
}
