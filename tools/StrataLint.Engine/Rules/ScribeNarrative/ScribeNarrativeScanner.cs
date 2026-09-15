using System.Collections.Immutable;
using System.Text;
using System.Text.RegularExpressions;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp;
using Microsoft.CodeAnalysis.CSharp.Syntax;
using Microsoft.CodeAnalysis.Text;

namespace StrataLint.Engine;

internal sealed record ScribeNarrativeFinding(string Class, string MatchedText, int Line, string Message);

internal static class ScribeNarrativeScanner
{
    private const string TheoryVolumeAlphabet = @"(?:pzg|gict|dect|bedc|fpod|qdo|cone)";

    internal static readonly Func<Rune, bool> CjkSourceCharacter = static rune => rune.Value is
        >= 0x2E80 and <= 0x2EFF // CJK Radicals Supplement: U+2E80-U+2EFF
        or >= 0x2F00 and <= 0x2FDF // Kangxi Radicals: U+2F00-U+2FDF
        or >= 0x3000 and <= 0x303F // CJK Symbols and Punctuation: U+3000-U+303F
        or >= 0x31C0 and <= 0x31EF // CJK Strokes: U+31C0-U+31EF
        // Enclosed CJK Letters and Months: U+3200-U+32FF; CJK Compatibility: U+3300-U+33FF
        or >= 0x3200 and <= 0x33FF
        or >= 0x3400 and <= 0x4DBF // CJK Unified Ideographs Extension A: U+3400-U+4DBF
        or >= 0x4E00 and <= 0x9FFF // CJK Unified Ideographs: U+4E00-U+9FFF
        or >= 0xF900 and <= 0xFAFF // CJK Compatibility Ideographs: U+F900-U+FAFF
        or >= 0xFE10 and <= 0xFE1F // Vertical Forms: U+FE10-U+FE1F
        or >= 0xFE30 and <= 0xFE4F // CJK Compatibility Forms: U+FE30-U+FE4F
        or >= 0xFE50 and <= 0xFE6F // Small Form Variants: U+FE50-U+FE6F
        or >= 0xFF00 and <= 0xFFEF // Halfwidth and Fullwidth Forms: U+FF00-U+FFEF
        // Pinned U+20000-U+2FA1F span, including gaps between these blocks:
        // CJK Unified Ideographs Extension B: U+20000-U+2A6DF; C: U+2A700-U+2B73F;
        // D: U+2B740-U+2B81F; E: U+2B820-U+2CEAF; F: U+2CEB0-U+2EBEF; I: U+2EBF0-U+2EE5F;
        // CJK Compatibility Ideographs Supplement: U+2F800-U+2FA1F.
        or >= 0x20000 and <= 0x2FA1F
        // CJK Unified Ideographs Extension G: U+30000-U+3134F; H: U+31350-U+323AF.
        or >= 0x30000 and <= 0x323AF;

    internal static readonly NarrativeClass DigestionLedgerReference = new(
        nameof(DigestionLedgerReference), "digestion ledger",
        Pattern(@"\b(?:Meta/Digestion|atom_id|coverage_gids|chain_atoms|cas_ref|residual-open|partial-closed|absorbed-closed|nonpropositional-inapplicable|accepted-event|subitems?|unresolved_subitems|digestion|backfill)\b"
            + @"|\batoms?\s+(?:sha256:)?[0-9a-f]{40,64}\b"
            + @"|\b[a-z][a-z0-9-]*-residual-[0-9a-f]{8,}\b"
            + @"|\b(?:theorem|definition|lemma|corollary|remark|proposition|section|appendix)/\d+(?:\.\d+)*\b"),
        Grammar:
        [
            // This Block rule favors precision: fixed documentary forms, with bounded clause-local relations.
            // The object slot is a closed alphabet of documentary modifiers (no prepositions): 'formalizes the
            // mass of the source atom' must not match, because the atom there is a prepositional complement.
            Pattern(@"\b(?:source|corollary|deposited|container|anchor|candidate|ingested|host|multi-clause|same|that|this|the)\s+atoms?\s+"
                + @"(?:(?:(?:also|only|itself|explicitly|merely|already|still)\s+)?(?:does\s+not\s+|never\s+)?asserts?"
                + @"|carries\s+(?:a|the|no)\s+(?:pre-committed\s+)?(?:receipt|numerical\s+certificate|clause|claim))\b"),
            Pattern(@"\b(?:closes|closing|discharges?|discharged|formaliz(?:es|ed|e|ing)|digests?|digested|does\s+not\s+(?:close|formalize|discharge))\s+(?:only\s+)?(?:the|this|that|its|each|every|a|an)\s+(?:(?:only|multi-clause|corollary|finite-decision|first|second|third|remaining|other|same|whole|entire|full|partial|stated|listed|named|numbered|quoted|corresponding|underlying|original|deposited|ingested|cited|referenced|unresolved)\s+){0,3}(?:(?:multi-clause|corollary|source|deposited|container|anchor|candidate|host|ingested|generic|same)\s+)?atoms?\b"
                + @"|\b(?:closes?|covers?)\s+only\s+the\s+[\w-]+\s+(?:clause|subitem|claim|statement)s?\s+of\s+(?:the\s+)?(?:multi-clause|corollary|source|deposited|container|anchor|candidate|host|ingested)\s+atoms?\b"
                + @"|\bmulti-clause\s+(?:corollary\s+)?atoms?\b"),
            Pattern(@"\batoms?'s\s+(?:proof\s+skeleton|separate\s+claims?|claims?|clauses?|subitems?|statements?|registration|traceability\s+demand|compatibility\s+claim|theorem\s+name|numerical\s+certificates?|explicit\s+diagonal\s+property)\b"
                + @"|\b(?:stated|asserted)\s+(?:elsewhere\s+)?in\s+(?:that|the\s+same|this)\s+atoms?\b"
                + @"|\bregistration\s+statements?\s+in\s+(?:that|the\s+same|this)\s+atoms?\b"
                + @"|\b(?:clauses?|subitems?)\s+(?:in|of)\s+(?:that|the\s+same|this|the\s+source|the\s+corollary)\s+atoms?\b")
        ]);

    internal static readonly NarrativeClass TheoryVolumeReference = new(
        nameof(TheoryVolumeReference), "theory volume",
        Pattern(@"\b(?:docs/develop/theory|theory\s+volumes?)\b"
            + @"|\b" + TheoryVolumeAlphabet + @"\b\s+(?:\d+(?:\.\d+)*|(?:Theorem|Remark|Definition|Proposition|Lemma|Corollary|Section|part|volume|source|line)\s+\d+(?:\.\d+)*|v\d+)\b"
            + @"|\b" + TheoryVolumeAlphabet + @"-v\d+(?:\.\d+)*\b"));

    internal static readonly NarrativeClass GovernanceProcessReference = new(
        nameof(GovernanceProcessReference), "governance process",
        Pattern(@"\b(?:issue\s*#?\s*\d{3,}|PR\s+#\d+|pull\s+request|panel\s+brief|dispatch\s+brief|orchestrator|six-route|proof_shape|admission_basis|escape[ _-]witness|bind-only|postmortem|git-history|accepted-event\s+receipts?)\b"),
        Pattern(@"\bsearch(?:es)?\b"), Pattern(@"\bduplicate\b"));

    internal static ImmutableArray<ScribeNarrativeFinding> Scan(string source)
    {
        ArgumentNullException.ThrowIfNull(source);
        var findings = new List<ScribeNarrativeFinding>();
        var root = CSharpSyntaxTree.ParseText(source).GetCompilationUnitRoot();
        var carriers = Carriers(root).ToArray();

        AddCjk(new Carrier([new TextPart(source, 1, true)]), findings);
        foreach (var carrier in carriers) AddCjk(carrier, findings);

        foreach (var carrier in carriers)
        {
            AddNarrative(DigestionLedgerReference, carrier, findings);
            AddNarrative(TheoryVolumeReference, carrier, findings);
            AddNarrative(GovernanceProcessReference, carrier, findings);
        }

        return findings.Distinct().OrderBy(f => f.Line).ThenBy(f => f.Class, StringComparer.Ordinal)
            .ThenBy(f => f.MatchedText, StringComparer.Ordinal).ToImmutableArray();
    }

    private static void AddCjk(Carrier carrier, List<ScribeNarrativeFinding> findings)
    {
        var offset = 0;
        foreach (var rune in carrier.Text.EnumerateRunes())
        {
            if (CjkSourceCharacter(rune))
            {
                var line = carrier.LineAt(offset);
                findings.Add(new(nameof(CjkSourceCharacter), rune.ToString(), line,
                    $"CjkSourceCharacter U+{rune.Value:X4} '{rune}' (line {line}): Blueprint Scribe source must not contain CJK characters"));
            }
            offset += rune.Utf16SequenceLength;
        }
    }

    private static void AddNarrative(NarrativeClass rule, Carrier carrier, List<ScribeNarrativeFinding> findings)
    {
        foreach (var pattern in new[] { rule.Direct }.Concat(rule.Grammar ?? []))
            foreach (Match match in pattern.Matches(carrier.Text)) Add(match.Value, match.Index);
        if (rule.Subject is null || rule.Relation is null) return;
        var start = 0;
        for (var end = 0; end <= carrier.Text.Length; end++)
        {
            if (end < carrier.Text.Length && carrier.Text[end] is not ('.' or ';' or ':' or '!' or '?')) continue;
            var sentence = carrier.Text[start..end];
            if (rule.Subject.IsMatch(sentence) && rule.Relation.IsMatch(sentence))
            {
                var trimmed = sentence.Trim();
                Add(trimmed, start + sentence.IndexOf(trimmed, StringComparison.Ordinal));
            }
            start = end + 1;
        }

        void Add(string text, int offset)
        {
            var line = carrier.LineAt(offset);
            findings.Add(new(rule.Name, text, line,
                $"{rule.Name} '{text}' (line {line}): Scribe prose must derive from the Lean declaration, not from the {rule.Layer}"));
        }
    }

    private static IEnumerable<Carrier> Carriers(SyntaxNode root)
    {
        foreach (var trivia in root.DescendantTrivia())
        {
            if (trivia.Kind() is SyntaxKind.SingleLineCommentTrivia or SyntaxKind.MultiLineCommentTrivia
                or SyntaxKind.SingleLineDocumentationCommentTrivia or SyntaxKind.MultiLineDocumentationCommentTrivia)
                yield return new Carrier([new TextPart(trivia.ToFullString(),
                    trivia.GetLocation().GetLineSpan().StartLinePosition.Line + 1, true)]);
        }
        foreach (var carrier in ExpressionCarriers(root)) yield return carrier;
    }

    private static IEnumerable<Carrier> ExpressionCarriers(SyntaxNode node)
    {
        if (node is ExpressionSyntax expression && TryRead(expression, out var parts))
        {
            yield return new Carrier(parts);
            yield break;
        }
        if (node is InterpolatedStringTextSyntax text)
        {
            yield return new Carrier([Part(text.TextToken)]);
            yield break;
        }
        foreach (var child in node.ChildNodes())
            foreach (var carrier in ExpressionCarriers(child)) yield return carrier;
    }

    private static bool TryRead(ExpressionSyntax expression, out List<TextPart> parts)
    {
        parts = [];
        switch (expression)
        {
            case LiteralExpressionSyntax literal when literal.IsKind(SyntaxKind.StringLiteralExpression)
                || literal.IsKind(SyntaxKind.Utf8StringLiteralExpression):
                parts.Add(Part(literal.Token));
                return true;
            case ParenthesizedExpressionSyntax parenthesized:
                return TryRead(parenthesized.Expression, out parts);
            case BinaryExpressionSyntax binary when binary.IsKind(SyntaxKind.AddExpression)
                && TryRead(binary.Left, out var left) && TryRead(binary.Right, out var right):
                parts.AddRange(left);
                parts.AddRange(right);
                return true;
            case InterpolatedStringExpressionSyntax interpolation
                when interpolation.Contents.All(content => content is InterpolatedStringTextSyntax):
                parts.AddRange(interpolation.Contents.Cast<InterpolatedStringTextSyntax>().Select(t => Part(t.TextToken)));
                return true;
            default:
                return false;
        }
    }

    private static TextPart Part(SyntaxToken token)
    {
        var line = token.GetLocation().GetLineSpan().StartLinePosition.Line + 1;
        if (token.Kind() is SyntaxKind.MultiLineRawStringLiteralToken or SyntaxKind.Utf8MultiLineRawStringLiteralToken)
            line++;
        return new TextPart(token.ValueText, line, token.Text.IndexOfAny(['\r', '\n']) >= 0);
    }

    private static Regex Pattern(string pattern) => new(pattern,
        RegexOptions.IgnoreCase | RegexOptions.CultureInvariant | RegexOptions.NonBacktracking);

    internal sealed record NarrativeClass(string Name, string Layer, Regex Direct,
        Regex? Subject = null, Regex? Relation = null,
        Regex[]? Grammar = null);

    private sealed record TextPart(string Value, int Line, bool PhysicalNewlines)
    {
        internal SourceText? PhysicalText { get; } = PhysicalNewlines ? SourceText.From(Value) : null;
    }

    private sealed class Carrier(List<TextPart> parts)
    {
        internal string Text { get; } = string.Concat(parts.Select(p => p.Value));

        internal int LineAt(int offset)
        {
            foreach (var part in parts)
            {
                if (offset < part.Value.Length)
                    return part.Line + (part.PhysicalText?.Lines.GetLinePosition(offset).Line ?? 0);
                offset -= part.Value.Length;
            }
            return parts.Count == 0 ? 1 : parts[^1].Line;
        }
    }
}
