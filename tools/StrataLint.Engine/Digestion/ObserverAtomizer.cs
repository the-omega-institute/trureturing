namespace StrataLint.Engine;

internal static class ObserverAtomizer
{
    internal static AtomizedTheoryDocument Atomize(ReadOnlySpan<byte> bytes, TheoryAtomizerRules rules)
    {
        ArgumentNullException.ThrowIfNull(rules);
        var document = MarkdownAstAtomizer.Atomize(
            bytes,
            paragraph => Identify(paragraph, rules),
            identifyFirstTableCellSource: paragraph => Identify(paragraph, rules));
        if (document.Claims.Any(atom =>
                atom.AstPath.Contains("/occurrence/", StringComparison.Ordinal)))
        {
            throw new TheorySourceFormatException("duplicate observer claim locator");
        }

        return document;
    }

    private static string? Identify(string paragraph, TheoryAtomizerRules rules)
    {
        foreach (var mapping in rules.ObserverClaimPrefixes)
        {
            if (paragraph.StartsWith(mapping.Token, StringComparison.Ordinal))
            {
                return mapping.Value;
            }
        }

        if (HasBoldClaimLead(paragraph))
        {
            throw new TheorySourceFormatException(
                $"unknown observer claim lead '{TheorySourceFormatException.ClaimLead(paragraph)}'");
        }
        return null;
    }

    private static bool HasBoldClaimLead(string paragraph)
    {
        var index = 0;
        while (index < paragraph.Length && paragraph[index] is ' ' or '\t')
        {
            index++;
        }
        return paragraph.AsSpan(index).StartsWith("**", StringComparison.Ordinal);
    }
}
