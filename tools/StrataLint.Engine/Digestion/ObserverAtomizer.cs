namespace StrataLint.Engine;

internal static class ObserverAtomizer
{
    internal static AtomizedTheoryDocument Atomize(ReadOnlySpan<byte> bytes, TheoryAtomizerRules rules)
    {
        ArgumentNullException.ThrowIfNull(rules);
        var unregistered = new SortedSet<string>(StringComparer.Ordinal);
        var document = MarkdownAstAtomizer.Atomize(
            bytes,
            paragraph => Identify(paragraph, rules, unregistered),
            () => GenreRegistryCheck.Collected([.. unregistered]),
            identifyFirstTableCellSource: paragraph => Identify(paragraph, rules, unregistered));
        return document;
    }

    private static string? Identify(
        string paragraph,
        TheoryAtomizerRules rules,
        SortedSet<string> unregistered)
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
            var token = TheorySourceFormatException.ClaimLead(paragraph);
            unregistered.Add(token);
            return token;
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
