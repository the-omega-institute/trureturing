using System.Collections.Immutable;

namespace StrataLint.Engine;

internal static class ScribeDescribeContract
{
    private static readonly ImmutableHashSet<string> LatexRequiredKinds =
        ImmutableHashSet.Create(StringComparer.Ordinal, "theorem", "proposition", "lemma");

    internal static bool RequiresLatex(string kind)
    {
        ArgumentException.ThrowIfNullOrWhiteSpace(kind);
        return LatexRequiredKinds.Contains(kind);
    }
}
