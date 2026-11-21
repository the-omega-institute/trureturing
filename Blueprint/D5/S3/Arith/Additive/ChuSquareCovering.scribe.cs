using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Additive;

internal sealed class ChuSquareCoveringDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Additive/ChuSquareCovering.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Digit/blancogomez2026coreoeis3");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Sets A, B of sizes a, b in {0, …, N − 1} with A + B covering {0, …, N − 1} exist exactly when "
        + "N ≤ ab, a ≤ N and b ≤ N; for N = n² and a = b the least size is n.",
        H("Additive covers of an initial interval"),
        Blocks(
            Describe.Lean(DescribeId.Create("chu-cover-sizes"),
                DeclarationHandle.Create(Prefix + "result"),
                H("All achievable pairs of sizes"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "For natural numbers N, a and b, there are sets A, B ⊆ {0, …, N − 1} with |A| = a, "
                        + "|B| = b and A + B ⊇ {0, …, N − 1} exactly when N ≤ ab, a ≤ N and b ≤ N.")),
                    Paragraph(Text(
                        "Necessity: N ≤ |A + B| ≤ |A| |B|, and A, B lie in a set of N elements. "
                        + "Sufficiency for a ≥ 1: every m < N is m mod a plus a multiple of a below N, so "
                        + "{0, …, a − 1} plus the multiples of a below N covers the interval; there are at "
                        + "most b such multiples because a multiple ja below N ≤ ab has j < b, and they are "
                        + "completed to b elements of the interval. For a = 0 the conditions force "
                        + "N = b = 0.")),
                    Paragraph(Text(
                        "With N = n² and a = b = k the condition reads n ≤ k ≤ n², so the least k is n. "
                        + "This is M. Chu's conjecture (2022) in OEIS A000290, proved as Proposition 9.1 of "
                        + "R. Blanco Gómez, Open statements in core entries of the OEIS, III (2026), for "
                        + "n ≥ 1; for n = 0 the least size is 0. The theorem extends the source's argument "
                        + "to every interval and every pair of sizes."))),
                DescribeRole.Theorem))));
}
