using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Digit;

internal sealed class DigitCapLeastCapDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Digit/DigitCapLeastCap.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Digit/coons2026calkinwilf");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The least digit cap whose upper growth exponent reaches r−1 is ell^r−1, and the least "
            + "cap whose counts grow at least linearly is ell²−1.",
        H("The least digit caps for polynomial and linear growth"),
        Blocks(
            Describe.Lean(DescribeId.Create("digit-cap-least-cap-result"),
                DeclarationHandle.Create(Prefix + "least_cap"),
                H("The least cap with upper exponent r−1"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "For ell ≥ 2 and r ≥ 2, ell^r−1 is the least cap k whose upper exponent "
                    + "limsup log b(k,ell,n)/log n is at least r−1. The cap ell^r−1 has at least "
                    + "n^(r−1)/C representations for large n by the Θ(n^(r−1)) bound, so along "
                    + "every tail log b/log n comes arbitrarily close to r−1 from below. Every "
                    + "cap k ≤ ell^r−2 has b(k,ell,n) = O(n^e) with e = (log_ell H)/2 < r−1, so "
                    + "its upper exponent is at most a value strictly between e and r−1. With "
                    + "the exact count n/ell+1 at the cap ell²−1, the case r = 2 answers CW2 of "
                    + "M. Coons, which he lists as open, in the sense that no smaller cap has "
                    + "upper exponent at least 1. The statement is Corollary 2 of the outreach "
                    + "note registered with the request."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("digit-cap-least-cap-linear-min"),
                DeclarationHandle.Create(Prefix + "least_linear_min"),
                H("The least cap with linear minimal growth"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "For ell ≥ 2, ell²−1 is the least cap k with c·n ≤ b(k,ell,n) for some "
                    + "c > 0 and all large n. At ell²−1 the count is exactly ⌊n/ell⌋+1. For a "
                    + "smaller cap the count is O(n^e) with e < 1, and c·n ≤ C·n^e fails once "
                    + "(1−e)·log n exceeds |log C|+|log c|. This is CW3 of M. Coons, answered by "
                    + "his Theorem 1."))),
                DescribeRole.Theorem))));
}
