using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Certificates;

internal sealed class ShinFourPointCompressionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S0/Certificates/ShinFourPointCompression.";
    private static readonly LibraryNoteRef Shin =
        LibraryNoteRef.Create("D5/L/Certificates/shin2026iterated");
    private static readonly LibraryNoteRef Zhang =
        LibraryNoteRef.Create("D5/L/Certificates/zhang2026sharp");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The eleven-fold sumset of {0,7,17,80} has 347 elements, a cardinality absent "
            + "from every four-element integer set in [0,79].",
        H("A negative answer to four-point sumset compression"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("four-point-compression-question"),
                DeclarationHandle.Create(Prefix + "claim"),
                H("The affirmative proposition"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Shin),
                Blocks(Paragraph(Text(
                    "For every natural h at least two and every four-element finite set A "
                        + "of integers, the proposition asks for a four-element integer set B "
                        + "in the closed interval from zero to D_h, with equal cardinalities "
                        + "of their h-fold sumsets. The bound D_h is choose(h+2,2), plus one "
                        + "when h is odd. Each sum uses exactly h elements, with repetition "
                        + "allowed; the zero-fold sumset is {0}. Scalar multiplication of "
                        + "each individual element would define a different operation.")),
                    Paragraph(Text(
                    "This is the affirmative answer to the unnumbered question after "
                        + "Corollary 10.5 and equation (193), also restated in Question 12.5 "
                        + "of the related source. It preserves only the number of distinct "
                        + "sums. It imposes no requirement to preserve the complete additive "
                        + "relation type, or to make the set primitive."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("four-point-compression-refuted"),
                DeclarationHandle.Create(Prefix + "result"),
                H("The cardinality 347 cannot be compressed to diameter 79"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Shin, Zhang),
                Blocks(Paragraph(Text(
                    "At h=11 the proposed bound is 79. The set {0,7,17,80} has an "
                        + "eleven-fold sumset of cardinality 347. For {0,a,b,c}, the sums "
                        + "are exactly i*a+j*b+k*c with nonnegative coefficients satisfying "
                        + "i+j+k at most eleven. The unused summands are zeros.")),
                    Paragraph(Text(
                    "A natural number records a finite set by its binary digits. Starting "
                        + "with the digit for zero, each addition step takes the union with "
                        + "the shifts by a, b and c. Induction identifies these digits with "
                        + "the actual repeated sumset in both directions. All sums are at "
                        + "most 880. Counting one bits in 111 bytes therefore counts every "
                        + "sum. The byte counts agree with binary-digit counts for every "
                        + "byte, and the count excludes 347 for every 0<a<b<c at most 79.")),
                    Paragraph(Text(
                    "Any four-element B in [0,79] has four increasing elements. Subtract "
                        + "its minimum to obtain {0,a,b,c} in the enumerated range. Repeated "
                        + "addition turns this translation into translation by eleven times "
                        + "the minimum, which preserves cardinality. Thus no such B can "
                        + "have the cardinality 347, contradicting the universal proposition. "
                        + "The argument does not determine the least diameter realizing "
                        + "every eleven-fold cardinality; in particular it does not assert "
                        + "that this diameter equals 80."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("shin-four-point-sumset-compression"),
                    ResolutionKind.Refuted)))));
}
