using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Complexity.PositivePairs.Digits;

internal sealed class PositivePairsDigitsCentralDigitInjectionDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S1/Words/Complexity/PositivePairs/Digits/CentralDigitInjection";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Words/nilforoushanparvaresh2026kdecks");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Multi-scale central digits are injective with exact length control.",
        H("CentralDigitInjection"),
        Blocks(
            Paragraph(Text(
                "This module combines the private central-coefficient identities with linear "
                + "independence of the selected actual directions. Its public theorem packages "
                + "lower-degree agreement, the exact degree-r coordinate formula, injectivity, "
                + "digit-array cardinality, nonempty equal-length pairs, and exact word length.")),
            D("actual-positive-pair-central-digits", "actual_positivePair_multiScale_central_digits", "Full central-digit system from actual pairs",
                "For finite linearly ordered A, r,t:N, and 2<=r, the selected actual leading differences are linearly independent; every selected pair has two nonempty equal-length words; every digit word agrees with referenceWord below degree r; each degree-r coefficient difference is the indicated sum of digitValue times actualLeadingDifference; the cutoffMagnus digit map is injective; the digit-array cardinality is (2^r)^(t*actualLyndonCount A r); and every digit word has length baseLength A r*(2^t-1)."))));

    private static DocumentBlock.Describe D(string id, string declaration, string title,
        string prose, DescribeRole role = DescribeRole.Theorem, bool literature = false) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Module + "." + declaration),
            H(title), StatementSource.FromAuthor(Disp(F.Id(declaration.Replace("_", string.Empty)))),
            literature ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role);
}
