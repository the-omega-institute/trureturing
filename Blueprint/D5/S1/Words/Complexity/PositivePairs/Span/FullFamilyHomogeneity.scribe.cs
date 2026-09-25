using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Complexity.PositivePairs.Span;

internal sealed class PositivePairsSpanFullFamilyHomogeneityDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S1/Words/Complexity/PositivePairs/Span/FullFamilyHomogeneity";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Words/nilforoushanparvaresh2026kdecks");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual full-family leading differences are homogeneous in their true degree.",
        H("FullFamilyHomogeneity"),
        Blocks(
            Paragraph(Text(
                "The classical Lyndon bracket basis motivates the target directions. The new "
                + "content here is realizability by the complete family of actual recursively "
                + "generated positive-word pairs, without quotienting duplicate indices.")),
            D("rational-homogeneous", "RationalHomogeneous", "Rational homogeneous polynomials",
                "RationalHomogeneous p r means every free word in the coefficient support of p has length r.", DescribeRole.Definition),
            D("actual-leading-difference", "actualLeadingDifference", "An actual indexed leading difference",
                "For finite A, level r, and a PositivePairIndex, actualLeadingDifference lifts the complete degree-r cutoff difference cutoffMagnus(u)-cutoffMagnus(v) to the full rational word algebra.", DescribeRole.Definition),
            D("full-family-span", "fullFamilySpan", "Span of the full actual family",
                "fullFamilySpan A r is the Q-submodule spanned by the range of actualLeadingDifference over every PositivePairIndex A r.", DescribeRole.Definition))));

    private static DocumentBlock.Describe D(string id, string declaration, string title,
        string prose, DescribeRole role = DescribeRole.Theorem, bool literature = false) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Module + "." + declaration),
            H(title), StatementSource.FromAuthor(Disp(F.Id(declaration.Replace("_", string.Empty)))),
            literature ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role);
}
