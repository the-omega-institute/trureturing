using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Complexity;

internal sealed class PositivePairFullFamilySpanDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S1/Words/Complexity/PositivePairFullFamilySpan";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Words/nilforoushanparvaresh2026kdecks");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The complete indexed family of actual positive-pair leading differences spans every rationalized Lyndon standard bracket and is stable under literal power substitution.",
        H("Full Actual Positive-Pair Span"),
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
                "fullFamilySpan A r is the Q-submodule spanned by the range of actualLeadingDifference over every PositivePairIndex A r.", DescribeRole.Definition),
            D("every-standard-bracket-mem", "every_standardBracket_mem", "Every standard bracket is realized in the span",
                "For finite linearly ordered A and every word w, the rational coefficient extension of standardBracket w belongs to fullFamilySpan A w.length. The induction uses the actual successor commutator and does not assume an abstract free parameter family."),
            D("literal-power-word", "literalPowerWord", "Literal letter-power substitution",
                "literalPowerWord m source replaces every letter of source by m consecutive copies of that same letter.", DescribeRole.Definition),
            D("literal-power-positive-pair", "literalPowerSubstitution_actual_positivePair", "Power substitution preserves lower data and scales the lead",
                "For finite A with decidable equality, m,r, and every actual pair index, powering both pair words multiplies each length by m, preserves equal positive lengths at levels r>=2 when m>0, preserves all scattered counts below r, and scales every degree-r count difference by m^r, including degenerate levels.")),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S1/Words/Complexity/PositivePairWordCoefficients"))]));

    private static DocumentBlock.Describe D(string id, string declaration, string title,
        string prose, DescribeRole role = DescribeRole.Theorem) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Module + "." + declaration),
            H(title), StatementSource.FromAuthor(Disp(F.Id(declaration.Replace("_", string.Empty)))),
            AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text(prose))), role);
}
