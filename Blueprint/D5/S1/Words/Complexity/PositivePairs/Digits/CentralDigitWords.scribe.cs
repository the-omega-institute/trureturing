using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Complexity.PositivePairs.Digits;

internal sealed class PositivePairsDigitsCentralDigitWordsDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S1/Words/Complexity/PositivePairs/Digits/CentralDigitWords";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Words/nilforoushanparvaresh2026kdecks");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Direction-major and scale-minor digits build literal positive words.",
        H("CentralDigitWords"),
        Blocks(
            Paragraph(Text(
                "For each length r, ActualLyndonWord is the subtype of actual words of length r "
                + "that satisfy IsLyndon. The module publicly installs a lifted linear order on "
                + "this subtype and, for finite A, a Fintype instance obtained by injection into "
                + "length-r vectors. These two anonymous public instances support the cardinality "
                + "and deterministic selection below; the digit construction itself is a "
                + "repository result, not a claim attributed to the cited paper.")),
            D("digit-base", "digitBase", "Degree-dependent digit base",
                "digitBase r is 2^r.", DescribeRole.Definition),
            D("digit-array", "DigitArray", "Complete direction-scale digit arrays",
                "DigitArray A r t is the function space assigning a base-2^r digit to every selected actual direction and every scale below t.", DescribeRole.Definition),
            D("digit-value", "digitValue", "A direction's encoded natural",
                "digitValue reads the t digits of one direction in base digitBase r using Nat.ofDigits.", DescribeRole.Definition),
            D("digit-block", "digitBlock", "An actual positive-word digit block",
                "For a selected pair (u,v), scale s, and digit j, digitBlock concatenates j copies of the 2^s literal power of u and digitBase r-1-j copies of the matching power of v.", DescribeRole.Definition),
            D("multi-scale-word", "multiScaleWord", "The complete multi-scale positive word",
                "multiScaleWord concatenates every digitBlock in direction-major, scale-minor order; at t=0 the result is the empty word.", DescribeRole.Definition),
            D("reference-word", "referenceWord", "The zero-digit reference word",
                "referenceWord A r t is multiScaleWord at the all-zero digit array, hence uses the powered v-side in every block.", DescribeRole.Definition),
            D("base-length", "baseLength", "Common-length coefficient",
                "baseLength A r is (2^r-1) times the sum of the selected u-word lengths and is the fixed coefficient in the multi-scale length law.", DescribeRole.Definition))));

    private static DocumentBlock.Describe D(string id, string declaration, string title,
        string prose, DescribeRole role = DescribeRole.Theorem, bool literature = false) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Module + "." + declaration),
            H(title), StatementSource.FromAuthor(Disp(F.Id(declaration.Replace("_", string.Empty)))),
            literature ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role);
}
