using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Certificates.BoxCover;

internal sealed class BoxCoverExamplesDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S0/Certificates/BoxCover/BoxCoverExamples.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A rational box forest confines a real squared-residual sublevel to its central interval.",
        H("A Concrete Squared-Residual Cover"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("square-boxes"),
                DeclarationHandle.Create(Module + "squareBoxes"),
                H("Five postordered rational intervals"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Nodes 0 through 4 have intervals [-2,-1], [1,2], [-1,1], "
                    + "[-1,2], and [-2,2], respectively. Each box has one coordinate; "
                    + "node 4 is the root."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("square-targets"),
                DeclarationHandle.Create(Module + "squareTargets"),
                H("The central target interval"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("There is one target box, with rational endpoints -1 and 1."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("square-residual"),
                DeclarationHandle.Create(Module + "squareResidual"),
                H("The square of the real coordinate"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The single residual expression squares input coordinate 0. Its input "
                    + "annotations are [-2,2], and its output annotations are [0,4]. "
                    + "Its real evaluation is x squared."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("square-forest"),
                DeclarationHandle.Create(Module + "squareForest"),
                H("Two exclusions, one covered leaf, and two splits"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Nodes 0 and 1 enclose the squared residual in [1,4] on their "
                    + "respective outer intervals. Node 2 enters target 0. Node 3 splits "
                    + "at 1 into nodes 2 and 1; node 4 splits at -1 into nodes 0 and 3. "
                    + "Both children precede each parent, and the split halves are closed."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("square-forest-accepted"),
                DeclarationHandle.Create(Module + "square_forest_accepted"),
                H("Exact acceptance at tolerance one quarter"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Kernel reduction proves that checkForest returns true for squareBoxes, "
                    + "squareTargets, squareResidual, tolerance 1/4, and squareForest. "
                    + "In particular, each excluded leaf has lower bound 1 strictly above 1/4."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("square-sublevel-covered"),
                DeclarationHandle.Create(Module + "square_sublevel_covered"),
                H("The real sublevel stays in the central interval"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The set of real x in [-2,2] with absolute value of x squared at most "
                    + "1/4 is contained in [-1,1]. The proof applies "
                    + "checked_forest_covers_sublevel to square_forest_accepted at root 4, "
                    + "then evaluates the single coordinate and target. "
                    + "The conclusion concerns all real points of this nonempty sublevel."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("escaped-sublevel-claim"),
                DeclarationHandle.Create(Module + "escapedSublevelClaim"),
                H("A proposed point outside the target"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The claim asserts that some real x belongs to [-2,2], satisfies "
                    + "the squared-residual bound 1/4, and does not belong to [-1,1]."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("no-escaped-sublevel"),
                DeclarationHandle.Create(Module + "no_escaped_sublevel"),
                H("No sublevel point escapes"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The claim is false: square_sublevel_covered places every proposed "
                    + "witness in [-1,1], contradicting its asserted nonmembership."))),
                DescribeRole.Theorem))));
}
