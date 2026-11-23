using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Attribution.AxisBudgets;

internal sealed class DimensionFourteenAttainmentDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/ConceptDynamics/Attribution/AxisBudgets/DimensionFourteenAttainment.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An explicit fourteen-coordinate factor attains the lower bound of two ordinary rank jumps.",
        H("Attainment with two ordinary rank jumps"),
        Blocks(
            Entry("attainment", "AttainsTwoJumpsAt640", "Attainment at coordinate zero",
                "Take two copies of the subsets of the thirteen free coordinates and mark coordinate "
                + "zero in dimension fourteen. There exist a Boolean factor and one common Boolean "
                + "choice for the marked edge. The full-subset loop is absent. The unselected mode "
                + "allows degree one at both full-subset endpoints, and the selected mode allows "
                + "degree zero or two at each. Ordinary rows and columns have degree one or three. "
                + "Every true entry outside the full-subset row is supported on inclusion. The cost "
                + "is four times the sum of one and the number of true entries from ordinary odd-rank "
                + "rows to odd-rank columns. It is at most 640. Exactly two true entries in ordinary "
                + "rows have target rank at least two greater than the source rank.",
                DescribeRole.Definition),
            Entry("infeasibility-claim", "claim", "The claimed absence of an attaining factor",
                "There is no such factor with exactly two ordinary rank jumps.", DescribeRole.Definition),
            Entry("refutation", "result", "A checked factor refutes the claim",
                "The claimed absence of an attaining factor is false. The packed row and column lists "
                + "specify a factor on two copies of the 8192 free-coordinate "
                + "subsets. The block checks verify the entry agreement, degree conditions, inclusion, "
                + "and total charge of 159 ordinary entries. Outside the exceptional row, only the "
                + "entries from mask 15 to 63 and from mask 255 to 1023 can skip a rank. The lower "
                + "bound already forces two ordinary jumps, so the factor attains it.",
                DescribeRole.Theorem))));

    private static DocumentBlock.Describe Entry(string id, string declaration, string title, string statement,
        DescribeRole role) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Owner + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(statement))), role);
}
