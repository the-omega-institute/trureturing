using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.AdmissibleWords;

internal sealed class FIBTwoSourceObstructionDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S1/Words/AdmissibleWords/FIBTwoSourceObstruction.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Two oriented differences compete for the same region of a containing event.",
        H("A joint bound from two sources"),
        Blocks(
            Describe.Lean(DescribeId.Create("capacity"), DeclarationHandle.Create(Owner + "shared_capacity"),
                H("Two disjoint differences under a shared capacity"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Let S and W be contained in both H and K, and let T be contained in K. "
                    + "With K of finite measure and S, H and T measurable, the sum of the masses "
                    + "of W outside S and T outside H is at most the mass of K minus the mass of S. "
                    + "The first difference lies in H and the second avoids H. Both lie in K outside S."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("five-vertices"),
                DeclarationHandle.Create(Owner + "five_vertex_range"),
                H("Exact joint range of the two differences"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For real q and c, prescribe Lebesgue mass q at S, T and W, and mass q plus c "
                    + "at H and K. All five events are measurable subsets of the half-open unit interval. "
                    + "Impose the inclusions of the shared capacity bound. A pair of difference "
                    + "masses a for W outside S and b for T outside H is realizable exactly when "
                    + "both are nonnegative and at most q, their sum is at most c, and b is at "
                    + "most the mass outside H. For attainment, reserve "
                    + "the last interval of length b in K for T outside H and replace it in H "
                    + "by an interval of the same length outside K. This leaves the interval "
                    + "needed by W outside S within both H and K. The inequalities imply "
                    + "that both q and c are nonnegative and q plus c is at most one."))),
                DescribeRole.Theorem))));
}
