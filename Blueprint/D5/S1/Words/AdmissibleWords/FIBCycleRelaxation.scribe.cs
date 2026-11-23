using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.AdmissibleWords;

internal sealed class FIBCycleRelaxationDocument : IScribeDocumentDefinition
{
    private const string Result =
        "D5/S1/Words/AdmissibleWords/FIBCycleRelaxation.cycle_consistent_without_joint_law";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Cycle inequalities admit the two-source FIB observations that have no joint law.",
        H("A gap between cycle constraints and a joint law"),
        Blocks(
            Describe.Lean(DescribeId.Create("cycle-relaxation-gap"), DeclarationHandle.Create(Result),
                H("A cycle-consistent family outside the joint laws"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Let c be positive, c be at most q, and q plus twice c be at most one. "
                    + "Use a reference vertex with fixed bit zero, followed by S, H, K, T and W. "
                    + "The family prescribes marginals q at S, T and W and q plus c at H and K. "
                    + "The five inclusion edges have disagreement probability c. The two query "
                    + "edges WS and TH have disagreement probabilities twice c and three times c. "
                    + "In the displayed completion, every walk returning to its initial vertex "
                    + "on the opposite side pays total cost at least one, where a side change "
                    + "pays one minus the edge distance. This gives every odd-subset cycle inequality. "
                    + "The observed pairs admit no common law on the five binary events.")),
                    Paragraph(Text(
                    "The proof checks triangles and triangle perimeters for the reference cut "
                    + "and the normalized corner q equals c equals one third. Their convex mixture "
                    + "extends each requested profile. Those inequalities give the triangle law "
                    + "on vertices with Boolean sides. For a joint law the pentagonal cut inequality "
                    + "on the reference, S, H, K and W, combined with the triangle through T, binds "
                    + "the two queries. The displayed family violates that inequality by twice c."))),
                DescribeRole.Theorem))));
}
