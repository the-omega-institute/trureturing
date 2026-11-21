using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Walks;

internal sealed class MeyerovitchYoungQ61DFAIntersectionDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Combinatorics/Graph/Walks/MeyerovitchYoungQ61DFAIntersection.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The finite-horizon DFA intersection encoding counts charged completed segments.",
        H("The DFA intersection encoding for Meyerovitch–Young Question 6.1"),
        Blocks(
            Paragraph(Text("Take a finite nonempty state space with deterministic transitions for every ordinary letter, a nonempty reset set, and a set of accepting states. For a family of complete automata, these are the disjoint union of their states, the initial states of its components, and the accepting states of its components, respectively. Alice has one vertex with an edge for each ordinary letter and a delimiter edge. Bob has one edge per ordered pair of states. The free-endpoint objective is the sum of integer costs along the paired walks. https://arxiv.org/html/2603.21449v1#S4.E6")),
            Paragraph(Text("An ordinary edge costs zero if it follows the deterministic transition and two otherwise. A delimiter edge ending in the reset set costs one if its departure state accepts and zero otherwise. A delimiter edge ending outside the reset set costs two.")),
            Describe.Lean(
                DescribeId.Create("matrix-minimum-eq-score"),
                DeclarationHandle.Create(Prefix + "matrixMinimum_eq_score"),
                H("Exact cost and minimizing endpoints"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For every word, the free-endpoint matrix minimum equals the number of charged completed segments. Its minimizing endpoints are exactly the states in the scan's current set.")),
                    Paragraph(Text("Start the scan at zero with the entire state space. An ordinary letter sends the current set through the deterministic transition and preserves the count. A delimiter adds one when all states in the current set accept, and then replaces the set by the reset set. The final unfinished segment contributes zero.")),
                    Paragraph(Text("At each prefix the actual endpoint score is obtained by minimizing over the departure state of the last edge. An ordinary letter preserves the minimum, and the only ways to attain it follow a cost-zero transition from a previous minimizer. At a delimiter the common score inside the reset set increases by one exactly when every previous minimizer accepts, because nonminimizers have integer scores at least one higher. Outside the reset set each score is two above the previous minimum."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("matrix-minimum-pos-iff"),
                DeclarationHandle.Create(Prefix + "matrixMinimum_pos_iff"),
                H("Detection of a charged segment"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The free-endpoint matrix minimum of a word is positive exactly when it has a delimiter whose preceding prefix leaves the scan's current state set contained in the accepting set. This recognizes a completed segment whose ordinary run accepts from every state in its starting set."))),
                DescribeRole.Theorem))));
}
