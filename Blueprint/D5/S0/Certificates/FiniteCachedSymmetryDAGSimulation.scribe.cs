using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Certificates;

internal sealed class FiniteCachedSymmetryDAGSimulationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S0/Certificates/FiniteCachedSymmetryDAGSimulation.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Fuel-indexed simulation of actual-context cached replay",
        H("Fuel-indexed simulation of actual-context cached replay"),
        Blocks(
            Paragraph(Text("A separately indexed literal suffix can be connected to an original DAG by proving that corresponding nodes have the same bound test, symmetry action or split coordinate, and that every split successor remains related at the next fuel. The theorem retains the same gap, lower-bound function, cache transitions and actual partial assignments. A shared node shape never transfers arithmetic acceptance between different contexts.")),
            Node("step-related", "StepRelated", "Corresponding nodes preserve every value branch",
                "Bound nodes correspond to bound nodes and symmetry nodes carry the same action. Split nodes carry the same coordinate and related successors for every possible value. The relation can depend on the remaining fuel in the simulation theorem.", DescribeRole.Definition),
            Node("checked-simulation", "checked_simulation", "Accepted literal replay transfers to aligned original nodes",
                "Induction on the remaining fuel transfers bound and symmetry tests unchanged. Each split consumes every source branch receipt and recurses with exactly the same cache step and partial update on both sides. Exhausted fuel rejects. Concrete node alignment and source acceptance must both be proved; neither a native verdict nor a producer hash supplies them.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
