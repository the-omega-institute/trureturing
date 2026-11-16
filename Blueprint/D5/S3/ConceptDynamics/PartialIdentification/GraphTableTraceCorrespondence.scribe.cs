using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.PartialIdentification;

internal sealed class GraphTableTraceCorrespondenceDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ConceptDynamics/PartialIdentification/GraphTableTraceCorrespondence.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "At a fixed exogenous state, a parent-ordered structural model is encoded by graph-local equation tables. One realization with an independent fixed seed preserves every hard-intervention outcome simultaneously.",
        H("Graph-table trace correspondence"),
        Blocks(
            Paragraph(Text(
                "The exogenous carrier of the realization is the full family of graph-local response tables. "
                    + "The realization keeps the original graph and certified order. Its equation reads the supplied table at the node and parent assignment; its explicit seed is fixed independently of the original initialization.")),
            Paragraph(Text(
                "The arbitrary-start theorem compares two traces whose initial states may differ. "
                    + "Induction on the order propagates agreement over the processed prefix; the topological certificate supplies the parent locality needed at the next update.")),
            Describe.Lean(
                DescribeId.Create("graph-table-model"),
                DeclarationHandle.Create(Prefix + "graphTableModel"),
                H("Graph-table structural model"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The model uses the supplied parent graph and a table-valued shared exogenous state, "
                        + "with equation value r(v, pa) and the explicit seed as its initial state."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("arbitrary-start-trace-uniqueness"),
                DeclarationHandle.Create(Prefix + "evaluation_witness_result_unique_from_arbitrary_start"),
                H("Parent-ordered traces agree from arbitrary initial states"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For one model, intervention, assignment, and exogenous state, any two EvaluationWitness traces "
                        + "along the certified complete order have the same final assignment even when their initial states differ."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("shared-seed-trace-correspondence"),
                DeclarationHandle.Create(Prefix + "graph_table_shared_seed_trace_correspondence"),
                H("One graph-table seed serves every intervention world"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For an original model M at one shared exogenous state u, encode each table entry by M.equation(v, pa, u). This single encoding serves every hard intervention and assignment. "
                        + "Every original-model trace, including the trace from M.initial(u), has the same completed output as the realized table-model trace from the fixed seed. The proof transports the original trace to the table model and then applies arbitrary-start uniqueness. This deterministic correspondence does not construct probability laws, a full seven-output compiler, nested interventions, or heterogeneous value types."))),
                DescribeRole.Theorem))));
}
