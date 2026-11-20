using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Queries;

internal sealed class BranchingPathPosteriorDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A disclosure can return to a branching vertex and use its other slot.",
        H("The graph posterior after a branching disclosure"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("incoming"),
                DeclarationHandle.Create(
                    "D5/S3/Combinatorics/Graph/Queries/BranchingPathPosterior.incoming"),
                H("The incoming pair for a request"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The requested position and the number of already recorded edges select " +
                    "an entry in the history. Use that directed edge as the incoming pair, " +
                    "and use the given initial pair if the index is outside the history."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("graph-branching-posterior"),
                DeclarationHandle.Create(
                    "D5/S3/Combinatorics/Graph/Queries/BranchingPathPosterior.graph_branching_posterior"),
                H("Condition on all the disclosed edges"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Each world supplies a simple graph on a common vertex set, with one " +
                        "common initial edge. Fix a schedule of requests at finitely many " +
                        "positions. At each position, an independent uniform permutation of " +
                        "two slots selects among two distinct candidates for the incoming pair. " +
                        "The pair can refer to an earlier edge, selected by the position and " +
                        "the current length of the disclosure. Prepend each returned edge " +
                        "to the history.")),
                    Paragraph(Text(
                        "For the given reference run, each position uses the same incoming " +
                        "pair whenever it is visited. Each recorded vertex differs from its " +
                        "predecessor. The observed slot table records exactly the reference " +
                        "rows, and the seen set records exactly the observed positions. For " +
                        "any world containing a reference row's incoming edge, its reported " +
                        "vertex is available exactly when it is an adjacent forward vertex.")),
                    Paragraph(Text(
                        "If the reference disclosure has positive mass, the posterior of " +
                        "a world event is its prior mass restricted to worlds containing every " +
                        "recorded edge and divided by the prior mass of that restriction.")),
                    Paragraph(Text(
                        "Replay tests the reference values at their actual histories. " +
                        "Inductively, these histories supply valid incoming edges whenever " +
                        "the graph contains every edge already disclosed. The distinct " +
                        "reference slot values at a twice observed position then give the " +
                        "required compatibility. The likelihood for a compatible graph " +
                        "depends only on the number of observed positions, so it cancels."))),
                DescribeRole.Theorem))));
}
