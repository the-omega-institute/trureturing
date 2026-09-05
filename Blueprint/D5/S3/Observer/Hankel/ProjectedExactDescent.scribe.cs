using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Hankel;

internal sealed class ProjectedExactDescentDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Global exact descent propagates through every driven time step and preserves outputs that factor through the projection.",
        H("Exact Descent Persists at Every Time"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("projected-state-eq-of-descent"),
                DeclarationHandle.Create("D5/S3/Observer/Hankel/ProjectedExactDescent.projectedState_eq_of_descent"),
                H("Exact projected states at every time"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The global operator identity P A=A_r P, together with the constructed reduced input P B, gives equality between every projected full state and reduced state. Both initial states are zero. This is a forced-input application of exact descent, and needs no contraction assumption."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("outputs-eq-of-descent"),
                DeclarationHandle.Create("D5/S3/Observer/Hankel/ProjectedExactDescent.outputs_eq_of_descent"),
                H("All factorized outputs are preserved"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("When the output also factors through P, exact descent preserves every output at every time. Full-state leakage can remain nonzero. Consequently a fixed global one-step exact descent cannot later fail solely because of hidden leakage. A one-trajectory check or a changing interface would require different hypotheses."))),
                DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(
            GidRef.Create("D5/S3/Observer/Hankel/ProjectedRealizationError"))]));
}
