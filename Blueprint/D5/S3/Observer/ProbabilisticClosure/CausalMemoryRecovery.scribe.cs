using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.ProbabilisticClosure;

internal sealed class CausalMemoryRecoveryDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The full visible response, unlike its scalar trace, recovers the actual causal memory kernel.",
        H("Causal Recovery from Observed Response Operators"),
        Blocks(
            Paragraph(Text(
                "Use the existing block evolution (y,h) -> (Ay+Bh,Cy+Dh). At time n, "
                + "the response sends every visible initial vector v to the visible part "
                + "of the actual trajectory started at (v,0). Initial hidden data are "
                + "set to zero here and are not inferred from this experiment.")),
            Describe.Lean(
                DescribeId.Create("actual-block-memory-causal-reconstruction"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/ProbabilisticClosure/CausalMemoryRecovery.recover_actual_memory"),
                H("Triangular reconstruction equals B D^n C at every lag"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The recursive reconstruction at n subtracts R(1) composed with R(n+1) "
                        + "from R(n+2), then subtracts lower reconstructed kernels composed "
                        + "with R(i+1). Every recursive index is strictly below n. Strong "
                        + "induction identifies this result with B D^n C, using the exact "
                        + "hidden-elimination equation and the zero-time identity R(0)=id.")),
                    Paragraph(Text(
                        "Thus identical full response maps imply identical feedback kernels, "
                        + "and the nth kernel uses responses only through n+2. This is not "
                        + "scalar spectral recovery: composition order and the response on "
                        + "each visible vector are retained. It does not identify a unique "
                        + "hidden realization, a particular hidden initial state, or an "
                        + "unobserved stochastic path law. No additional generic observer "
                        + "factorization theorem is redeclared."))),
                DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(
            GidRef.Create("D5/S3/Observer/ProbabilisticClosure/DiscreteMemoryElimination"))]));
}
