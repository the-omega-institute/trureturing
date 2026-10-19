using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Matrix.LinGProperty;

internal sealed class ResultDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Quantum/Matrix/LinGProperty/Result.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Trace augmentation gives the geometric-mean comparison in every dimension.",
        H("The geometric-mean comparison for trace augmentation"), Blocks(
            Describe.Lean(DescribeId.Create("lin-positive-parameter-family"),
                DeclarationHandle.Create(Owner + "parameter_family"),
                H("Every parameter at least one"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Eigenstructure/lin2016gproperty")),
                Blocks(Paragraph(Text("For every natural dimension n, every positive semidefinite complex block matrix with blocks A, X, X-adjoint and B, every real c at least one and every decreasing index j, the singular value s_j(X+c trace(X) I) is bounded by the corresponding eigenvalue of the geometric mean of A+c trace(A) I and B+c trace(B) I.")),
                    Paragraph(Text("The zero diagonal block case forces X to vanish. Otherwise both diagonal traces are positive. A block diagonal congruence normalizes them to one, the trace-overlap arithmetic and difference-square bounds give the normalized comparison, and the separate homogeneity of the geometric mean restores the original traces. The same actual block matrix supplies all estimates."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("lin-g-property"),
                DeclarationHandle.Create(Owner + "result"),
                H("The trace-augmentation conjecture"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Eigenstructure/lin2016gproperty")),
                Blocks(Paragraph(Text("The proposition conjecture quantifies over every n, all three complex n by n blocks A, X and B, positivity of their full block matrix and every j in Fin n. It states s_j(Phi(X)) at most lambda_j(Phi(A) geometric-mean Phi(B)), with Phi(T)=T+trace(T) I. Both spectral lists decrease. The geometric mean has its positive definite inverse-square-root formula on nonzero diagonal inputs and is zero when either diagonal input is zero. No commutation, invertibility or rank condition is imposed on the original blocks.")),
                    Paragraph(Text("Apply the parameter family at c=1. The intermediate trace-overlap bounds retain the common Gram realization of the two diagonal blocks and the cross block, while the harmonic comparison respects noncommutative multiplication order."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("lin-2016-trace-augmentation-g-property"),
                    ResolutionKind.Proved)))));
}
