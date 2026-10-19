using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Matrix.LinPsiMap;

internal sealed class ResultDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Quantum/Matrix/LinPsiMap/Result.";
    private static LibraryNoteRef Source => LibraryNoteRef.Create("D5/L/Eigenstructure/lin2016psimap");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The map Psi gives both indexed spectral properties in every dimension.",
        H("Both spectral properties of the map Psi"), Blocks(
            Describe.Lean(DescribeId.Create("lin-psi-conjecture"),
                DeclarationHandle.Create(Owner + "conjecture"),
                H("The two-property proposition"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The proposition quantifies over every natural dimension n, all complex n by n matrices A, X and B, positivity of [A X; X-adjoint B], and every index j in Fin n. It is the conjunction of 2 s_j(Psi(X)) <= lambda_j(Psi(A)+Psi(B)) and s_j(Psi(X)) <= lambda_j(Psi(A) geometric-mean Psi(B)), where Psi(T)=2 trace(T) I−T. Both spectral lists decrease, using the same singular-value, eigenvalue and geometric-mean definitions as the trace-augmentation comparison."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("lin-psi-both-properties"),
                DeclarationHandle.Create(Owner + "result"),
                H("The a-property and g-property"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text("Both inequalities hold for every positive semidefinite complex block matrix. No commutation, invertibility or rank hypothesis is imposed on the original blocks. Dimension zero is vacuous; if either diagonal block is zero, positivity forces the cross block to vanish and the total geometric mean handles the degenerate case.")),
                    Paragraph(Text("For positive diagonal traces, a block congruence normalizes them separately. Reduction-block positivity and the Gram-discrepancy estimate provide the arithmetic deficit. The existing difference-square and geometric-mean lower bounds give the normalized geometric comparison. Independent positive homogeneity of the geometric mean restores the g-property for the original blocks, and the matrix arithmetic-geometric mean comparison gives the a-property."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("lin-2016-psi-map-properties"),
                    ResolutionKind.Proved)))));
}
