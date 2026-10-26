using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Matrix.TaylorMajorization;

internal sealed class ResultDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Eigenstructure/zhang2026weakmajorizationtaylor");

    private const string Module = "D5/S3/Quantum/Matrix/TaylorMajorization/Result";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Refutation of unrestricted Hermitian Taylor majorization.",
        H("Refutation of unrestricted Hermitian Taylor majorization."), Blocks(
            Describe.Lean(DescribeId.Create("taylor-majorization-result-result"),
                DeclarationHandle.Create(Module + ".result"),
                H("The spectral comparison is false"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The claim for all Hermitian matrices and every order at least five is false. Use dimension two, A=Z-I, B=X and order five. Both matrices are Hermitian. Weak majorization would imply the real trace inequality by the full initial sum. The shifted Pauli family instead gives a strictly negative trace defect, contradicting that inequality. The example concerns Hermitian matrices without a positivity restriction."))), DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("zhang-2026-taylor-coefficient-weak-majorization"),
                    ResolutionKind.Refuted)))));

}
