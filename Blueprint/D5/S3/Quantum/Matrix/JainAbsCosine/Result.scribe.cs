using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Matrix.JainAbsCosine;

internal sealed class ResultDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exactly double nonzero eigenvalues for the odd absolute cosine power matrix.",
        H("Multiplicity from Fourier mode separation"), Blocks(
            Describe.Lean(DescribeId.Create("jain-absolute-cosine-multiplicity-result"),
                DeclarationHandle.Create("D5/S3/Quantum/Matrix/JainAbsCosine/Result.result"),
                H("The nonzero multiplicity conjecture"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Eigenstructure/jain2017hadamard")),
                Blocks(Paragraph(Text(
                    "For every odd order 2m+1 with m at least one and every nonnegative real exponent, every nonzero characteristic root other than the largest Fourier mode has algebraic multiplicity exactly two. The matrix and the claim are those of Jain. Periodicity of the absolute cosine identifies the matrix as a real circulant. Reflection pairs its Fourier factors into one linear factor for the constant mode and squared linear factors for the remaining modes. The exact gap signs separate all nonzero representative values. Removing the unique squared factor leaves a polynomial that does not vanish at the chosen root, so the root multiplicity is exactly two."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("jain-2017-abs-cosine-hadamard-power-multiplicity-two"),
                    ResolutionKind.Proved)))));
}
