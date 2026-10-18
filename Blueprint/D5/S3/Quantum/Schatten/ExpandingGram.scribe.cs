using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Schatten;

internal sealed class ExpandingGramDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Schatten/ExpandingGram";
    private static LibraryNoteRef Background => LibraryNoteRef.Create("D5/L/Eigenstructure/bhatia1997matrixanalysis");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Expanding square matrices and their singular values.",
        H("Expanding square matrices and their singular values"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("zhangli-expandinggram-expanding-isunit-det"),
                DeclarationHandle.Create(Module + ".expanding_isUnit_det"),
                H("Expansion implies invertibility"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Background),
                Blocks(Paragraph(Text("If a complex square matrix T satisfies T*T−I positive semidefinite, then det(T) is a unit. Its Gram matrix is positive definite, so T is invertible. The assertion includes the empty matrix."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("zhangli-expandinggram-expanding-adjoint"),
                DeclarationHandle.Create(Module + ".expanding_adjoint"),
                H("Expansion of the adjoint"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Background),
                Blocks(Paragraph(Text("If T*T−I is positive semidefinite for a complex square T, then TT*−I is positive semidefinite as well. Singular-value decomposition transfers the lower bound from one Gram matrix to the other."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("zhangli-expandinggram-expanding-right-singularvaluessorted"),
                DeclarationHandle.Create(Module + ".expanding_right_singularValuesSorted"),
                H("Right multiplication by an expanding matrix"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Background),
                Blocks(Paragraph(Text("For every complex square A and every T with T*T−I positive semidefinite, sᵢ(A)≤sᵢ(AT) for every decreasing singular-value index i. Positivity of A(TT*−I)A* and Gram-order monotonicity prove the comparison; A need not be invertible."))),
                DescribeRole.Theorem))));
}
