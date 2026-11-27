using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.General.LinearAlgebra;

internal sealed class ExpSurjectiveDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exp Surjective", H("Exp Surjective"),
        Blocks(
            Paragraph(Text("Products of principal minors of weight w: transpose, inverse, triangular laws, analyticity. Fischer's inequality for principal minors of positive semidefinite matrices. Maximal compact subgroup, its complexification, block diagonal part, Haar probability on K. Polar decomposition in U(p,q); basic properties of accretive matrices. Exponential is onto K; every element of U(p,q) is a product of two exponentials.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/General/LinearAlgebra/ExpSurjective.exists_polar"),
                H("exists_polar"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Polar decomposition: every g in U(diag ε) is kz with k in K = U(diag ε)∩U(n) and z in U(diag ε) positive definite and the exponential of an element of the Lie algebra.")))))));
}
