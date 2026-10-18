using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Subentropy;

internal sealed class GaussianMatrixDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Subentropy is an entropy expectation on the standard Gaussian measure of a common Euclidean space.",
        H("The matrix Gaussian entropy expectation"), Blocks(
            Paragraph(Text("Let A be a finite positive semidefinite complex matrix of trace one. Put a_A(z)=Re⟨z,Az⟩/2 and η(u)=−u log u. The standard Gaussian is the real standard Gaussian on the underlying complex Euclidean space. Choose any index i₀ and let κ be the entropy expectation of the corresponding squared pair of independent standard real Gaussian coordinates.")),
            Describe.Lean(DescribeId.Create("subentropy-matrix-gaussian-entropy"),
                DeclarationHandle.Create("D5/S3/Quantum/Subentropy/GaussianMatrix.matrix_subentropy_gaussian_entropy"),
                H("A common-coordinate matrix entropy representation"),
                StatementSource.FromAuthor(Disp(Statement())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The eigenvalues of A form a probability vector. The existing diagonal entropy representation makes the weighted quadratic entropy integrable. Pairing independent real coordinates realizes the standard Gaussian on the complex Euclidean space, and the eigenvector unitary preserves that Gaussian. Spectral transport identifies the diagonal weighted quadratic form with a_A in these coordinates. Consequently η(a_A) is integrable. The existing isometric-embedding invariance identifies the determinant-integral subentropy with the diagonal one, so Q(A)=Eη(a_A)−κ. Zero and repeated eigenvalues are included. The constant κ is fixed within each matrix dimension and cancels in comparisons on that space."))),
                DescribeRole.Theorem))));
    private static Formula Statement()
    {
        Formula quadratic = Call("a", F.Id("A"));
        Formula value = new Formula.Binary(Call("E", Call("eta", quadratic)),
            FormulaBinaryOperator.Subtract, Call("E", Call("eta", Call("X", F.Id("i0")))));
        Formula identity = new Formula.Relation(Call("Q", F.Id("A")),
            FormulaRelationOperator.Equal, value);
        return new Formula.Logic(Call("Integrable", Call("eta", quadratic), F.Id("gamma")),
            FormulaLogicOperator.And, identity);
    }
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
}
