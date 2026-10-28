using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Subentropy;

internal sealed class GaussianDiagonalDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A fixed coordinate entropy expectation is the common baseline for diagonal subentropy.",
        H("The diagonal Gaussian entropy expectation"), Blocks(
            Paragraph(Text("For a finite probability vector p, use independent standard real Gaussian coordinates z_(i,0), z_(i,1), put X_i=(z_(i,0)^2+z_(i,1)^2)/2 and a=Σ_i p_i X_i. Write η(u)=−u log u. Choose any coordinate i₀; the theorem does not require positive weights.")),
            Describe.Lean(DescribeId.Create("subentropy-diagonal-gaussian-entropy"),
                DeclarationHandle.Create("D5/S3/Quantum/Subentropy/GaussianDiagonal.diagonal_subentropy_gaussian_entropy"),
                H("A common fixed-dimension entropy baseline"),
                StatementSource.FromAuthor(Disp(Statement())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Swapping two coordinate pairs preserves the product Gaussian measure, so all expectations Eη(X_i) are equal. A fourth-moment Gaussian bound supplies absolute integrability of each coordinate entropy. The Gaussian entropy-gap representation and the integrable finite baseline then imply integrability of η(a). Integrating the difference and using Σ_i p_i=1 gives Q(diag p)=Eη(a)−Eη(X_(i₀)). The baseline is constant within each fixed dimension, which suffices for cancellation in fixed-dimension concavity and pinching comparisons."))),
                DescribeRole.Theorem))));
    private static Formula Statement()
    {
        Formula value = new Formula.Binary(Call("E", Call("eta", F.Id("a"))),
            FormulaBinaryOperator.Subtract, Call("E", Call("eta", Call("X", F.Id("i0")))));
        Formula identity = new Formula.Relation(Call("Q", Call("diag", F.Id("p"))),
            FormulaRelationOperator.Equal, value);
        return new Formula.Logic(Call("Integrable", Call("eta", F.Id("a")), F.Id("gamma")),
            FormulaLogicOperator.And, identity);
    }
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
}
