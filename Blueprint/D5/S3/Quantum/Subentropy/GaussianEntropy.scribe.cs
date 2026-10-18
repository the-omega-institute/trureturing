using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Subentropy;

internal sealed class GaussianEntropyDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Diagonal determinant-integral subentropy equals an integrable Gaussian entropy Jensen gap.",
        H("Gaussian entropy-gap representation"), Blocks(
            Paragraph(Text("Let p be a probability vector on a finite type I. Under the product of independent standard real Gaussian laws indexed by I×{0,1}, put X_i(z)=(z_(i,0)^2+z_(i,1)^2)/2 and a(z)=Σ_i p_i X_i(z). Write η(u)=−u log u, with η(0)=0. The entire gap η(a)−Σ_i p_i η(X_i) is integrable.")),
            Describe.Lean(DescribeId.Create("subentropy-diagonal-gaussian-entropy-gap"),
                DeclarationHandle.Create("D5/S3/Quantum/Subentropy/GaussianEntropy.diagonal_subentropy_gaussian_gap"),
                H("The exact diagonal Gaussian representation"),
                StatementSource.FromAuthor(Disp(Statement())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The scalar Laplace-Jensen identity represents the gap by the nonnegative kernel [Σ_i p_i exp(−sX_i)−exp(−sa)]/s². Each exponential is bounded by one and is integrable. The Gaussian coordinate Laplace transform gives its expected value [(1+s)^(−1)−∏_i(1+s p_i)^(−1)]/s². The reciprocal substitution t=1/s identifies this scalar integral with the existing determinant-integral definition and supplies integrability. Product integrability and Fubini then identify the Gaussian expected gap. This argument permits zero weights and needs neither entropy moments as an assumption nor an exchange of separately divergent integrals. The theorem concerns diagonal matrices; the common-coordinate matrix representation and pinching inequalities require additional unitary transport."))),
                DescribeRole.Theorem))));
    private static Formula Statement()
    {
        Formula i = F.Id("i"), x = Call("X", i), a = F.Id("a"), p = Call("p", i);
        Formula gap = new Formula.Binary(Call("eta", a), FormulaBinaryOperator.Subtract,
            Call("sum", new Formula.Binary(p, FormulaBinaryOperator.Multiply, Call("eta", x))));
        return new Formula.Logic(Call("Integrable", gap, F.Id("gamma")), FormulaLogicOperator.And,
            new Formula.Relation(Call("Q", Call("diag", F.Id("p"))), FormulaRelationOperator.Equal, Call("E", gap)));
    }
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
}
