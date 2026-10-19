using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Subentropy;

internal sealed class GaussianRepresentationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The exact diagonal Gaussian quadratic-form Laplace transform.",
        H("Diagonal Gaussian Laplace transform"), Blocks(
            Paragraph(Text("Let I be finite, p_i≥0 and s≥0. The coordinates z_(i,0), z_(i,1) are independent real Gaussian random variables of mean zero and variance one, so each pair represents one standard complex Gaussian coordinate. No normalization of p is required.")),
            Describe.Lean(DescribeId.Create("subentropy-diagonal-gaussian-laplace"),
                DeclarationHandle.Create("D5/S3/Quantum/Subentropy/GaussianRepresentation.diagonal_gaussian_laplace"),
                H("Independent complex-coordinate Laplace transform"),
                StatementSource.FromAuthor(Disp(Statement())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The quadratic form in the exponential is −Σ_(i,k) s p_i z_(i,k)^2/2. For one real coordinate with coefficient c≥0, rewrite the Gaussian expectation using gaussianPDFReal and combine the exponentials. Mathlib integral_gaussian evaluates the resulting integral. Squaring the answer gives 1/(1+c). Finite product integration pairs the two equal factors for every i, yielding ∏_i(1+s p_i)^(−1). This is the diagonal Laplace transform only. Identification of the entropy expectation with the determinant-integral subentropy remains a separate mathematical obligation."))),
                DescribeRole.Theorem))));
    private static Formula Statement()
    {
        Formula s = F.Id("s"), pj = Call("p", Call("fst", F.Id("j"))), zj = Call("z", F.Id("j"));
        Formula exponent = Call("sum", new Formula.Fraction(
            Mul(Sub(D(0), Mul(s, pj)), new Formula.Power(zj, D(2))), D(2)));
        Formula value = Call("prod", new Formula.Fraction(D(1),
            Add(D(1), Mul(s, Call("p", F.Id("i"))))));
        return new Formula.Relation(Call("E", Call("exp", exponent)), FormulaRelationOperator.Equal, value);
    }
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
}
