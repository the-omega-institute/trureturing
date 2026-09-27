using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Zigzag;

internal sealed class LaurentCoefficientsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Zigzag/LaurentCoefficients.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finite antidiagonal solution of the Laurent recurrence yields the exact central and shifted coefficients needed by the two parity boundaries.",
        H("Finite Laurent Coefficient Formula"),
        Blocks(
            Describe.Lean(DescribeId.Create("finite-antidiagonal-sum"),
                DeclarationHandle.Create(Prefix + "closedPolynomial"),
                H("A finite solution, not a formal infinite series"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "At depth m the sum ranges over pairs (a,b) with a+b=m. Each term has coefficient 2*choose(a,b)*2^(a-b)*3^b and Laurent exponent a-2b. The equivalent h-index presentation is 2*sum over h<=floor(m/2) of choose(m-h,h)*2^(m-2h)*3^h*z^(m-3h). All sums are finite; no analytic convergence is invoked."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("closed-solution-equals-transfer"),
                DeclarationHandle.Create(Prefix + "pathPolynomial_closed_formula"),
                H("The antidiagonal solves the path recurrence"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                    "A Pascal identity proves the finite antidiagonal sum satisfies the same second-order Laurent recurrence as pathPolynomial. Direct calculation gives common seeds 2 and 4z; two-step induction then proves equality at every natural depth. This supplies a closed expression rather than just numerical fitting."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("even-central-coefficient"),
                DeclarationHandle.Create(Prefix + "pathPolynomial_coeff_three_mul"),
                H("The even central coefficient"), StatementSource.FromAuthor(EvenCoefficient()),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                    "At depth 3s, exponent zero selects exactly the antidiagonal index (2s,s). Its coefficient is 2*6^s*choose(2s,s). The proof shows every other term has a different Laurent exponent, which is the exact even zero-charge count before adding the negative sector."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("odd-shifted-coefficient"),
                DeclarationHandle.Create(Prefix + "pathPolynomial_coeff_three_mul_add_two"),
                H("The odd shifted coefficient"), StatementSource.FromAuthor(OddCoefficient()),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                    "At depth 3s+2, the odd singleton shift asks for exponent -1. Only the index (2s+1,s+1) contributes, giving 6^(s+1)*choose(2s+1,s+1). Both coefficient identities hold for every s and feed the literal balanced-count endpoint through the path equivalences."))),
                DescribeRole.Theorem)), []));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Mul(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Universal(Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create("s"),
            new Formula.NamedConstant(FormulaIdentifier.Create("Nat")), body);
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula PolyCoeff(Formula depth, Formula exponent) =>
        Call("coeff", Call("pathPolynomial", depth), exponent);
    private static Formula Pow(Formula baseValue, Formula exponent) =>
        new Formula.Power(baseValue, exponent);
    private static Formula Choose(Formula n, Formula k) => Call("choose", n, k);

    private static Formula EvenCoefficient()
    {
        var s = F.Id("s");
        var twice = Mul(D(2), s);
        return Disp(Universal(Equal(PolyCoeff(Mul(D(3), s), D(0)),
            Mul(Mul(D(2), Pow(D(6), s)), Choose(twice, s)))));
    }

    private static Formula OddCoefficient()
    {
        var s = F.Id("s");
        var next = Add(s, D(1));
        return Disp(Universal(Equal(
            PolyCoeff(Add(Mul(D(3), s), D(2)), new Formula.Negate(D(1))),
            Mul(Pow(D(6), next), Choose(Add(Mul(D(2), s), D(1)), next)))));
    }
}
