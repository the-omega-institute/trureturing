using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Interpolation;

internal sealed class CullinanYoungKrawtchoukDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Interpolation/CullinanYoungKrawtchouk.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/RecurrenceComposition/cullinanyoung2026krawtchouk");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The even Krawtchouk sign interpolant has the leading coefficient stated by Cullinan and Young.",
        H("Cullinan--Young Krawtchouk Sign Interpolant"),
        Blocks(
            Paragraph(Text(
                "The source uses the nodes j minus N/2 and the Lagrange basis ell_i. "
                    + "The proposition spells out the interpolation sum and its basis products over rational nodes.")),
            Describe.Lean(
                DescribeId.Create("cullinanyoung-krawtchouk-ell"),
                DeclarationHandle.Create(Prefix + "ell"),
                H("Lagrange basis polynomial"),
                StatementSource.FromAuthor(Disp(new Formula.Bind(
                    FormulaQuantifier.ForAll,
                    FormulaIdentifier.Create("N"),
                    Naturals(),
                    new Formula.Bind(
                        FormulaQuantifier.ForAll,
                        FormulaIdentifier.Create("i"),
                        Naturals(),
                        Equal(Call("ell", F.Id("N"), F.Id("i")), EllBody(F.Id("N"), F.Id("i"))))))),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "For natural N and i, ell is the product of the centered linear factors at all nodes except i, with the corresponding rational denominator."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("cullinanyoung-krawtchouk-interpolant"),
                DeclarationHandle.Create(Prefix + "I"),
                H("Krawtchouk sign interpolant"),
                StatementSource.FromAuthor(Disp(new Formula.Bind(
                    FormulaQuantifier.ForAll,
                    FormulaIdentifier.Create("N"),
                    Naturals(),
                    Equal(Call("I", F.Id("N")), InterpolantBody(F.Id("N")))))),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "For natural N, I is the sum of the sign values at the centered nodes multiplied by the corresponding Lagrange basis polynomials."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("cullinanyoung-krawtchouk-claim"),
                DeclarationHandle.Create(Prefix + "claim"),
                H("Remark 8 leading coefficient formula"),
                StatementSource.FromAuthor(ClaimFormula()),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "Page 6, Remark 8 states: \"Numerical experimentation suggests that the leading coefficient of I_N(x) (and, therefore, F_N(x)) is given by (−1)^{(N−2)/2}/(N−1)! · C((N−2)/2), where C(n) is the nth Catalan number.\" The source takes N even. The Lean statement encodes the even case with N at least two; natural division is rendered by Nat.div and the coefficient is rational. Page 6 defines: \"Let I_N(x) be the Lagrange form of the interpolating polynomial of the points of P_N. Then I_N(x) = Σ_{i=0}^{N} sgn(i − N/2) ℓ_i(x), where ℓ_i(x) = Π_{j=0,j≠i}^{N} (x − (j − N/2))/(i − j).\" The interpolation sum and the basis products appear directly in the formula below."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("cullinanyoung-krawtchouk-result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("The proved leading coefficient formula"),
                StatementSource.FromAuthor(Disp(ClaimBody())),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "The proof uses Vieta's next-coefficient identity, reflection of the centered nodes, alternating partial binomial sums, and the Catalan central-binomial identity. The nonzero next coefficient also gives degree 2m plus 1 for N equal to 2(m plus 1).")),
                    Paragraph(Text(
                        "The statement covers every even N at least two. The source's identification of F_N with I_N is Proposition 6 and is not asserted here; odd N is outside the source observation."))),
                DescribeRole.Theorem))));

    private static Formula EllBody(Formula N, Formula i)
    {
        var j = F.Id("j");
        var range = Call(Qualified("Finset", "range"), Add(N, D(1)));
        var erased = Call(Qualified("Finset", "erase"), range, i);
        var difference = Sub(Cast(i, Rationals()), Cast(j, Rationals()));
        var node = Sub(Cast(j, Rationals()), Divide(Cast(N, Rationals()), D(2)));
        var factor = Multiply(
            Call(Qualified("Polynomial", "C"), Divide(D(1), difference)),
            Parenthesized(Sub(F.Id("X"), Call(Qualified("Polynomial", "C"), node))));
        var product = new Formula.Subscript(
            Prod, new Formula.Relation(j, FormulaRelationOperator.MemberOf, erased));
        return Seq(product, Sp, Parenthesized(factor));
    }

    private static Formula InterpolantBody(Formula N)
    {
        var i = F.Id("i");
        var range = Call(Qualified("Finset", "range"), Add(N, D(1)));
        var node = Sub(Cast(i, Rationals()), Divide(Cast(N, Rationals()), D(2)));
        var sign = Cast(Call(Qualified("SignType", "sign"), node), Rationals());
        var summand = Multiply(Call(Qualified("Polynomial", "C"), sign), Call("ell", N, i));
        var sum = new Formula.Subscript(
            Sum, new Formula.Relation(i, FormulaRelationOperator.MemberOf, range));
        return Seq(sum, Sp, Parenthesized(summand));
    }

    private static Formula ClaimFormula() => Disp(new Formula.Logic(
        F.Id("claim"), FormulaLogicOperator.Iff, Parenthesized(ClaimBody())));

    private static Formula ClaimBody()
    {
        var N = F.Id("N");
        var half = NatDiv(Sub(N, D(2)), D(2));
        var exponent = Parenthesized(half);
        var numerator = Multiply(
            new Formula.Power(Parenthesized(Neg(D(1))), exponent),
            Cast(Call("catalan", half), Rationals()));
        var denominator = Cast(Call(Qualified("Nat", "factorial"), Sub(N, D(1))), Rationals());
        var equality = Equal(
            Call(Qualified("Polynomial", "leadingCoeff"), Call("I", N)),
            Divide(numerator, denominator));
        var implications = Imp(
            Parenthesized(LessEqual(D(2), N)),
            Imp(Parenthesized(Call("Even", N)), equality));
        return new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("N"), Naturals(), implications);
    }

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Rationals() => Seq(Mathbb, Grp(F.Id("Q")));
    private static Formula Qualified(string owner, string name) =>
        Seq(Operatorname, Grp(F.Id(owner)), Dot, Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula Call(Formula function, params Formula[] args) =>
        new Formula.Apply(function, [.. args]);
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Sub(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Divide(Formula left, Formula right) =>
        new Formula.Fraction(left, right);
    private static Formula NatDiv(Formula left, Formula right) =>
        Call(Qualified("Nat", "div"), left, right);
    private static Formula Cast(Formula value, Formula type) =>
        Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula Neg(Formula value) => Seq(Minus, value);
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula LessEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Imp(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
}
