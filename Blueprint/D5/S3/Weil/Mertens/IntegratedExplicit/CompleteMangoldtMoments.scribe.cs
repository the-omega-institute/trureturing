using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Mertens.IntegratedExplicit;

internal sealed class CompleteMangoldtMomentsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The signed logarithmic moments of the complete Mangoldt remainder",
        H("Differentiating throughout the initial half-plane"),
        Blocks(Describe.Lean(
            DescribeId.Create("signed-logarithmic-moments"),
            DeclarationHandle.Create(
                "D5/S3/Weil/Mertens/IntegratedExplicit/CompleteMangoldtMoments.iterated_derivative_moment"),
            H("All derivatives of the complete transform"),
            StatementSource.FromAuthor(Claim()), AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("Let Φ be the explicit transform of the complete Mangoldt remainder U. "
                    + "One derivative of exp(−su) contributes −u. Iterating gives the signed powers in the formula.")),
                Paragraph(Text("Fix s with Re(s)>1 and put d=(Re(s)−1)/3 and a=1+d. "
                    + "On a neighborhood of s, the damping beyond a is at least d. "
                    + "The exponential series gives uᵏ≤k! exp(du)/dᵏ for u≥0. "
                    + "The absolute zeroth moment on the line a thus dominates the moment of each "
                    + "fixed order throughout this neighborhood, including the next order used for differentiation. "
                    + "Differentiation under the integral and induction identify the derivatives."))),
            DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);

    private static Formula Claim()
    {
        var k = F.Id("k");
        var s = F.Id("s");
        var u = F.Id("u");
        var weight = F.Seq(F.Open, new Formula.Negate(u), F.Close, F.Caret, F.Grp(k));
        var integrand = Multiply(weight,
            Multiply(Call("exp", new Formula.Negate(Multiply(s, u))), Call("U", Call("exp", u))));
        var fn = F.Seq(F.Open, F.LambdaLower, F.Sp, u, F.Sp, F.Mapsto, F.Sp, integrand, F.Close);
        var integral = F.Seq(F.Int, F.Underscore, F.Grp(F.D(0)), F.Caret, F.Grp(F.Infty),
            F.Sp, integrand, F.Sp, F.Id("d"), u);
        var identity = new Formula.Relation(Call("iteratedDeriv", k, F.Id("transform"), s),
            FormulaRelationOperator.Equal, integral);
        var claim = new Formula.Logic(Call("IntegrableOn", fn, Call("Ioi", F.D(0))),
            FormulaLogicOperator.And, identity);
        var hs = new Formula.Relation(F.D(1), FormulaRelationOperator.LessThan, Call("Re", s));
        var conditional = new Formula.Logic(hs, FormulaLogicOperator.Implies, claim);
        var complex = new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create("s"),
            F.Seq(F.Mathbb, F.Grp(F.Id("C"))), conditional);
        return F.Disp(new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create("k"),
            F.Seq(F.Mathbb, F.Grp(F.Id("N"))), complex));
    }
}
