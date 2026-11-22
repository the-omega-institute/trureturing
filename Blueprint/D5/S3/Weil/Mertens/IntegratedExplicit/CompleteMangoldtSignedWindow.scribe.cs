using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Mertens.IntegratedExplicit;

internal sealed class CompleteMangoldtSignedWindowDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Signed Mangoldt moments on a logarithmic window",
        H("Comparing derivatives at equal real parts"),
        Blocks(Describe.Lean(
            DescribeId.Create("signed-window-moment-bound"),
            DeclarationHandle.Create("D5/S3/Weil/Mertens/IntegratedExplicit/"
                + "CompleteMangoldtSignedWindow.signed_window_moment_bound"),
            H("A bound from either sign on the window"),
            StatementSource.FromAuthor(F.Disp(Claim())), AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("Write D(k,s)=(−1)ᵏΦ₊⁽ᵏ⁾(s)/k! for the normalized derivative of the "
                    + "completed Mangoldt transform, g(u)=U(exp(u)) for the complete remainder, "
                    + "and K(k,σ,u)=uᵏ exp(−σu)/k! for the real moment weight.")),
                Paragraph(Text("The moment at p has modulus at most the integral of |g| against K, "
                    + "where σ is the real part of p. The moment at the real point σ is the signed "
                    + "integral of g against the same weight. For e equal to 1 or −1, their sum "
                    + "with the real term multiplied by e is at most the integral of 2 max(eg,0) against K.")),
                Paragraph(Text("On the prescribed window, the exponential series bounds K by "
                    + "(σ−q)⁻ᵏ exp(−qu). On the complement use max(eg,0)≤|g|. "
                    + "These estimates split the contribution to the same pair of derivatives "
                    + "into a window integral and an absolute tail."))),
            DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);

    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);

    private static Formula Relation(Formula left, FormulaRelationOperator op, Formula right) =>
        new Formula.Relation(left, op, right);

    private static Formula Integral(Formula domain, Formula integrand, Formula variable) =>
        F.Seq(F.Int, F.Underscore, F.Grp(domain), F.Sp, integrand, F.Sp, F.Id("d"), variable);

    private static Formula Claim()
    {
        var k = F.Id("k");
        var p = F.Id("p");
        var a = F.Id("a");
        var b = F.Id("b");
        var e = F.Id("e");
        var u = F.Id("u");
        var q = F.Id("q");
        var real = F.Seq(F.Mathbb, F.Grp(F.Id("R")));
        var complex = F.Seq(F.Mathbb, F.Grp(F.Id("C")));
        var natural = F.Seq(F.Mathbb, F.Grp(F.Id("N")));
        var sigma = Call("Re", p);
        var window = F.Seq(F.OpenBracket, a, F.Comma, b, F.CloseBracket);
        var tails = F.Seq(F.Open, F.D(0), F.Comma, F.Infty, F.Close,
            F.Sp, F.Setminus, F.Sp, window);
        var g = Call("g", u);
        var positivePart = Call("max", Multiply(e, g), F.D(0));
        var inner = Integral(window,
            Multiply(positivePart, Call("exp", new Formula.Negate(Multiply(q, u)))), u);
        var outer = Integral(tails, Multiply(new Formula.Absolute(g), Call("K", k, sigma, u)), u);
        var inversePower = new Formula.Power(F.Seq(F.Open, Subtract(sigma, q), F.Close),
            new Formula.Negate(k));
        var left = Add(new Formula.Absolute(Call("D", k, p)),
            Multiply(e, Call("Re", Call("D", k, sigma))));
        var right = Add(Multiply(Multiply(F.D(2), inversePower), inner), Multiply(F.D(2), outer));
        var sign = new Formula.Logic(
            Relation(e, FormulaRelationOperator.Equal, F.D(1)), FormulaLogicOperator.Or,
            Relation(e, FormulaRelationOperator.Equal, new Formula.Negate(F.D(1))));
        Formula[] assumptions =
        [
            Relation(F.D(1), FormulaRelationOperator.LessThan, sigma),
            Relation(F.D(0), FormulaRelationOperator.LessThan, a),
            Relation(a, FormulaRelationOperator.LessThanOrEqual, b),
            Relation(q, FormulaRelationOperator.LessThan, sigma),
            sign
        ];
        Formula claim = Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
        foreach (var assumption in assumptions.Reverse())
        {
            claim = new Formula.Logic(assumption, FormulaLogicOperator.Implies, claim);
        }

        return All("k", natural, All("p", complex,
            All("a", real, All("b", real, All("q", real, All("e", real, claim))))));
    }
}
