using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Periodic;

internal sealed class BalaA281181TotientSquarePeriodDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Periodic/BalaA281181TotientSquarePeriod.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/ArithUnits/bala2026totientsquareperiod");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Totient-square periods of integral derivation coefficients.",
        H("Bala A281181 Totient-Square Period"),
        Blocks(
            Node("BalaPolynomialSystem.c", "c", Formula0(),
                "The first coordinate is indexed by false.", DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("BalaPolynomialSystem.s", "s", Formula1(),
                "The second coordinate is indexed by true.", DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("BalaPolynomialSystem.deriv", "deriv", Formula2(),
                "The two polynomial coordinate derivatives are c to the power q times s, and c to the power q plus one.", DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("BalaPolynomialSystem.initial", "initial", Formula3(),
                "The initial evaluation sends c to one and s to zero.", DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("BalaPolynomialSystem.C", "C", Formula4(),
                "The first coordinate flow has initial value one.", DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("BalaPolynomialSystem.S", "S", Formula5(),
                "The second coordinate flow has initial value zero.", DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("BalaPolynomialSystem.constant_S", "constant S", Formula6(),
                "The second flow starts at zero.", DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("BalaPolynomialSystem.A281180_ode", "A281180 ode", Formula7(),
                "At q equal to three, the invariant reduces the second coordinate equation to the quartic scalar equation.", DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("BalaPolynomialSystem.H", "H", Formula8(),
                "Integrate C to the power q with constant coefficient zero.", DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("BalaPolynomialSystem.constant_H", "constant H", Formula9(),
                "The primitive has constant coefficient zero.", DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("BalaPolynomialSystem.derivative_H", "derivative H", Formula10(),
                "Differentiating the primitive recovers C to the power q.", DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("BalaPolynomialSystem.cosh_identity", "cosh identity", Formula11(),
                "The sum and difference of the coordinate flows solve scalar linear differential equations, giving the two exponentials.", DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("BalaPolynomialSystem.log_derivative", "log derivative", Formula12(),
                "The logarithmic derivative of C plus S is C to the power q.", DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("BalaPolynomialSystem.evenSequence", "evenSequence", Formula13(),
                "The even derivative values of a coordinate power form an integer sequence.", DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("BalaPolynomialSystem.even_sequence_coefficient", "even sequence coefficient", Formula14(),
                "These integer values are exactly the even exponential coefficients.", DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("BalaPolynomialSystem.even_sequence_period", "even sequence period", Formula15(),
                "Odd-prime square-root coordinates and a separate second-order argument at two establish every positive modulus for q equal to three or seven.", DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("claim", "claim", Formula16(),
                "E.g.f. C(x) satisfies C(x) = cosh( Integral C(x)^3 dx ). More generally, we conjecture that the sequence {a(n)} reduced modulo a positive integer k is eventually periodic with the period dividing phi(k)^2, where phi(n) = A000010(n). An example is given below. - _Peter Bala_, Feb 16 2026 The source is unpaginated. The primitive has constant coefficient zero, eCoeff is factorial times the ordinary coefficient, and all sequences take integer values. Natural subtraction is truncated subtraction.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "result", Formula17(),
                "The integral derivation flow supplies the series and its integer exponential coefficients. Prime-power operator annihilators give the prescribed shift, and divisibility assembles all positive moduli.", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)))));

    private static DocumentBlock Node(string name, string title, Formula formula,
        string prose, DescribeRole role, AssessedProvenance provenance) => Describe.Lean(
        DescribeId.Create("balaa281181totientsquareperiod-" + name.Replace("C", "uppercase-c").Replace("S", "uppercase-s").Replace('.', '-').Replace('_', '-').ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name[(name.LastIndexOf('.') + 1)..]), H(title), StatementSource.FromAuthor(formula),
        provenance, Blocks(Paragraph(Text(prose))), role,
        null);

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Qualified(params string[] parts)
    {
        var items = new System.Collections.Generic.List<Formula>();
        foreach (var part in parts)
        {
            if (items.Count != 0) items.Add(Dot);
            items.Add(Operatorname);
            items.Add(Grp(F.Id(part)));
        }
        return Seq(items.ToArray());
    }
    private static Formula Formula0() => Disp(Seq(Qualified("BalaPolynomialSystem","c"), Sp, Eq, Sp, Parenthesized(Seq(Qualified("MvPolynomial","X"), Sp, F.Id("false"), Sp, Colon, Sp, F.Id("MvPolynomial"), Sp, F.Id("Bool"), Sp, Seq(Mathbb, Grp(F.Id("Z")))))));

    private static Formula Formula1() => Disp(Seq(Qualified("BalaPolynomialSystem","s"), Sp, Eq, Sp, Parenthesized(Seq(Qualified("MvPolynomial","X"), Sp, F.Id("true"), Sp, Colon, Sp, F.Id("MvPolynomial"), Sp, F.Id("Bool"), Sp, Seq(Mathbb, Grp(F.Id("Z")))))));

    private static Formula Formula2() => Disp(Seq(Forall, Sp, Parenthesized(Seq(F.Id("q"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp, Comma, Sp, Qualified("BalaPolynomialSystem","deriv"), Sp, F.Id("q"), Sp, Eq, Sp, Qualified("MvPolynomial","mkDerivation"), Sp, Seq(Mathbb, Grp(F.Id("Z"))), Sp, Parenthesized(Seq(F.Id("fun"), Sp, F.Id("b"), Sp, Colon, Sp, F.Id("Bool"), Sp, Mapsto, Sp, F.Id("if"), Sp, F.Id("b"), Sp, F.Id("then"), Sp, new Formula.Power(Parenthesized(Seq(Qualified("BalaPolynomialSystem","c"))),Seq(F.Id("q"), Sp, Plus, Sp, D(1))), Sp, F.Id("else"), Sp, new Formula.Power(Parenthesized(Seq(Qualified("BalaPolynomialSystem","c"))),F.Id("q")), Sp, Cdot, Sp, Qualified("BalaPolynomialSystem","s")))));

    private static Formula Formula3() => Disp(Seq(Qualified("BalaPolynomialSystem","initial"), Sp, Eq, Sp, Qualified("MvPolynomial","eval"), Sp, Parenthesized(Seq(F.Id("fun"), Sp, F.Id("b"), Sp, Colon, Sp, F.Id("Bool"), Sp, Mapsto, Sp, F.Id("if"), Sp, F.Id("b"), Sp, F.Id("then"), Sp, Parenthesized(Seq(D(0), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("Z"))))), Sp, F.Id("else"), Sp, D(1)))));

    private static Formula Formula4() => Disp(Seq(Forall, Sp, Parenthesized(Seq(F.Id("q"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp, Comma, Sp, Qualified("BalaPolynomialSystem","C"), Sp, F.Id("q"), Sp, Eq, Sp, Qualified("BalaFlow","flow"), Sp, Parenthesized(Seq(Qualified("BalaPolynomialSystem","deriv"), Sp, F.Id("q"))), Sp, Qualified("BalaPolynomialSystem","initial"), Sp, Qualified("BalaPolynomialSystem","c")));

    private static Formula Formula5() => Disp(Seq(Forall, Sp, Parenthesized(Seq(F.Id("q"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp, Comma, Sp, Qualified("BalaPolynomialSystem","S"), Sp, F.Id("q"), Sp, Eq, Sp, Qualified("BalaFlow","flow"), Sp, Parenthesized(Seq(Qualified("BalaPolynomialSystem","deriv"), Sp, F.Id("q"))), Sp, Qualified("BalaPolynomialSystem","initial"), Sp, Qualified("BalaPolynomialSystem","s")));

    private static Formula Formula6() => Disp(Seq(Forall, Sp, Parenthesized(Seq(F.Id("q"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp, Comma, Sp, Qualified("PowerSeries","constantCoeff"), Sp, Parenthesized(Seq(Qualified("BalaPolynomialSystem","S"), Sp, F.Id("q"))), Sp, Eq, Sp, D(0)));

    private static Formula Formula7() => Disp(Seq(Qualified("PowerSeries","derivative"), Sp, Parenthesized(Seq(Qualified("BalaPolynomialSystem","S"), Sp, D(3))), Sp, Eq, Sp, new Formula.Power(Parenthesized(Seq(D(1), Sp, Plus, Sp, new Formula.Power(Parenthesized(Seq(Qualified("BalaPolynomialSystem","S"), Sp, D(3))),D(2)))),D(2))));

    private static Formula Formula8() => Disp(Seq(Forall, Sp, Parenthesized(Seq(F.Id("q"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp, Comma, Sp, Qualified("BalaPolynomialSystem","H"), Sp, F.Id("q"), Sp, Eq, Sp, Qualified("D5","S1","Recurrence","Algebraic","SchroderIntegralEGF","primitive"), Sp, Parenthesized(Seq(new Formula.Power(Parenthesized(Seq(Qualified("BalaPolynomialSystem","C"), Sp, F.Id("q"))),F.Id("q"))))));

    private static Formula Formula9() => Disp(Seq(Forall, Sp, Parenthesized(Seq(F.Id("q"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp, Comma, Sp, Qualified("PowerSeries","constantCoeff"), Sp, Parenthesized(Seq(Qualified("BalaPolynomialSystem","H"), Sp, F.Id("q"))), Sp, Eq, Sp, D(0)));

    private static Formula Formula10() => Disp(Seq(Forall, Sp, Parenthesized(Seq(F.Id("q"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp, Comma, Sp, Qualified("PowerSeries","derivative"), Sp, Parenthesized(Seq(Qualified("BalaPolynomialSystem","H"), Sp, F.Id("q"))), Sp, Eq, Sp, new Formula.Power(Parenthesized(Seq(Qualified("BalaPolynomialSystem","C"), Sp, F.Id("q"))),F.Id("q"))));

    private static Formula Formula11() => Disp(Seq(Forall, Sp, Parenthesized(Seq(F.Id("q"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp, Comma, Sp, Qualified("BalaPolynomialSystem","C"), Sp, F.Id("q"), Sp, Eq, Sp, Qualified("PowerSeries","C"), Sp, Parenthesized(Seq(D(1), Sp, Slash, Sp, D(2), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("Q"))))), Sp, Cdot, Sp, Parenthesized(Seq(Parenthesized(Seq(Qualified("PowerSeries","subst"), Sp, Parenthesized(Seq(Qualified("BalaPolynomialSystem","H"), Sp, F.Id("q"))), Sp, Parenthesized(Seq(Qualified("PowerSeries","exp"), Sp, Seq(Mathbb, Grp(F.Id("Q"))))))), Sp, Plus, Sp, Parenthesized(Seq(Qualified("PowerSeries","subst"), Sp, Parenthesized(Seq(Minus, Sp, Parenthesized(Seq(Qualified("BalaPolynomialSystem","H"), Sp, F.Id("q"))))), Sp, Parenthesized(Seq(Qualified("PowerSeries","exp"), Sp, Seq(Mathbb, Grp(F.Id("Q")))))))))));

    private static Formula Formula12() => Disp(Seq(Forall, Sp, Parenthesized(Seq(F.Id("q"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp, Comma, Sp, Qualified("PowerSeries","derivative"), Sp, Parenthesized(Seq(Qualified("PowerSeries","logOf"), Sp, Parenthesized(Seq(Qualified("BalaPolynomialSystem","C"), Sp, F.Id("q"), Sp, Plus, Sp, Qualified("BalaPolynomialSystem","S"), Sp, F.Id("q"))))), Sp, Eq, Sp, new Formula.Power(Parenthesized(Seq(Qualified("BalaPolynomialSystem","C"), Sp, F.Id("q"))),F.Id("q"))));

    private static Formula Formula13() => Disp(Seq(Forall, Sp, Parenthesized(Seq(F.Id("q"), Sp, F.Id("e"), Sp, F.Id("n"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp, Comma, Sp, Qualified("BalaPolynomialSystem","evenSequence"), Sp, F.Id("q"), Sp, F.Id("e"), Sp, F.Id("n"), Sp, Eq, Sp, Qualified("BalaPolynomialSystem","initial"), Sp, Parenthesized(Seq(Qualified("Nat","iterate"), Sp, Parenthesized(Seq(Qualified("BalaPolynomialSystem","deriv"), Sp, F.Id("q"))), Sp, Parenthesized(Seq(D(2), Sp, Cdot, Sp, F.Id("n"))), Sp, Parenthesized(Seq(new Formula.Power(Parenthesized(Seq(Qualified("BalaPolynomialSystem","c"))),F.Id("e"))))))));

    private static Formula Formula14() => Disp(Seq(Forall, Sp, Parenthesized(Seq(F.Id("q"), Sp, F.Id("e"), Sp, F.Id("n"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp, Comma, Sp, Parenthesized(Seq(Qualified("BalaPolynomialSystem","evenSequence"), Sp, F.Id("q"), Sp, F.Id("e"), Sp, F.Id("n"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("Q"))))), Sp, Eq, Sp, F.Id("eCoeff"), Sp, Parenthesized(Seq(new Formula.Power(Parenthesized(Seq(Qualified("BalaPolynomialSystem","C"), Sp, F.Id("q"))),F.Id("e")))), Sp, Parenthesized(Seq(D(2), Sp, Cdot, Sp, F.Id("n")))));

    private static Formula Formula15() => Disp(Seq(Forall, Sp, Parenthesized(Seq(F.Id("q"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp, Comma, Sp, Parenthesized(Seq(F.Id("q"), Sp, Eq, Sp, D(3), Sp, Lor, Sp, F.Id("q"), Sp, Eq, Sp, D(7))), Sp, Implies, Sp, Forall, Sp, Parenthesized(Seq(F.Id("e"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp, Comma, Sp, Forall, Sp, Parenthesized(Seq(F.Id("k"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp, Comma, Sp, D(1), Sp, Le, Sp, F.Id("k"), Sp, Implies, Sp, Exists, Sp, Parenthesized(Seq(F.Id("N"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp, Comma, Sp, D(1), Sp, Le, Sp, F.Id("N"), Sp, Land, Sp, Parenthesized(Seq(Forall, Sp, Parenthesized(Seq(F.Id("n"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp, Comma, Sp, F.Id("N"), Sp, Le, Sp, F.Id("n"), Sp, Implies, Sp, Qualified("Int","ModEq"), Sp, Parenthesized(Seq(F.Id("k"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("Z"))))), Sp, Parenthesized(Seq(Qualified("BalaPolynomialSystem","evenSequence"), Sp, F.Id("q"), Sp, F.Id("e"), Sp, Parenthesized(Seq(F.Id("n"), Sp, Plus, Sp, new Formula.Power(Parenthesized(Seq(Qualified("Nat","totient"), Sp, F.Id("k"))),D(2)))))), Sp, Parenthesized(Seq(Qualified("BalaPolynomialSystem","evenSequence"), Sp, F.Id("q"), Sp, F.Id("e"), Sp, F.Id("n")))))));

    private static Formula Formula16() => Disp(Seq(F.Id("claim"), Sp, Eq, Sp, Parenthesized(Seq(Exists, Sp, Parenthesized(Seq(F.Id("H"), Sp, F.Id("C"), Sp, Colon, Sp, F.Id("PowerSeries"), Sp, Seq(Mathbb, Grp(F.Id("Q"))))), Sp, Comma, Sp, Qualified("PowerSeries","constantCoeff"), Sp, F.Id("H"), Sp, Eq, Sp, D(0), Sp, Land, Sp, Qualified("PowerSeries","derivative"), Sp, F.Id("H"), Sp, Eq, Sp, new Formula.Power(F.Id("C"),D(3)), Sp, Land, Sp, F.Id("C"), Sp, Eq, Sp, Qualified("PowerSeries","C"), Sp, Parenthesized(Seq(D(1), Sp, Slash, Sp, D(2), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("Q"))))), Sp, Cdot, Sp, Parenthesized(Seq(Qualified("PowerSeries","subst"), Sp, F.Id("H"), Sp, Parenthesized(Seq(Qualified("PowerSeries","exp"), Sp, Seq(Mathbb, Grp(F.Id("Q"))))), Sp, Plus, Sp, Qualified("PowerSeries","subst"), Sp, Parenthesized(Seq(Minus, Sp, F.Id("H"))), Sp, Parenthesized(Seq(Qualified("PowerSeries","exp"), Sp, Seq(Mathbb, Grp(F.Id("Q"))))))), Sp, Land, Sp, Parenthesized(Seq(Exists, Sp, F.Id("a"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Sp, To, Sp, Seq(Mathbb, Grp(F.Id("Z"))), Sp, Comma, Sp, Parenthesized(Seq(Forall, Sp, F.Id("n"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Sp, Comma, Sp, Parenthesized(Seq(F.Id("a"), Sp, F.Id("n"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("Q"))))), Sp, Eq, Sp, F.Id("eCoeff"), Sp, Parenthesized(Seq(new Formula.Power(F.Id("C"),D(1)))), Sp, Parenthesized(Seq(D(2), Sp, Cdot, Sp, F.Id("n"))))), Sp, Land, Sp, Parenthesized(Seq(Forall, Sp, F.Id("k"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Sp, Comma, Sp, D(1), Sp, Le, Sp, F.Id("k"), Sp, Implies, Sp, Exists, Sp, F.Id("N"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Sp, Comma, Sp, Forall, Sp, F.Id("n"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Sp, Comma, Sp, F.Id("N"), Sp, Le, Sp, F.Id("n"), Sp, Implies, Sp, Qualified("Int","ModEq"), Sp, Parenthesized(Seq(F.Id("k"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("Z"))))), Sp, Parenthesized(Seq(F.Id("a"), Sp, Parenthesized(Seq(F.Id("n"), Sp, Plus, Sp, new Formula.Power(Parenthesized(Seq(Qualified("Nat","totient"), Sp, F.Id("k"))),D(2)))))), Sp, Parenthesized(Seq(F.Id("a"), Sp, F.Id("n")))))))))));

    private static Formula Formula17() => Disp(Seq(Exists, Sp, Parenthesized(Seq(F.Id("H"), Sp, F.Id("C"), Sp, Colon, Sp, F.Id("PowerSeries"), Sp, Seq(Mathbb, Grp(F.Id("Q"))))), Sp, Comma, Sp, Qualified("PowerSeries","constantCoeff"), Sp, F.Id("H"), Sp, Eq, Sp, D(0), Sp, Land, Sp, Qualified("PowerSeries","derivative"), Sp, F.Id("H"), Sp, Eq, Sp, new Formula.Power(F.Id("C"),D(3)), Sp, Land, Sp, F.Id("C"), Sp, Eq, Sp, Qualified("PowerSeries","C"), Sp, Parenthesized(Seq(D(1), Sp, Slash, Sp, D(2), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("Q"))))), Sp, Cdot, Sp, Parenthesized(Seq(Qualified("PowerSeries","subst"), Sp, F.Id("H"), Sp, Parenthesized(Seq(Qualified("PowerSeries","exp"), Sp, Seq(Mathbb, Grp(F.Id("Q"))))), Sp, Plus, Sp, Qualified("PowerSeries","subst"), Sp, Parenthesized(Seq(Minus, Sp, F.Id("H"))), Sp, Parenthesized(Seq(Qualified("PowerSeries","exp"), Sp, Seq(Mathbb, Grp(F.Id("Q"))))))), Sp, Land, Sp, Parenthesized(Seq(Exists, Sp, F.Id("a"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Sp, To, Sp, Seq(Mathbb, Grp(F.Id("Z"))), Sp, Comma, Sp, Parenthesized(Seq(Forall, Sp, F.Id("n"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Sp, Comma, Sp, Parenthesized(Seq(F.Id("a"), Sp, F.Id("n"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("Q"))))), Sp, Eq, Sp, F.Id("eCoeff"), Sp, Parenthesized(Seq(new Formula.Power(F.Id("C"),D(1)))), Sp, Parenthesized(Seq(D(2), Sp, Cdot, Sp, F.Id("n"))))), Sp, Land, Sp, Parenthesized(Seq(Forall, Sp, F.Id("k"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Sp, Comma, Sp, D(1), Sp, Le, Sp, F.Id("k"), Sp, Implies, Sp, Exists, Sp, F.Id("N"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Sp, Comma, Sp, Forall, Sp, F.Id("n"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Sp, Comma, Sp, F.Id("N"), Sp, Le, Sp, F.Id("n"), Sp, Implies, Sp, Qualified("Int","ModEq"), Sp, Parenthesized(Seq(F.Id("k"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("Z"))))), Sp, Parenthesized(Seq(F.Id("a"), Sp, Parenthesized(Seq(F.Id("n"), Sp, Plus, Sp, new Formula.Power(Parenthesized(Seq(Qualified("Nat","totient"), Sp, F.Id("k"))),D(2)))))), Sp, Parenthesized(Seq(F.Id("a"), Sp, F.Id("n")))))))));
}
