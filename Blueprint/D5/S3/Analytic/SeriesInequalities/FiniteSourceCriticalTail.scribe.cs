using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.SeriesInequalities;

internal sealed class FiniteSourceCriticalTailDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite source boundaries have geometric antidiagonal tails at the critical weight.",
        H("Finite Source Critical Tail"),
        Blocks(Describe.Lean(
            DescribeId.Create("finite-source-critical-tail"),
            DeclarationHandle.Create(
                "D5/S3/Analytic/SeriesInequalities/FiniteSourceCriticalTail."
                + "finite_source_critical_tail"),
            H("A larger radius controls the actual recursive output"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Let K be a normed ring, including the real or complex numbers. "
                    + "The boundary b is bounded in norm by A and vanishes at every index "
                    + "greater than M. The extension E has E(n,0)=b(n) and "
                    + "E(n,k+1)=E(n+1,k)-sum over j=0,...,k of E(n,j)b(k-j).")),
                Paragraph(Text(
                    "Tail(rho,b,L) is the supremum of rho^(n+k) times the norm of "
                    + "E(n,k), over all natural n and k with L at most n+k. The theorem "
                    + "proves that these sets of values are bounded and that their "
                    + "suprema converge to zero.")),
                Paragraph(Text(
                    "The finite mass polynomial g(x)=x+A sum over i=0,...,M of x^(i+1) "
                    + "satisfies g(rho)=1-(1-rho)rho^(M+1)<1. Continuity supplies "
                    + "rho<R<1 with g(R)<1. Strong induction on the column index gives "
                    + "the uniform bound norm(E(n,k)) R^k at most A.")),
                Paragraph(Text(
                    "Writing q=rho/R, one has rho at most q and q<1. Thus every weighted "
                    + "entry on the Lth tail is at most A q^L. This controls the complete "
                    + "output of a finitely supported boundary, including its infinitely "
                    + "many columns. The radius may depend on the support bound M.")),
                Paragraph(Text(
                    "The statement proves finite-source tail decay. It does not assert "
                    + "a rational Taylor-germ identity, norm-closedness of the full source "
                    + "image, or compactness of that image."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));
        Formula reals = Seq(Mathbb, Grp(F.Id("R")));
        Formula field = F.Id("K");
        Formula a = F.Id("A");
        Formula rho = F.Id("rho");
        Formula radius = F.Id("R");
        Formula support = F.Id("M");
        Formula boundary = F.Id("b");
        Formula i = F.Id("i");
        Formula n = F.Id("n");
        Formula k = F.Id("k");
        Formula level = F.Id("L");
        Formula bi = Call("b", i);
        Formula entry = Call("extension", boundary, n, k);
        Formula tail = Call("Tail", rho, boundary, level);
        Formula ratio = new Formula.Fraction(rho, radius);
        Formula hypotheses = And(
            Call("NormedRing", field),
            And(LtFormula(D(0), a),
                And(LtFormula(D(0), rho),
                    And(LtFormula(rho, D(1)),
                        And(EqFormula(Mul(a, rho), Pow(Sub(D(1), rho), D(2))),
                            And(
                                ForAll([Bound("i", naturals)],
                                    LeqFormula(Call("norm", bi), a)),
                                ForAll([Bound("i", naturals)],
                                    Implies(LtFormula(support, i), EqFormula(bi, D(0))))))))));
        Formula estimates = And(
            ForAll([Bound("n", naturals), Bound("k", naturals)],
                LeqFormula(Mul(Call("norm", entry), Pow(radius, k)), a)),
            And(
                ForAll([Bound("L", naturals)], LeqFormula(tail, Mul(a, Pow(ratio, level)))),
                Call("Tendsto", Call("Tail", rho, boundary), F.Id("atTop"), Call("nhds", D(0)))));
        Formula conclusion = new Formula.BindMany(
            FormulaQuantifier.Exists, [Bound("R", reals)],
            And(LtFormula(rho, radius), And(LtFormula(radius, D(1)), estimates)));
        return Disp(ForAll(
            [Bound("K", F.Id("Type")), Bound("A", reals), Bound("rho", reals),
             Bound("M", naturals), Bound("b", Seq(naturals, To, field))],
            Implies(hypotheses, conclusion)));
    }

    private static Formula ForAll(Formula.BoundVariable[] variables, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables], body);
    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
    private static Formula Mul(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Sub(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Pow(Formula value, Formula exponent) => new Formula.Power(value, exponent);
    private static Formula EqFormula(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula LtFormula(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula LeqFormula(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);
    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);
}
