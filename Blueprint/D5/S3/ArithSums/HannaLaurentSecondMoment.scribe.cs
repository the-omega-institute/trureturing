using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ArithSums;

internal sealed class HannaLaurentSecondMomentDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/ArithSums/hanna2025a391810");
    private static Formula V(string name) => F.Id(name);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula Add(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(a, b);
    private static Formula Eqn(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Neg(Formula a) => Seq(Minus, Open, a, Close);
    private static Formula N => Seq(Mathbb, new Formula.LatexGroup([V("N")]));
    private static Formula Bound => Pow(new Formula.Floor(
        new Formula.Fraction(Add(V("n"), D(1)), D(2))), D(2));
    private static Formula Moment => Seq(Sum, Underscore,
        new Formula.LatexGroup([Eqn(V("k"), D(0))]), Caret,
        new Formula.LatexGroup([Bound]), Sp,
        Mul(Pow(V("k"), D(2)), Call("coeff", Call("series", V("n")), Neg(V("k")))));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The full signed second moment of Hanna's bilateral Laurent rows.",
        H("A391810: the signed Laurent second moment"), Blocks(
            Paragraph(Text("For every natural n>=2, formula (4) concerns T(n,k), "
                + "the coefficient at zero of x^k times the full bilateral Laurent sum "
                + "over all integers j of x^j*(1-x^j)^(n+j), expanded at zero. "
                + "Equivalently T(n,k) is the coefficient at -k of that sum. "
                + "Integer exponents use Laurent-field inverses. The inherited "
                + "series is the formally summable Hahn sum, with every outer integer "
                + "index retained. No value of the bilateral series at one is used.")),
            Paragraph(Text("Put y=x^(-1). The exact coefficient identity "
                + "HannaLaurentRowSums.series_coefficient identifies T(n,k) with the "
                + "integer coefficient of P_n(y)=-1+sum_{q=1..n} "
                + "y^q*(1-y^q)^(n-q). The constant -1 comes from outer index -(n+1); "
                + "the remaining nonpositive coefficients come from indices -1 through -n. "
                + "The inherited row_degree bound is natDegree(P_n)<=floor((n+1)/2)^2. "
                + "Thus the published inclusive endpoint contains the full coefficient support.")),
            Paragraph(Text("For the Euler operator E=y*d/dy, the coefficient of y^k "
                + "in E^2(P) is k^2 times the coefficient of y^k in P. E^2 does not "
                + "increase degree. Evaluating this finite polynomial at y=1 therefore "
                + "gives the full weighted coefficient sum, including k=0 and the upper endpoint.")),
            Paragraph(Text("For the term y^q*(1-y^q)^m, E^2 evaluated at one is q^2 "
                + "when m=0, -3*q^2 when m=1, 2*q^2 when m=2, and zero when m>=3. "
                + "For n>=3 only q=n,n-1,n-2 remain. Their sum is "
                + "n^2-3*(n-1)^2+2*(n-2)^2=-(2*n-5). For n=2 the two available "
                + "terms give 4-3=1, the same signed expression. The constant -1 is "
                + "annihilated by E^2. Integer subtraction precedes negation and the cast to rationals.")),
            Describe.Lean(DescribeId.Create("a391810-second-moment-result"),
                DeclarationHandle.Create("D5/S3/ArithSums/HannaLaurentSecondMoment.result"),
                H("The complete formula (4)"),
                StatementSource.FromAuthor(Disp(new Formula.Bind(
                    FormulaQuantifier.ForAll, FormulaIdentifier.Create("n"), N,
                    new Formula.Logic(
                        new Formula.Relation(D(2), FormulaRelationOperator.LessThanOrEqual, V("n")),
                        FormulaLogicOperator.Implies,
                        Eqn(Moment, Neg(Sub(Mul(D(2), Call("toInt", V("n"))), D(5)))))))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The theorem holds for every natural n>=2. "
                    + "The coefficient is rational, with the signed integer right side "
                    + "cast to the rationals. Natural division by two is performed before "
                    + "squaring the inclusive bound. The coefficient bridge transports "
                    + "the finite polynomial identity to the original series. This settles "
                    + "the second moment in the stated expansion convention; it asserts "
                    + "no other moment formula or analytic convergence at one."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a391810-second-moment"),
                    ResolutionKind.Proved)))));
}
