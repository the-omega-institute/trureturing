using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ArithSums;

internal sealed class HannaLaurentRowSumsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ArithSums/HannaLaurentRowSums.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/ArithSums/hanna2025a391810");
    private static Formula N => Seq(Mathbb, new Formula.LatexGroup([F.Id("N")]));
    private static Formula Z => Seq(Mathbb, new Formula.LatexGroup([F.Id("Z")]));
    private static Formula V(string name) => F.Id(name);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula Eqn(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula LtRel(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Ne(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.NotEqual, b);
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Add(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(a, b);
    private static Formula Negative(Formula a) => Seq(Minus, a);
    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula Positive(Formula body) =>
        All("n", N, Imp(LtRel(D(0), V("n")), body));
    private static Formula SumBelow(string name, Formula upper, Formula body) => Seq(
        Sum, Underscore, new Formula.LatexGroup([
            Seq(D(0), Sp, Leq, Sp, V(name), Sp, Lt, Sp, upper)]), Sp, body);
    private static Formula Coeff(Formula f, Formula d) => Call("coeff", f, d);
    private static Formula Entry => Call("rowEntry", V("n"), V("m"));
    private static Formula Bound => Call("rowBound", V("n"));
    private static Formula Series => Call("series", V("n"));
    private static Formula Row => Call("rowPolynomial", V("n"));
    private static Formula Summand => Call("summand", V("n"), V("k"));
    private static Formula Coefficient => Coeff(Series, Negative(V("m")));

    public DocumentDefinition Create()
    {
        var j = V("j");
        var n = V("n");
        var k = V("k");
        var d = V("d");
        var x = Call("X");
        return DocumentDefinition.Create(ScribeNode.Create(
            "The nonpositive Laurent coefficients in A391810 have zero full row sum.",
            H("Hanna's bilateral Laurent rows"), Blocks(
                Node("z", "Laurent monomials",
                    All("k", Z, Eqn(Call("z", k), Call("single", k, D(1)))),
                    "The monomial x to the integer power k has coefficient one at k and zero elsewhere.",
                    DescribeRole.Definition),
                Node("summand", "The original rational summand",
                    All("n", N, All("k", Z, Eqn(Summand,
                        Mul(Call("z", k), Pow(Sub(D(1), Call("z", k)), Add(n, k)))))),
                    "Work in rational Laurent series expanded at zero. Integer powers use the field inverse for negative exponents. For positive n the zero-index term vanishes.",
                    DescribeRole.Definition),
                Node("summand_order", "The order of a nonzero-index summand",
                    All("n", N, All("k", Z, Imp(Ne(k, D(0)),
                        Eqn(Call("order", Summand), Add(k, Mul(Add(n, k), Call("min", D(0), k))))))),
                    "The order of 1 minus x to the k is the minimum of zero and k. Orders add under multiplication and multiply by the integer exponent under powers of a nonzero series.",
                    DescribeRole.Theorem),
                Node("summand_lower_bound", "A common lower support bound",
                    Positive(All("k", Z, All("d", Z, Imp(Ne(Coeff(Summand, d), D(0)),
                        new Formula.Relation(Negative(Pow(Add(n, D(1)), D(2))),
                            FormulaRelationOperator.LessThanOrEqual, d))))),
                    "Completing the square in the negative-index order gives a uniform lower bound. This makes the union of supports well founded.",
                    DescribeRole.Theorem),
                Node("coefficient_finite", "Finite contributions to each coefficient",
                    Positive(All("d", Z, Call("Finite", Seq(OpenBrace, k, Sp, InMacro, Sp, Z,
                        Sp, Vert, Sp, Ne(Coeff(Summand, d), D(0)), CloseBrace)))),
                    "For each fixed exponent, only a bounded integer interval of outer indices can have a nonzero coefficient. Both tails eventually have order above that exponent.",
                    DescribeRole.Theorem),
                Node("family", "The formally summable bilateral family",
                    Positive(All("k", Z, Eqn(Call("family", n, k), Summand))),
                    "The family bundles the original summands with their common lower support bound and finite contributions at every coefficient. Its formal sum is therefore a genuine Laurent series.",
                    DescribeRole.Definition),
                Node("series", "The original bilateral Laurent sum",
                    Positive(Eqn(Series, Call("hsum", Call("family", n)))),
                    "The formal Hahn sum adds each coefficient using its finitely many contributing terms. It retains all positive and negative integer outer indices.",
                    DescribeRole.Definition),
                Node("rowPolynomial", "The finite inverse-variable row polynomial",
                    All("n", N, Eqn(Row, Add(Negative(D(1)), SumBelow("j", n,
                        Mul(Pow(x, Add(j, D(1))),
                            Pow(Sub(D(1), Pow(x, Add(j, D(1)))), Sub(n, Add(j, D(1))))))))),
                    "Here x denotes the polynomial variable, corresponding to the inverse of the original Laurent variable. The indices minus one through minus n give these polynomial summands. The index minus n minus one supplies constant minus one; all remaining outer indices have only positive Laurent powers.",
                    DescribeRole.Definition),
                Node("series_coefficient", "Exact integer identification of every nonpositive coefficient",
                    Positive(All("m", N, Eqn(Coefficient, Call("rationalCast", Coeff(Row, V("m")))))),
                    "This identity proves that the finite polynomial describes the full nonpositive truncation, including its constant term, and that every such rational coefficient comes from an integer.",
                    DescribeRole.Theorem),
                Node("rowBound", "The published inclusive row bound",
                    All("n", N, Eqn(Bound, Pow(new Formula.Floor(
                        new Formula.Fraction(Add(n, D(1)), D(2))), D(2)))),
                    "The last coefficient index is floor((n+1)/2) squared.",
                    DescribeRole.Definition),
                Node("row_degree", "The exact full-row support bound",
                    All("n", N, new Formula.Relation(Call("natDegree", Row),
                        FormulaRelationOperator.LessThanOrEqual, Bound)),
                    "Expand each polynomial summand by the binomial theorem. Its terms below the highest term have exponent at most the row bound. If n is even, the highest terms cancel under reflection of the outer index. If n is odd, their degrees already satisfy the bound.",
                    DescribeRole.Theorem),
                Node("rowEntry", "Integer triangle coefficients",
                    All("n", N, All("m", N, Eqn(Entry, Coeff(Row, V("m"))))),
                    "The coefficient bridge identifies this integer with T(n,m) in the original Laurent definition.",
                    DescribeRole.Definition),
                Node("result", "The universal zero row sum with its original-series support",
                    Positive(And(Eqn(SumBelow("m", Add(Bound, D(1)), Entry), D(0)),
                        And(Eqn(SumBelow("m", Add(Bound, D(1)), Coefficient), D(0)),
                            All("m", N, Imp(LtRel(Bound, V("m")), Eqn(Coefficient, D(0))))))),
                    "Evaluate only the finite inverse-variable polynomial at one. Every outer term vanishes except its final term, which equals one and cancels the constant minus one. The degree bound makes this evaluation the full inclusive row sum. The coefficient bridge transfers both the zero sum and the full support bound to the original bilateral Laurent series.",
                    DescribeRole.Theorem,
                    new OpenProblemResolutionClaim(ProblemSlugRef.Create(
                        "oeis-a391810-full-laurent-row-sums"), ResolutionKind.Proved)) )));
    }

    private static DocumentBlock Node(string name, string title, Formula formula,
        string prose, DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create("a391810-" + name.Replace("_", "").ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(Disp(formula)),
            name == "z" || name == "summand" || name == "rowBound"
                ? AssessedProvenance.FromLiterature(Source)
                : AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
