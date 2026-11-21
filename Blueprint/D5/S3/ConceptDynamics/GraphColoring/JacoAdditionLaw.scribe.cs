using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.GraphColoring;

internal sealed class JacoAdditionLawDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ConceptDynamics/GraphColoring/JacoAdditionLaw.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Certificates/kok2014finitejaco");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The maximum degrees of finite linear Jaco graphs obey an exact additive correction law with golden fractional parts.",
        H("The corrected Jaco maximum-degree addition law"),
        Blocks(
            Node("jaco-law-delta", "Maximum degree as an integer", "delta",
                Disp(Equal(Delta(F.Id("n")), Call("maxDegree", Call("jaco", F.Id("n"))))),
                "delta n is the ordinary maximum degree of the existing finite linear Jaco graph jaco n on the labels 1 through n, cast to an integer so that differences may be negative. The order-zero graph has no vertices and maximum degree zero.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("jaco-law-frac", "The golden fractional part", "frac",
                Disp(Equal(X(F.Id("n")), Call("fract", new Formula.Fraction(Add(F.Id("n"), D(2)), F.Id("phi"))))),
                "frac n is the fractional part of (n+2)/phi, where phi=(1+sqrt(5))/2 is the golden ratio; it lies in [0,1).",
                DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("jaco-law-alpha", "The correction constant", "alpha",
                Disp(Equal(F.Id("alpha"), Subtract(Call("sqrt", D(5)), D(2)))),
                "alpha=sqrt(5)-2, approximately 0.236, equals 2/phi-1, since 2/phi=sqrt(5)-1.",
                DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("jaco-law-sum", "The multi-summand correction law", "sum_law", SumFormula(),
                "For every finite family of natural orders n_j, j in s, with r=|s| members and total N, the maximum degree of J_N exceeds the sum of the members' maximum degrees by exactly floor(sum_j frac(n_j)-(r-1)alpha). Proof: the existing maximum-degree theorem gives delta n=floor((n+2)/phi)-1 for n at least two; the graphs of order zero and one have at most one vertex and maximum degree zero, which matches floor(2/phi)-1=floor(3/phi)-1=0. Hence delta n=(n+2)/phi-frac(n)-1 as real numbers. Subtracting, the summands' constants (n_j+2)/phi cancel against (N+2)/phi except for (2-2r)/phi, and 2/phi=sqrt(5)-1 turns the remaining constant into -(r-1)alpha. The integer difference therefore equals sum_j frac(n_j)-(r-1)alpha-frac(N), and since frac(N) lies in [0,1) it is the floor of sum_j frac(n_j)-(r-1)alpha. The source states only the two-branch conjecture for two distinct summands at least three, which is false; this law replaces it for any number of summands, including the empty family, where both sides vanish.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("jaco-law-result", "Two-summand trichotomy and witnesses", "result", ResultFormula(),
                "The first clause restates the multi-summand law. For any two orders n,m it reads delta(n+m)-delta n-delta m=floor(frac n+frac m-alpha). Because both fractional parts lie in [0,1) and 0<alpha<1, the argument lies in [-alpha,2-alpha), so the correction is -1 exactly when frac n+frac m<alpha, 0 exactly when alpha<=frac n+frac m<1+alpha, and 1 exactly when 1+alpha<=frac n+frac m. Exact rational bounds 8/5<phi<13/8 give delta 3=2, delta 4=2, delta 6=3, delta 7=4, delta 10=6, delta 11=7 and delta 14=8, so the distinct pairs (3,11), (3,4) and (4,6) attain the values -1, 0 and 1. The pair (3,11) is the one that refutes the source's first branch, and (4,6) realises the plus-one correction.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)))));

    private static Formula SumFormula() => Disp(SumBody());

    private static Formula SumBody()
    {
        var j = F.Id("j");
        var nj = Sub(F.Id("n"), j);
        var lhs = Subtract(Delta(SumOver(nj)), SumOver(Delta(nj)));
        var rhs = new Formula.Floor(Subtract(SumOver(X(nj)),
            Multiply(Par(Subtract(Call("card", F.Id("s")), D(1))), F.Id("alpha"))));
        return All("s", Call("Finset", F.Id("iota")), All("n", Arrow(F.Id("iota"), Nat()),
            Equal(lhs, rhs)));
    }

    private static Formula ResultFormula()
    {
        var n = F.Id("n");
        var m = F.Id("m");
        var c = Subtract(Subtract(Delta(Add(n, m)), Delta(n)), Delta(m));
        var t = Add(X(n), X(m));
        var a = F.Id("alpha");
        var two = And(Equal(c, new Formula.Floor(Subtract(t, a))),
            And(Iff(Equal(c, new Formula.Negate(D(1))), Lt(t, a)),
                And(Iff(Equal(c, D(0)), And(Le(a, t), Lt(t, Add(D(1), a)))),
                    Iff(Equal(c, D(1)), Le(Add(D(1), a), t)))));
        var witnesses = And(Equal(Subtract(Subtract(Delta(Add(D(3), D(1, 1))), Delta(D(3))), Delta(D(1, 1))), new Formula.Negate(D(1))),
            And(Equal(Subtract(Subtract(Delta(Add(D(3), D(4))), Delta(D(3))), Delta(D(4))), D(0)),
                Equal(Subtract(Subtract(Delta(Add(D(4), D(6))), Delta(D(4))), Delta(D(6))), D(1))));
        return Disp(And(SumBody(),
            And(All("n", Nat(), All("m", Nat(), two)), witnesses)));
    }

    private static DocumentBlock Node(string id, string title, string declaration, Formula formula,
        string prose, DescribeRole role, AssessedProvenance provenance) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(formula), provenance, Blocks(Paragraph(Text(prose))), role);
    private static Formula Arrow(Formula a, Formula b) => new Formula.TypeArrow(a, b);
    private static Formula Nat() => new Formula.NamedConstant(FormulaIdentifier.Create("Nat"));
    private static Formula Delta(Formula n) => Call("delta", n);
    private static Formula X(Formula n) => Call("frac", n);
    private static Formula Sub(Formula a, Formula b) => new Formula.Subscript(a, b);
    private static Formula SumOver(Formula body) => Seq(new Formula.Subscript(Sum, Seq(F.Id("j"), Sp, F.Id("in"), Sp, F.Id("s"))), Sp, Par(body));
    private static Formula Par(Formula x) => Seq(Open, x, Close);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(Par(a), FormulaLogicOperator.And, Par(b));
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(Par(a), FormulaLogicOperator.Iff, Par(b));
    private static Formula All(string n, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(n), type, body);
}
