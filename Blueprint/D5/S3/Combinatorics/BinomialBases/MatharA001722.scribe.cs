using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.BinomialBases;

internal sealed class MatharA001722Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/BinomialBases/MatharA001722.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The signed first-kind Stirling sum defining OEIS A001722 satisfies Mathar's third-order recurrence for every index at least three. Its ordinary rational formal generating series is annihilated by a nonzero fourth-order differential operator.",
        H("Mathar's recurrence and D-finiteness for A001722"),
        Blocks(
            Node("s", "Signed Stirling coefficients", Signed(),
                "The coefficient convention is signed: s(N,K) is the coefficient of X to the K in the product of X-i for i from zero through N-1. The empty product is one. Coefficients and casts are in the integers.", DescribeRole.Definition),
            Node("a", "The full coefficient sum", Sequence(),
                "This is Borislav Crstici's all-index formula in OEIS A001722, revision 26, https://oeis.org/A001722/internal?fmt=text. The canonical entry name is Generalized Stirling numbers [n+7,7]_5. The range contains both zero and n; the binomial coefficient is computed in the naturals and cast to the integers. No recurrence or initial-value characterization is assumed.", DescribeRole.Definition),
            Node("G", "Ordinary formal generating series", Generating(),
                "G is the ordinary formal power series whose nth coefficient is a(n) cast to the rationals. It is not an exponential generating series, and no convergence assertion is involved.", DescribeRole.Definition),
            Node("claim", "The two assertions", ClaimFormula(),
                "The first assertion is Mathar's recurrence in the formula field of OEIS A001722, revision 26. Every n at least three is included. Subtraction in the subscripts is natural subtraction; n is cast to the integers before computing the polynomial coefficients. The second assertion requires a homogeneous polynomial-coefficient differential equation for the same full G, with at least one nonzero coefficient polynomial. The inclusion is the canonical map from rational polynomials to rational formal power series; D is formal differentiation, and its zeroth iterate is the identity.", DescribeRole.Definition),
            Node("result", "Recurrence and a homogeneous annihilator", Disp(And(Recurrence(), DFinite())),
                "Set B(n)=(-1)^n times the Taylor translate at -5 of the falling product of length n+2. The Hasse derivative coefficient formula gives coeff(2,B(n))=a(n), directly from the signed sum. Multiplication of the falling product by its next factor gives B(n+1)=B(n)(n+7-X). The combination B(m+3)-3(m+8)B(m+2)+(3m^2+45m+169)B(m+1)-(m+7)^3 B(m) equals -X^3 B(m); taking its second coefficient proves the recurrence. For the ordinary series, the fourth-order operator has coefficient polynomials p(0)=-18+254z-1029z^2, p(1)=1-24z+253z^2-1019z^3, p(2)=-3z^2+54z^3-289z^4, p(3)=3z^4-30z^5 and p(4)=-z^6. All higher p(j) are zero. Coefficient extraction reduces its equation to the recurrence multiplied by n+1. The two boundary coefficients use a(0)=1, a(1)=18 and a(2)=251. Thus every coefficient vanishes and p(4) is nonzero.", DescribeRole.Theorem)), []));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("mathar-a001722-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role);

    private static Formula N() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Z() => Seq(Mathbb, Grp(F.Id("Z")));
    private static Formula Q() => Seq(Mathbb, Grp(F.Id("Q")));
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Ex(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(Par(a), b);
    private static Formula Par(Formula a) => Seq(Open, a, Close);
    private static Formula Cast(Formula a, Formula type) => Par(Seq(a, Sp, Colon, Sp, type));
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(Par(a), FormulaLogicOperator.And, Par(b));
    private static Formula Sum(Formula k, Formula bound, Formula body) =>
        Seq(F.Sum, Underscore, Grp(k, Sp, InMacro, Sp, Call("range", bound)), Sp, Par(body));
    private static Formula Signed()
    {
        Formula n=F.Id("N"), k=F.Id("K"), i=F.Id("i");
        Formula product=Seq(Prod, Underscore, Grp(i,Sp,InMacro,Sp,Call("range",n)), Sp,
            Par(Sub(F.Id("X"),Call("C",Cast(i,Z())))));
        return Disp(All("N",N(),All("K",N(),Eq(Call("s",n,k),Call("coeff",product,k)))));
    }
    private static Formula Sequence()
    {
        Formula n=F.Id("n"), k=F.Id("k");
        Formula weight=Mul(Mul(Mul(Pow(new Formula.Negate(D(1)),Add(n,k)),
            Cast(Call("choose",Add(k,D(2)),D(2)),Z())),Pow(Cast(D(5),Z()),k)),
            Call("s",Add(n,D(2)),Add(k,D(2))));
        return Disp(All("n",N(),Eq(Call("a",n),Sum(k,Add(n,D(1)),weight))));
    }
    private static Formula Generating()
    {
        Formula n=F.Id("n");
        return Disp(All("n",N(),Eq(Call("coeff",n,F.Id("G")),Cast(Call("a",n),Q()))));
    }
    private static Formula Recurrence()
    {
        Formula n=F.Id("n"), x=Cast(n,Z());
        Formula body=Eq(Sub(Add(Add(Call("a",n),
            Mul(Mul(D(3),Par(Sub(new Formula.Negate(x),D(5)))),Call("a",Sub(n,D(1))))),
            Mul(Par(Add(Add(Mul(D(3),Pow(x,D(2))),Mul(D(2,7),x)),D(6,1))),Call("a",Sub(n,D(2))))),
            Mul(Pow(Add(x,D(4)),D(3)),Call("a",Sub(n,D(3))))),D(0));
        return All("n",N(),new Formula.Logic(Le(D(3),n),FormulaLogicOperator.Implies,Par(body)));
    }
    private static Formula DFinite()
    {
        Formula r=F.Id("r"), j=F.Id("j");
        Formula nonzero=Ex("j",N(),And(Le(j,r),
            new Formula.Relation(Call("p",j),FormulaRelationOperator.NotEqual,D(0))));
        Formula equation=Eq(Sum(j,Add(r,D(1)),Mul(Call("inclusion",Call("p",j)),
            Call("iterate",Call("derivative"),j,F.Id("G")))),D(0));
        return Ex("r",N(),Ex("p",new Formula.TypeArrow(N(),Call("Polynomial",Q())),And(nonzero,equation)));
    }
    private static Formula ClaimFormula() => Disp(new Formula.Logic(F.Id("claim"),
        FormulaLogicOperator.Iff,Par(And(Recurrence(),DFinite()))));
}
