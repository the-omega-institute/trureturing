using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ArithSums;

internal sealed class SchulteArbitraryGcdQuotientConvolutionDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ArithSums/SchulteArbitraryGcdQuotientConvolution.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/ArithSums/schulte2022a350900");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Arbitrary complex weights on Schulte's gcd quotient form a Dirichlet convolution.",
        H("Schulte's arbitrary-function gcd-quotient convolution"),
        Blocks(
            Paragraph(Text(
                "Let N denote the natural numbers including zero, P the positive "
                + "integers, and C the complex numbers. All gcd operations and slashes "
                + "are natural-number operations. Write ofNat for the canonical map "
                + "from N to C, phi for Euler's totient, and ite(p,x,y) for x when p "
                + "holds and y otherwise. Divisor sums use positive divisors; at zero "
                + "the natural divisor set is empty. No value of a function on P at "
                + "zero is assumed.")),
            Node("square", "The original ordered square", SquareFormula(),
                "For a function g on N, square(g,n) sums over every ordered pair "
                + "1<=i<=n and 1<=k<=n, including the diagonal. For n>0, "
                + "h=gcd(gcd(i,k),n) is positive and divides g=gcd(i,n). Hence "
                + "q=g/h is positive, q*h=g, and q divides n. In particular every "
                + "summand queries a positive argument. The value at n=0 is an "
                + "empty sum, rather than an additional asserted source case.",
                DescribeRole.Definition, sourceDefinition: true),
            Node("H", "The divisor-totient function", HFormula(),
                "H is A057660, interpreted in C. Each divisor e and phi(e) is "
                + "cast separately before multiplication.", DescribeRole.Definition, sourceDefinition: true),
            Node("positiveLift", "A zero extension of a positive-domain weight", LiftFormula(),
                "At n>0 the expression f(n) means f applied to the positive "
                + "integer with value n. The extension is zero only at n=0. "
                + "For arbitrary z in C, write extension(f,z) for the function "
                + "d |-> ite(0<d,f(d),z); it agrees with positiveLift(f) on P.",
                DescribeRole.Definition),
            Node("A", "The positive-domain square statistic", AFormula(),
                "A is defined by the original square with a zero extension, "
                + "independently of its later convolution formula. Every function "
                + "P -> C is permitted, without reality, positivity, boundedness "
                + "or multiplicativity assumptions.", DescribeRole.Definition, sourceDefinition: true),
            Node("PositiveMultiplicative", "Normalized coprime multiplicativity", MultiplicativeFormula(),
                "Multiplicative means f(1)=1 and f(ab)=f(a)f(b) for coprime "
                + "positive a,b. Complete multiplicativity is not required. "
                + "Coprimality is that of their underlying natural numbers.",
                DescribeRole.Definition, sourceDefinition: true),
            Node("result", "The whole arbitrary-function identity and its source clauses", ResultFormula(),
                "For every f:P -> C, the first clause holds for every n>0. "
                + "Its right side is the Dirichlet convolution of the pointwise "
                + "product f(d)*phi(d) with H, not a pointwise product of those "
                + "two functions. The second clause preserves normalization at "
                + "one and every coprime positive product. The third permits "
                + "every zero-extension value z. In the last clause, idPositive "
                + "is d |-> ofNat(d) on P, and rowSum is the natural-valued "
                + "SchulteGcdQuotientRowSumConvolution.rowSum, cast into C.",
                DescribeRole.Theorem),
            Paragraph(Text(
                "To derive the identity, first replace each interval 1..n by "
                + "0..n-1: the endpoint values agree. For fixed i put g=gcd(i,n). "
                + "Associativity and commutativity of gcd identify the inner "
                + "argument with g/gcd(g,k). This has period g, and g divides n, "
                + "so its weighted sum is n/g complete periods. In one period, "
                + "group by e=gcd(g,k), whose multiplicity is phi(g/e), and "
                + "reindex d=g/e. The inner sum is therefore "
                + "(n/g)*Sum_{d|g} phi(d)*f(d). Grouping the outer indices by "
                + "g gives multiplicity phi(n/g). The complex gcd regrouping "
                + "uses the real and imaginary parts of the existing "
                + "RoldanCirculantEnergyP2Q3.sum_gcd_multiplicity theorem.")),
            Paragraph(Text(
                "In arithmetic-function notation let G be the pointwise product "
                + "of the zero extension of f with phi, B the pointwise product "
                + "id*phi, and Z the divisor-convolution unit-summand function "
                + "zeta, equal to one on P and zero at zero. Then H=B*Z and the "
                + "regrouped square is B*(Z*G)=G*(B*Z), where the displayed "
                + "stars denote Dirichlet convolution. Expanding the last "
                + "convolution yields the first clause. Totient, id and zeta "
                + "are normalized multiplicative functions; pointwise products "
                + "and Dirichlet convolutions preserve that property, yielding "
                + "the second clause. Positivity of q proves the third clause. "
                + "For idPositive its zero extension is exactly ofNat, so "
                + "distributing natural casts through both finite sums gives "
                + "the row-sum clause.")),
            Paragraph(Text(
                "The source is the complete arbitrary-function COMMENTS sentence "
                + "of OEIS A350900 in the revision identified by the source note. "
                + "The separate triangle-symmetry assertion is outside this "
                + "statement. The mathematics uses classical gcd-fibre counting "
                + "and arithmetic-function convolution; it asserts no historical "
                + "priority. The source note records the uninspected literature "
                + "whose contents cannot be inferred from bibliographic data.")))));

    private static DocumentBlock Node(string name, string title, Formula formula,
        string prose, DescribeRole role, bool sourceDefinition = false) => Describe.Lean(
            DescribeId.Create("a350900-arbitrary-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(Disp(formula)),
            sourceDefinition ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role);

    private static Formula SquareFormula()
    {
        var i = V("i"); var k = V("k"); var n = V("n");
        var q = Divide(Call("gcd", i, n), Call("gcd", Call("gcd", i, k), n));
        return All("g", Arrow(N(), C()), All("n", N(),
            Eqn(Call("square", V("g"), n), RangeSum(i, n, RangeSum(k, n, Call("g", q))))));
    }

    private static Formula HFormula() => All("n", N(),
        Eqn(Call("H", V("n")), DivisorSum(V("e"), V("n"),
            Mul(Cast(V("e")), Cast(Call("phi", V("e")))))));

    private static Formula LiftFormula() => All("f", Arrow(P(), C()), All("n", N(),
        Eqn(Call("positiveLift", V("f"), V("n")),
            Call("ite", Positive(V("n")), Call("f", V("n")), D(0)))));

    private static Formula AFormula() => All("f", Arrow(P(), C()), All("n", N(),
        Eqn(Call("A", V("f"), V("n")), Call("square", Call("positiveLift", V("f")), V("n")))));

    private static Formula MultiplicativeFormula()
    {
        var f = V("f"); var a = V("a"); var b = V("b");
        return All("f", Arrow(P(), C()), Iffn(Call("PositiveMultiplicative", f),
            Both(Eqn(Call("f", D(1)), D(1)), All("a", P(), All("b", P(),
                Imp(Eqn(Call("gcd", a, b), D(1)),
                    Eqn(Call("f", Mul(a, b)), Mul(Call("f", a), Call("f", b)))))))));
    }

    private static Formula ResultFormula()
    {
        var f = V("f"); var n = V("n"); var d = V("d");
        var a = V("a"); var b = V("b");
        var identity = All("n", N(), Imp(Positive(n),
            Eqn(Call("A", f, n), DivisorSum(d, n,
                Mul(Mul(Call("positiveLift", f, d), Cast(Call("phi", d))), Call("H", Divide(n, d)))))));
        var closure = Imp(Call("PositiveMultiplicative", f),
            Both(Eqn(Call("A", f, D(1)), D(1)), All("a", N(), All("b", N(),
                Imp(Positive(a), Imp(Positive(b), Imp(Eqn(Call("gcd", a, b), D(1)),
                    Eqn(Call("A", f, Mul(a, b)), Mul(Call("A", f, a), Call("A", f, b))))))))));
        var extension = All("z", C(), All("n", N(), Imp(Positive(n),
            Eqn(Call("square", Call("extension", f, V("z")), n), Call("A", f, n)))));
        var row = All("n", N(), Eqn(Call("A", V("idPositive"), n), Cast(Call("rowSum", n))));
        return All("f", Arrow(P(), C()), new Formula.Aligned([
            Wrap(identity), Seq(Land, Sp, Wrap(closure)),
            Seq(Land, Sp, Wrap(extension)), Seq(Land, Sp, Wrap(row))]));
    }

    private static Formula V(string name) => F.Id(name);
    private static Formula N() => Seq(Mathbb, Grp(V("N")));
    private static Formula P() => Seq(Mathbb, Grp(V("P")));
    private static Formula C() => Seq(Mathbb, Grp(V("C")));
    private static Formula Arrow(Formula a, Formula b) => new Formula.TypeArrow(a, b);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(name))), [.. args]);
    private static Formula Cast(Formula n) => Call("ofNat", n);
    private static Formula Eqn(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Positive(Formula a) => new Formula.Relation(D(0), FormulaRelationOperator.LessThan, a);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Both(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Iffn(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula Wrap(Formula value) => Seq(Open, value, Close);
    private static Formula Divide(Formula a, Formula b) => Seq(Open, a, Close, Sp, Slash, Sp, Open, b, Close);
    private static Formula RangeSum(Formula index, Formula n, Formula body) =>
        Seq(new Formula.Subscript(Sum, Seq(index, Sp, Eq, Sp, D(1), Dot, Dot, n)), Sp, body);
    private static Formula DivisorSum(Formula index, Formula n, Formula body) =>
        Seq(new Formula.Subscript(Sum, Seq(index, Sp, Mid, Sp, n)), Sp, body);
}
