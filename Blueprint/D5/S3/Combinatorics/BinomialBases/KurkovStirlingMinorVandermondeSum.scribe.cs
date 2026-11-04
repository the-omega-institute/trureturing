using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.BinomialBases;

internal sealed class KurkovStirlingMinorVandermondeSumDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Combinatorics/BinomialBases/KurkovStirlingMinorVandermondeSum.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/RecurrenceComposition/kurkov2026a396563");
    private const string SourceSentence = "Conjecture: B(n, k, m) = (Sum_{j_1=0..n} Sum_{j_2=0..j_1} ... Sum_{j_m=0..j_{m-1}} (-1)^(j_1 + j_2 + ... + j_m) * (Product_{1 <= q < p <= m} (j_q - j_p + p - q)^2) * Product_{t=1..m} (n+t-1)_{j_t} * (n-j_t+t)^(n+k) / (j_t+m-t)!) / (Product_{i=0..m-1} (n+i)!) where B(n, k, m) is the determinant of the k X k matrix with (i, j)-th entry |Stirling1(n+m+i, n+j)|, where (x)_{n} is the falling factorial defined as (x)_{n} = Product_{k=0..n-1} (x-k).";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Kurkov's three-parameter Stirling-minor Vandermonde sum.",
        H("A Stirling minor as a finite Vandermonde-square sum"),
        Blocks(
            Paragraph(Text("All parameters are natural numbers. The matrix indices in the OEIS source start at one; a Fin index i represents i+1. The unsigned cycle numbers are Nat.stirlingFirst. The domain Chain is the antitone-map type of KurkovNestedStirlingIdentity, so each tuple in the nested ranges is counted exactly once. Factorials, descending factorials and exponents are natural; all divisions and Vandermonde differences are rational. Natural subtraction has Lean's truncated meaning; the bounds on a chain make the displayed indices equal to their integer values.")),
            Node("B", "The first-kind Stirling minor", BDefinition(),
                "The source, OEIS A396563 FORMULA (unpaginated), defines the determinant in the sentence below. " + SourceSentence,
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("sourceTerm", "The signed summand", TermDefinition(),
                "The sign exponent is the sum of the chain values. Each pair of positions contributes the square of its rational difference with the position correction. The descending factorial and the power n+k lie in the numerator. " + SourceSentence,
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("sourceRHS", "The normalized nested sum", RHSDefinition(),
                "The complete chain sum is divided by the product of (n+i)! for 0<=i<m. Empty products and determinants have value one. " + SourceSentence,
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "Kurkov's three-parameter assertion", ClaimDefinition(),
                "OEIS A396563 FORMULA, approved revision 15, is unpaginated. " + SourceSentence + " The assertion quantifies over all n,k>=0 and m>=1. The source examples and programs include n=0 and k=0.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "The full identity", ClaimBody(),
                "The coefficient identity for rising factorials converts the first-kind minor into an elementary-coefficient corner. Determinant-one inverse Toeplitz matrices identify that corner with the complete-coefficient corner of a different size. The map sending j at position t to n-j+t identifies the nested tuples with increasing subsets. Factorial normalization and Cauchy–Binet give a signed moment determinant. Stirling inclusion–exclusion evaluates its entries; column reversal cancels its sign. This proves the displayed identity also when n=0 or k=0.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(ProblemSlugRef.Create("kurk396563"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, string title, Formula formula,
        string prose, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
            DescribeId.Create("a396563-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Owner + name), H(title), StatementSource.FromAuthor(Disp(formula)),
            provenance, Blocks(Paragraph(Text(prose))), role, openProblemResolutionClaim: resolution);

    private static Formula V(string name) => F.Id(name);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula At(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula Qualified(string owner, string name) =>
        Seq(Operatorname, Grp(Seq(V(owner), Dot, V(name))));
    private static Formula Nat() => Seq(Mathbb, Grp(V("N")));
    private static Formula Rat() => Seq(Mathbb, Grp(V("Q")));
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula CastQ(Formula value) => Parenthesized(Seq(value, Colon, Rat()));
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Lam(string name, Formula type, Formula body) =>
        Seq(LambdaLower, Sp, V(name), Colon, type, Sp, Mapsto, Sp, body);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(Parenthesized(a), b);
    private static Formula Val(Formula a) => Call("val", a);
    private static Formula J(Formula j, Formula t) => Val(At(Val(j), t));
    private static Formula Fact(Formula a) => At(Qualified("Nat", "factorial"), a);
    private static Formula SumFin(string name, Formula size, Formula body) =>
        Seq(new Formula.Subscript(Sum, Seq(V(name), Colon, Call("Fin", size))), Sp, Parenthesized(body));
    private static Formula ProdFin(string name, Formula size, Formula body) =>
        Seq(new Formula.Subscript(Prod, Seq(V(name), Colon, Call("Fin", size))), Sp, Parenthesized(body));
    private static Formula NKM(Formula body) => All("n", Nat(), All("k", Nat(), All("m", Nat(), body)));
    private static Formula ChainType(Formula n, Formula m) => Call("Chain", n, m);

    private static Formula BDefinition()
    {
        var n=V("n"); var k=V("k"); var m=V("m"); var i=V("i"); var j=V("j");
        var entry=CastQ(At(Qualified("Nat", "stirlingFirst"),
            Add(Add(n,m),Add(Val(i),D(1))), Add(n,Add(Val(j),D(1)))));
        return NKM(Eq(Call("B",n,k,m), At(Qualified("Matrix","det"),
            Lam("i",Call("Fin",k),Lam("j",Call("Fin",k),entry)))));
    }
    private static Formula TermDefinition()
    {
        var n=V("n"); var k=V("k"); var m=V("m"); var j=V("j");
        var t=V("t"); var q=V("q"); var p=V("p");
        var difference=Sub(Add(Sub(CastQ(J(j,q)),CastQ(J(j,p))),CastQ(Val(p))),CastQ(Val(q)));
        var pairProduct=ProdFin("q",m,
            Seq(new Formula.Subscript(Prod, Seq(p, Sp, InMacro, Sp,
                At(Qualified("Finset","Ioi"),q))), Sp, Parenthesized(Pow(difference,D(2)))));
        var index=Sub(Add(J(j,t),m),Add(Val(t),D(1)));
        var baseValue=CastQ(Add(Sub(n,J(j,t)),Add(Val(t),D(1))));
        var descending=CastQ(At(Qualified("Nat","descFactorial"),Add(n,Val(t)),J(j,t)));
        var factor=new Formula.Fraction(Mul(descending,Pow(baseValue,Add(n,k))),CastQ(Fact(index)));
        var body=Mul(Mul(Pow(CastQ(new Formula.Negate(D(1))),SumFin("t",m,J(j,t))),pairProduct),ProdFin("t",m,factor));
        return All("n",Nat(),All("m",Nat(),All("k",Nat(),All("j",ChainType(n,m),
            Eq(Call("sourceTerm",k,j),body)))));
    }
    private static Formula RHSDefinition()
    {
        var n=V("n"); var k=V("k"); var m=V("m"); var j=V("j"); var i=V("i");
        var sum=Seq(new Formula.Subscript(Sum,Seq(j,Colon,ChainType(n,m))),Sp,Parenthesized(Call("sourceTerm",k,j)));
        var denominator=ProdFin("i",m,CastQ(Fact(Add(n,Val(i)))));
        return NKM(Eq(Call("sourceRHS",n,k,m),new Formula.Fraction(sum,denominator)));
    }
    private static Formula ClaimBody() => NKM(Imp(Le(D(1),V("m")),
        Eq(Call("B",V("n"),V("k"),V("m")),Call("sourceRHS",V("n"),V("k"),V("m")))));
    private static Formula ClaimDefinition() => Eq(V("claim"), Parenthesized(ClaimBody()));
}
