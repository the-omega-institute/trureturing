using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FactorialRatio;

internal sealed class OeisA347855BalaThirdIndexIntegralDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FactorialRatio/OeisA347855BalaThirdIndexIntegral.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Factorization/bala2021fractionalfactorial");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Bala A347855 integrality.", H("Bala A347855: integrality at every natural index"), Blocks(
            Node("a", All("n", Seq(Mathbb, Grp(F.Id("N"))), Eq(Call("a" ,V("n")), Mul(Div(Cast(App(Q("Nat", "factorial"), Mul(D(4), V("n"))), Seq(Mathbb, Grp(F.Id("R")))), Mul(Cast(App(Q("Nat", "factorial"), Mul(D(2), V("n"))), Seq(Mathbb, Grp(F.Id("R")))), Cast(App(Q("Nat", "factorial"), V("n")), Seq(Mathbb, Grp(F.Id("R")))))), Div(App(Q("OeisA347854BalaHalfIndexIntegral", "ffact"), Div(Cast(V("n"), Seq(Mathbb, Grp(F.Id("R")))), D(3))), App(Q("OeisA347854BalaHalfIndexIntegral", "ffact"), Div(Mul(D(4), Cast(V("n"), Seq(Mathbb, Grp(F.Id("R"))))), D(3))))))),
                "OEIS A347855, NAME (unpaginated): \"a(n) = (4*n)!/((2*n)!*(n)!) * (n/3)!/(4*n/3)!.\" Natural factorials are cast to the reals; fractional factorials use ffact.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", Eq(Call("claim"), Parenthesized(ClaimBody())),
                "OEIS A347855, COMMENTS (unpaginated): \"The sequence is conjectured to be integral.\" Integrality means that for every natural index, including zero, the value is the cast of an integer.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("progression", All("n", Seq(Mathbb, Grp(F.Id("N"))), Eq(Call("progression" ,V("n")), RangeProd(V("n"), Add(V("n"), Mul(D(3), Add(V("k"), D(1))))))),
                "The product of the n natural factors n+3(k+1), with k in Finset.range n.", DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("third_dvd", All("n", Seq(Mathbb, Grp(F.Id("N"))), Impl(Seq(Neg, Sp, Parenthesized(Dvd(D(3), V("n")))), Dvd(Mul(App(Q("Nat", "factorial"), Mul(D(2), V("n"))), Mul(App(Q("Nat", "factorial"), V("n")), Call("progression" ,V("n")))), App(Q("Nat", "factorial"), Mul(D(4), V("n")))))),
                "When three does not divide n, the product of (2n)!, n! and progression n divides (4n)!. The prime three contributes no valuation to progression n; other primes are controlled by counts of divisible progression terms.", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("result", ClaimBody(),
                "Every natural index has an integer value. Reduction to factorial quotients and comparison of prime valuations give an integer cast.", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source), new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a347855-bala-third-index-integrality"), ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, Formula formula, string prose, DescribeRole role, AssessedProvenance provenance, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create("bala-" + name.Replace('_', '-')), DeclarationHandle.Create(Prefix + name), H(name),
            StatementSource.FromAuthor(Disp(formula)), provenance, Blocks(Paragraph(Text(prose))), role, openProblemResolutionClaim: resolution);

    private static Formula V(string name) => F.Id(name);
    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Q(string owner, string name) => Seq(Named(owner), Dot, Named(name));
    private static Formula App(Formula f, params Formula[] args) => args.Length == 0 ? f : new Formula.Apply(f, [.. args]);
    private static Formula Call(string name, params Formula[] args) => App(Named(name), args);
    private static Formula Parenthesized(Formula body) => Seq(Open, body, Close);
    private static Formula Cast(Formula body, Formula type) => Parenthesized(Seq(body, Colon, Sp, type));
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Ex(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);

    private static Formula Dvd(Formula a, Formula b) => Seq(a, Sp, Mid, Sp, b);
    private static Formula Impl(Formula a, Formula b) => Seq(Parenthesized(a), Sp, Implies, Sp, Parenthesized(b));
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);

    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Div(Formula a, Formula b) => new Formula.Fraction(a, b);


    private static Formula RangeProd(Formula size, Formula body) =>
        Seq(new Formula.Subscript(Prod, Seq(V("k"), Sp, InMacro, Sp, App(Q("Finset", "range"), size))), Sp, Parenthesized(body));

    private static Formula ClaimBody() => All("n", Seq(Mathbb, Grp(F.Id("N"))), Ex("z", new Formula.Integers(), Eq(Cast(V("z"), Seq(Mathbb, Grp(F.Id("R")))), Call("a" ,V("n")))));
}
