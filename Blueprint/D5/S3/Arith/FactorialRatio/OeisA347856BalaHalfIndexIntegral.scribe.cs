using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FactorialRatio;

internal sealed class OeisA347856BalaHalfIndexIntegralDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FactorialRatio/OeisA347856BalaHalfIndexIntegral.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Factorization/bala2021fractionalfactorial");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Bala A347856 integrality.", H("Bala A347856: integrality at every natural index"), Blocks(
            Node("a", All("n", Seq(Mathbb, Grp(F.Id("N"))), Eq(Call("a" ,V("n")), Mul(Div(Cast(App(Q("Nat", "factorial"), Mul(D(6), V("n"))), Seq(Mathbb, Grp(F.Id("R")))), Mul(Cast(App(Q("Nat", "factorial"), Mul(D(4), V("n"))), Seq(Mathbb, Grp(F.Id("R")))), Cast(App(Q("Nat", "factorial"), V("n")), Seq(Mathbb, Grp(F.Id("R")))))), Div(App(Q("OeisA347854BalaHalfIndexIntegral", "ffact"), Div(Cast(V("n"), Seq(Mathbb, Grp(F.Id("R")))), D(2))), App(Q("OeisA347854BalaHalfIndexIntegral", "ffact"), Div(Mul(D(3), Cast(V("n"), Seq(Mathbb, Grp(F.Id("R"))))), D(2))))))),
                "OEIS A347856, NAME (unpaginated): \"a(n) = (6*n)!/((4*n)!*n!) * (n/2)!/(3*n/2)!.\" Natural factorials are cast to the reals; fractional factorials use ffact.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", Eq(Call("claim"), Parenthesized(ClaimBody())),
                "OEIS A347856, COMMENTS (unpaginated): \"The sequence is conjectured to be integral.\" Integrality means that for every natural index, including zero, the value is the cast of an integer.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", ClaimBody(),
                "Every natural index has an integer value. Reduction to factorial quotients and comparison of prime valuations give an integer cast.", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source), new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a347856-bala-half-index-integrality"), ResolutionKind.Proved)))));

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





    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Div(Formula a, Formula b) => new Formula.Fraction(a, b);




    private static Formula ClaimBody() => All("n", Seq(Mathbb, Grp(F.Id("N"))), Ex("z", new Formula.Integers(), Eq(Cast(V("z"), Seq(Mathbb, Grp(F.Id("R")))), Call("a" ,V("n")))));
}
