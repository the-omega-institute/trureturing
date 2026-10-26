using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FactorialRatio;

internal sealed class OeisA276102BalaFifthIndexIntegralDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FactorialRatio/OeisA276102BalaFifthIndexIntegral.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Factorization/bala2016integerfactorials");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Bala A276102 integrality.", H("Bala A276102: integrality at every natural index"), Blocks(
            Node("a", All("n", N(), Eq(Call("a" ,V("n")), Div(Mul(Cast(App(Q("Nat", "factorial") ,Mul(D(6), V("n"))), R()), App(Q("Real", "Gamma") ,Add(Div(Cast(V("n"), R()), D(5)), D(1)))), Mul(Mul(Cast(App(Q("Nat", "factorial") ,Mul(D(3), V("n"))), R()), Cast(App(Q("Nat", "factorial") ,Mul(D(2), V("n"))), R())), App(Q("Real", "Gamma") ,Add(Div(Mul(D(6), Cast(V("n"), R())), D(5)), D(1))))))),
                "OEIS A276102, NAME (unpaginated): \"a(n) = (6*n)!*(n/5)!/((3*n)!*(2*n)!*(6*n/5)!).\" Bala, page 1: \"throughout these notes x! is shorthand for Γ(x + 1)\". Natural factorials are cast to the reals.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", Eq(Call("claim"), Parenthesized(ClaimBody())),
                "OEIS A276102, COMMENTS (unpaginated): \"This is only conjecturally an integer sequence.\" Bala, page 5: \"are also integral for n ≥ 0.\" Naturals include zero, and integrality means equality to the real cast of an integer.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", ClaimBody(),
                "Every natural index gives the real cast of an integer. Gamma recurrence and prime valuations prove the assertion for fifth indices, including zero.", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source), new OpenProblemResolutionClaim(ProblemSlugRef.Create("bfrac-fracfactorial"), ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, Formula formula, string prose, DescribeRole role, AssessedProvenance provenance, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create("bala-" + name.Replace('_', '-').ToLowerInvariant()), DeclarationHandle.Create(Prefix + name), H(name),
            StatementSource.FromAuthor(Disp(formula)), provenance, Blocks(Paragraph(Text(prose))), role, openProblemResolutionClaim: resolution);

    private static Formula V(string name) => F.Id(name);
    private static Formula N() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula R() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Q(string owner, string name) => Seq(Named(owner), Dot, Named(name));
    private static Formula App(Formula f, params Formula[] args) => args.Length == 0 ? f : new Formula.Apply(f, [.. args]);
    private static Formula Call(string name, params Formula[] args) => App(Named(name), args);
    private static Formula Parenthesized(Formula body) => Seq(Open, body, Close);
    private static Formula Cast(Formula body, Formula type) => Parenthesized(Seq(body, Colon, Sp, type));
    private static Formula All(string name, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Ex(string name, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Div(Formula a, Formula b) => new Formula.Fraction(a, b);

    private static Formula ClaimBody() => All("n", N(), Ex("z", new Formula.Integers(), Eq(Call("a", V("n")), Cast(V("z"), R()))));
}
