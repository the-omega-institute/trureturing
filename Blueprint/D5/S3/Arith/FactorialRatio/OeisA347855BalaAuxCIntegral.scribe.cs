using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FactorialRatio;

internal sealed class OeisA347855BalaAuxCIntegralDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FactorialRatio/OeisA347855BalaAuxCIntegral.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Factorization/bala2021fractionalfactorial");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Bala A347855 integrality.", H("Bala A347855: integrality at every natural index"), Blocks(
            Node("c", All("n", Seq(Mathbb, Grp(F.Id("N"))), Eq(Call("c" ,V("n")), Div(Cast(App(Q("Nat", "factorial"), Add(Mul(D(1,2), V("n")), D(8))), Seq(Mathbb, Grp(F.Id("Q")))), Mul(Cast(App(Q("Nat", "factorial"), Add(Mul(D(6), V("n")), D(4))), Seq(Mathbb, Grp(F.Id("Q")))), Mul(Cast(App(Q("Nat", "factorial"), Add(Mul(D(3), V("n")), D(1))), Seq(Mathbb, Grp(F.Id("Q")))), RangeProd(Add(Mul(D(3), V("n")), D(3)), Cast(Add(Add(Mul(D(3), V("n")), Mul(D(3), V("k"))), D(2)), Seq(Mathbb, Grp(F.Id("Q")))))))))),
                "OEIS A347855, FORMULA (unpaginated): \"a(3*n+2) = 3^(3*n+2) * c(n), where c(n) = (12*n+8)!/( (6*n+4)!*(3*n+1)!*Product_{k = 0..3*n+2} (3*n+3*k+2) ) appears to be integral. (End)\" The product includes both endpoints given by the source; Finset.range uses an exclusive upper endpoint.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", Eq(Call("claim"), Parenthesized(ClaimBody())),
                "OEIS A347855, FORMULA (unpaginated): \"a(3*n+2) = 3^(3*n+2) * c(n), where c(n) = (12*n+8)!/( (6*n+4)!*(3*n+1)!*Product_{k = 0..3*n+2} (3*n+3*k+2) ) appears to be integral. (End)\" Integrality means that for every natural index, including zero, the value is the cast of an integer.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", ClaimBody(),
                "Every natural index has an integer value. The Gamma recurrence and the divisible factorial denominator give an integer cast.", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source), new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a347855-bala-aux-c-integrality"), ResolutionKind.Proved)))));

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



    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);

    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Div(Formula a, Formula b) => new Formula.Fraction(a, b);


    private static Formula RangeProd(Formula size, Formula body) =>
        Seq(new Formula.Subscript(Prod, Seq(V("k"), Sp, InMacro, Sp, App(Q("Finset", "range"), size))), Sp, Parenthesized(body));

    private static Formula ClaimBody() => All("n", Seq(Mathbb, Grp(F.Id("N"))), Ex("z", new Formula.Integers(), Eq(Cast(V("z"), Seq(Mathbb, Grp(F.Id("Q")))), Call("c" ,V("n")))));
}
