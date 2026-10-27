using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FactorialRatio;

internal sealed class BalaA361034ParityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FactorialRatio/BalaA361034Parity.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Factorization/bala2023quarticparity");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Bala's OEIS A361034 parity characterization.",
        H("OEIS A361034: parity of a quartic factorial quotient"), Blocks(
            Node("quotient_odd", SharedBody(),
                "For positive natural numbers C and j, when 8 j! C = (4j)! and the exponent of 2 in C is 3j - 3, the factorial quotient is an integer and is odd exactly when n + j is a power of two. The binary digit sum determines the exponent of 2 in the quotient.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("a", All("n", Nat(), Eq(Call("a", V("n")), Quotient(D(2,5,2,0), D(2)))),
                "OEIS A361034, NAME (unpaginated): \"a(n) = 2520*(4*n)!/(n!*(n+2)!^3).\" The index n is a natural number, including zero. Nat.div denotes natural-number division; the factorial denominator divides the numerator.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", Eq(Call("claim"), Parenthesized(ClaimBody())),
                "OEIS A361034, COMMENTS (unpaginated): \"Conjecture: a(n) is odd iff n = 2^k - 2 for some k >= 1.\" Both n and k range over the natural numbers. The lower bound on k makes the subtraction exact.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", ClaimBody(),
                "The factorial quotient is odd exactly at the stated indices. Its exponent of 2 is three times the binary digit sum of n + 2, less three; this vanishes exactly when n + 2 is a power of two.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)))));

    private static DocumentBlock Node(string name, Formula formula, string prose, DescribeRole role, AssessedProvenance provenance, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create("bala361034-" + name.Replace('_', '-')),
            DeclarationHandle.Create(Prefix + name), H(name), StatementSource.FromAuthor(Disp(formula)),
            provenance, Blocks(Paragraph(Text(prose))), role, openProblemResolutionClaim: resolution);

    private static Formula V(string name) => F.Id(name);
    private static Formula Nat() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Q(string owner, string name) => Seq(Named(owner), Dot, Named(name));
    private static Formula App(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula Call(string name, params Formula[] args) => args.Length == 0 ? Named(name) : App(Named(name), args);
    private static Formula Parenthesized(Formula body) => Seq(Open, body, Close);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Ex(string name, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), Nat(), body);
    private static Formula Eq(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Le(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Add(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Sub(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Mul(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Pow(Formula value, Formula exponent) => new Formula.Power(value, exponent);
    private static Formula And(Formula left, Formula right) => new Formula.Logic(left, FormulaLogicOperator.And, right);
    private static Formula IffBody(Formula left, Formula right) => new Formula.Logic(left, FormulaLogicOperator.Iff, right);
    private static Formula Fact(Formula value) => App(Q("Nat", "factorial"), value);
    private static Formula Quotient(Formula coefficient, Formula shift) => App(Q("Nat", "div"),
        Mul(coefficient, Fact(Mul(D(4), V("n")))),
        Mul(Fact(V("n")), Pow(Fact(Add(V("n"), shift)), D(3))));
    private static Formula ClaimBody() => All("n", Nat(), IffBody(Call("Odd", Call("a", V("n"))),
        Ex("k", And(Le(D(1), V("k")), Eq(V("n"), Sub(Pow(D(2), V("k")), D(2)))))));

    private static Formula SharedBody() => All("C", Nat(), All("j", Nat(), All("n", Nat(),
        new Formula.Logic(
            And(new Formula.Relation(D(0), FormulaRelationOperator.LessThan, V("C")),
                And(new Formula.Relation(D(0), FormulaRelationOperator.LessThan, V("j")),
                    And(Eq(Mul(Mul(D(8), Fact(V("j"))), V("C")), Fact(Mul(D(4), V("j")))),
                        Eq(App(Q("Nat", "factorization"), V("C"), D(2)), Sub(Mul(D(3), V("j")), D(3)))))),
            FormulaLogicOperator.Implies,
            IffBody(Call("Odd", Quotient(V("C"), V("j"))),
                Ex("k", Eq(Add(V("n"), V("j")), Pow(D(2), V("k")))))))));
}
