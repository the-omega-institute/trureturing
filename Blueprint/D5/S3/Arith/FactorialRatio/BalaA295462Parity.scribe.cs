using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FactorialRatio;

internal sealed class BalaA295462ParityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FactorialRatio/BalaA295462Parity.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Factorization/bala2026a295462");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Bala A295462 parity.", H("Bala A295462: binary spacing and oddness"), Blocks(
            Node("a", All("n", Nat(), Eq(Call("a", V("n")),
                new Formula.Fraction(
                    Mul(FactorialCast(Mul(D(1,5), V("n"))), FactorialCast(Mul(D(2), V("n")))),
                    Mul(Mul(FactorialCast(Mul(D(1,0), V("n"))), FactorialCast(Mul(D(6), V("n")))), FactorialCast(V("n")))))),
                "OEIS A295462, NAME (unpaginated): \"a(n) = (15*n)!*(2*n)!/((10*n)!*(6*n)!*n!).\" Each natural factorial is cast to the rationals and division is exact.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("spacedBits", All("n", Nat(), Eq(Call("spacedBits", V("n")), Parenthesized(
                All("i", Nat(), All("j", Nat(), Impl(Lt(V("i"), V("j")),
                    Impl(Eq(App(Q("Nat", "testBit"), V("n"), V("i")), Named("true")),
                        Impl(Eq(App(Q("Nat", "testBit"), V("n"), V("j")), Named("true")),
                            Le(Add(V("i"), D(4)), V("j")))))))))),
                "OEIS A048718, COMMENTS (unpaginated): \"Max. 1 one-bit occur in each range of four bits.\" Position i has weight 2^i. Every pair of occupied positions i < j has distance at least four; zero has empty support.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", Eq(Call("claim"), Parenthesized(ClaimBody())),
                "OEIS A295462, REFERENCES (%D, unpaginated): \"Conjecture: a(n) is odd iff the 1 bits in the binary expansion of n are separated by at least three 0's, that is, iff n belongs to A048718.\" The index n ranges over all natural numbers, including zero; a natural m realizes the rational quotient and Odd tests m.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", ClaimBody(),
                "Every quotient is a natural integer, and it is odd exactly when occupied binary positions are separated by at least four. The binary prime valuation is a sum of nonnegative floor defects. Spacing makes all defects zero. The first shorter gap forces one defect to equal one; a strict geometric bound controls the lower occupied positions.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source), new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("bala295462"), ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, Formula formula, string prose, DescribeRole role, AssessedProvenance provenance, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create("bala-parity-" + name.Replace("spacedBits", "spaced-bits")), DeclarationHandle.Create(Prefix + name), H(name),
            StatementSource.FromAuthor(Disp(formula)), provenance, Blocks(Paragraph(Text(prose))), role, openProblemResolutionClaim: resolution);

    private static Formula V(string name) => F.Id(name);
    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Q(string owner, string name) => Seq(Named(owner), Dot, Named(name));
    private static Formula App(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula Call(string name, params Formula[] args) => args.Length == 0 ? Named(name) : App(Named(name), args);
    private static Formula Parenthesized(Formula body) => Seq(Open, body, Close);
    private static Formula Nat() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Rat() => Seq(Mathbb, Grp(F.Id("Q")));
    private static Formula Cast(Formula value) => Parenthesized(Seq(value, Colon, Sp, Rat()));
    private static Formula FactorialCast(Formula n) => Cast(App(Q("Nat", "factorial"), n));
    private static Formula All(string name, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Ex(string name, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Impl(Formula a, Formula b) => Seq(Parenthesized(a), Sp, Implies, Sp, Parenthesized(b));
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula ClaimBody() => All("n", Nat(), Ex("m", Nat(),
        Seq(Parenthesized(Eq(Call("a", V("n")), Cast(V("m")))), Sp, Land, Sp,
            Parenthesized(Seq(Call("Odd", V("m")), Sp, Iff, Sp, Call("spacedBits", V("n")))))));
}
