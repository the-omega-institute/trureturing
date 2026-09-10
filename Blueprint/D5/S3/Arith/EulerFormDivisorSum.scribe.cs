using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith;

internal sealed class EulerFormDivisorSumDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/EulerFormDivisorSum.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Words/oeis2026a388986");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every Euler-form number in A228058 satisfies the strict divisor-sum inequality of A388986.",
        H("Euler-form divisor sums"),
        Blocks(
            Paragraph(Text(
                "Let p be a prime congruent to one modulo four, let a be a natural number, "
                + "and let r be odd, greater than one, and coprime to p. Put N=p^(4a+1)r^2. "
                + "The two functions below sum actual divisors of N, including one.")),
            Node("unitarySum", "The unitary divisor sum", UnitaryFormula(),
                "A divisor d is unitary when d and N/d are coprime. The quotient is exact "
                + "on the divisor set. This definition also includes N itself.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("squarefreeSum", "The squarefree divisor sum", SquarefreeFormula(),
                "The sum ranges over divisors containing no square factor greater than one. "
                + "Its prime-support product is obtained from Mathlib's powerset identity.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("euler_form_lt", "The Euler-form inclusion", MainFormula(),
                "After dividing by positive N, the distinguished prime contributes at most "
                + "six fifths to each product. Every prime from r has exponent at least two. "
                + "A finite reciprocal-square product bound, with separate cases for whether "
                + "the support contains three and another prime, bounds the remaining sum "
                + "strictly below five thirds. Their product is strictly below two. "
                + "The hypothesis r>1 supplies a nonempty support; for r=1 and p=5 the "
                + "claimed inequality would fail.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a388986-euler-form-divisor-sum"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? claim = null) => Describe.Lean(
        DescribeId.Create("a388986-" + name.Replace('_', '-').ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
        provenance, Blocks(Paragraph(Text(prose))), role, claim);

    private static Formula UnitaryFormula() => Disp(Seq(
        Bound("N"), Call("unitarySum", F.Id("N")), Sp, Eq, Sp,
        DivisorSum(Seq(Call("gcd", F.Id("d"),
            new Formula.Fraction(F.Id("N"), F.Id("d"))), Sp, Eq, Sp, D(1)))));

    private static Formula SquarefreeFormula() => Disp(Seq(
        Bound("N"), Call("squarefreeSum", F.Id("N")), Sp, Eq, Sp,
        DivisorSum(Call("Squarefree", F.Id("d")))));

    private static Formula MainFormula() => Disp(Seq(
        Bound("p"), Bound("a"), Bound("r"), Call("prime", F.Id("p")),
        Sp, Land, Sp, new Formula.Modulo(F.Id("p"), D(4)), Sp, Eq, Sp, D(1),
        Sp, Land, Sp, Call("Odd", F.Id("r")),
        Sp, Land, Sp, D(1), Sp, Lt, Sp, F.Id("r"),
        Sp, Land, Sp, Call("gcd", F.Id("p"), F.Id("r")), Sp, Eq, Sp, D(1),
        Sp, Rightarrow, Sp, Add(Call("unitarySum", EulerNumber()),
            Call("squarefreeSum", EulerNumber())), Sp, Lt, Sp, Mul(D(2), EulerNumber())));

    private static Formula EulerNumber() =>
        Mul(Pow(F.Id("p"), Add(Mul(D(4), F.Id("a")), D(1))), Pow(F.Id("r"), D(2)));

    private static Formula DivisorSum(Formula predicate) => Seq(
        new Formula.Subscript(F.Sum, Seq(F.Id("d"), Sp, InMacro, Sp,
            Call("divisors", F.Id("N")), Comma, Sp, predicate)), Sp, F.Id("d"));

    private static Formula Bound(string name) => Seq(Forall, Sp, F.Id(name), Sp, InMacro, Sp,
        Mathbb, Grp(F.Id("N")), Comma, Sp);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. args]);
    private static Formula Pow(Formula a, Formula b) => Seq(Grp(a), Caret, Grp(b));
    private static Formula Add(Formula x, Formula y) =>
        new Formula.Binary(x, FormulaBinaryOperator.Add, y);
    private static Formula Mul(Formula x, Formula y) =>
        new Formula.Binary(x, FormulaBinaryOperator.Multiply, y);
}
