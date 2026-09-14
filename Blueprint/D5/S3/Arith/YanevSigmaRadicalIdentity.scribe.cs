using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith;

internal sealed class YanevSigmaRadicalIdentityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/YanevSigmaRadicalIdentity.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Arith/yanev2017a023887");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Yanev's identity expresses every positive divisor-power sum through ordinary divisor sums and the radical.",
        H("Yanev's Sigma-Radical Identity"),
        Blocks(
            Paragraph(Text("All variables take values in the natural numbers N. "
                + "The named operator primeRadical is the frozen primeRadical of "
                + "D5/S1/Deficit/AlmostAdditivity (A007947), the product of the distinct "
                + "prime divisors, with empty product one. The notation sigma(k,x) denotes "
                + "the sum of the k-th powers of the positive divisors of x, and is zero "
                + "at x = 0. Powers, products and inequalities are in N, "
                + "and m - 1 is truncated natural subtraction.")),
            Node("result", "The general divisor-power identity", ResultFormula(),
                "For every n > 0 and m > 0, the displayed equation is the multiplied-out "
                + "form of Yanev's conjecture in A023887, using the frozen primeRadical "
                + "of D5/S1/Deficit/AlmostAdditivity (A007947), rendered as the named "
                + "operator primeRadical. Both sides are positive: the "
                + "radical is positive and each divisor sum includes the divisor one. "
                + "In particular sigma(1,primeRadical(n)^(m-1)) is positive, so division recovers "
                + "the stated quotient, with exact natural-number division as well. "
                + "Sela Fried (2025, Theorem 3) proved the m = 2 case on A001157; the "
                + "general-m statement is the claim settled here. For prime powers, "
                + "the equation follows from geometric-sum multiplication identities. "
                + "Coprime multiplicativity of the radical and divisor sums then "
                + "extends it to every positive natural number.", DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a023887-yanev-sigma-radical-identity"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role, OpenProblemResolutionClaim? claim = null) =>
        Describe.Lean(DescribeId.Create("a023887-" + name),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
            AssessedProvenance.FromLiterature(Source), Blocks(Paragraph(Text(prose))), role, claim);

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Named(name), [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Equal(Formula left, Formula right) => Seq(left, Sp, Eq, Sp, right);
    private static Formula Less(Formula left, Formula right) => Seq(left, Sp, Lt, Sp, right);
    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Mul(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Power(Formula value, Formula exponent) => new Formula.Power(value, exponent);
    private static Formula Bound(string name) =>
        Seq(Forall, Sp, F.Id(name), Colon, Sp, Naturals(), Comma, Sp);
    private static Formula Implication(Formula premise, Formula conclusion) =>
        Seq(Parenthesized(premise), Sp, Implies, Sp, conclusion);

    private static Formula ResultFormula()
    {
        Formula n = F.Id("n");
        Formula m = F.Id("m");
        Formula radicalPower = Power(Call("primeRadical", n), Parenthesized(Subtract(m, D(1))));
        Formula left = Mul(Call("sigma", m, n), Call("sigma", D(1), radicalPower));
        Formula right = Call("sigma", D(1), Mul(Power(n, m), radicalPower));
        return Disp(Seq(Bound("n"), Bound("m"),
            Implication(Less(D(0), n), Implication(Less(D(0), m), Equal(left, right)))));
    }
}
