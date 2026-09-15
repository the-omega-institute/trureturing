using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith;

internal sealed class CloitreFibFourThreeAdicValuationSigmaDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/CloitreFibFourThreeAdicValuationSigma.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Arith/cloitre2002a074724");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The highest power of three dividing F(4n) satisfies the Marcus and Bala formulas.",
        H("Cloitre's Fibonacci Three-Adic Valuation and Divisor Sum"),
        Blocks(
            Paragraph(Text("All variables and values lie in the natural numbers N, and n is the index. "
                + "F denotes Nat.fib, v_3 denotes padicValNat 3, and sigma_1 (also written sigma) "
                + "denotes ArithmeticFunction.sigma 1, the sum of positive divisors. The function a "
                + "is A074724 as defined below. Powers and products are natural-number operations; "
                + "each displayed subtraction is truncated natural-number subtraction.")),
            Node("a", "The power of three in F(4n)", DefinitionFormula(),
                "The exponent is the 3-adic valuation of F(4n). For a positive index, this defines "
                + "the highest power of three dividing that Fibonacci number. At zero, the total "
                + "Lean definition uses padicValNat 3 0 = 0 and therefore gives a(0) = 1; the "
                + "theorem below concerns positive indices.", DescribeRole.Definition,
                AssessedProvenance.FromLiterature(Source)),
            Node("result", "The valuation and divisor-sum formulas", ResultFormula(),
                "For n > 0, A051064(n) = v_3(3n) = v_3(n) + 1. The valuation formula follows "
                + "from the rank-12 criterion for divisibility of F(k) by nine and induction "
                + "using the Fibonacci tripling identity. Bala's formula is stated with the "
                + "denominator multiplied out in N. Writing n = 3^e m with 3 not dividing m "
                + "gives sigma_1(3n) - 3 sigma_1(n) = sigma_1(m) > 0; positivity of the "
                + "denominator is proved inside. The separate remark 'Equivalently, a(n) = "
                + "A088838(n) - A074724(n)' is not part of the settled claim.",
                DescribeRole.Theorem, AssessedProvenance.FromLiterature(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a074724-cloitre-fib-four-three-adic-valuation-sigma"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance, OpenProblemResolutionClaim? claim = null) =>
        Describe.Lean(DescribeId.Create("a074724-" + name),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
            provenance, Blocks(Paragraph(Text(prose))), role, claim);

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, Formula argument) =>
        new Formula.Apply(Named(name), [argument]);
    private static Formula Valuation(Formula argument) =>
        new Formula.Apply(new Formula.Subscript(Named("v"), D(3)), [argument]);
    private static Formula SigmaOne(Formula argument) =>
        new Formula.Apply(new Formula.Subscript(Seq(Operatorname, Grp(SigmaLower)), D(1)), [argument]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Equal(Formula left, Formula right) => Seq(left, Sp, Eq, Sp, right);
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Sub(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Mul(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Power(Formula value, Formula exponent) => new Formula.Power(value, exponent);
    private static Formula Bound(string name) =>
        Seq(Forall, Sp, F.Id(name), Colon, Sp, Naturals(), Comma, Sp);
    private static Formula Conjunction(Formula first, Formula second) =>
        Seq(Parenthesized(first), Sp, Land, Sp, Parenthesized(second));

    private static Formula DefinitionFormula()
    {
        Formula n = F.Id("n");
        return Disp(Seq(Bound("n"),
            Equal(Call("a", n), Power(D(3), Valuation(Call("F", Mul(D(4), n)))))));
    }

    private static Formula ResultFormula()
    {
        Formula n = F.Id("n");
        Formula first = Equal(Call("a", n),
            Power(D(3), Parenthesized(Add(Valuation(n), D(1)))));
        Formula denominator = Sub(SigmaOne(Mul(D(3), n)), Mul(D(3), SigmaOne(n)));
        Formula second = Equal(Mul(Call("a", n), Parenthesized(denominator)),
            Sub(SigmaOne(Mul(D(3), n)), SigmaOne(n)));
        return Disp(Seq(Bound("n"), Parenthesized(Seq(D(0), Sp, Lt, Sp, n)),
            Sp, Implies, Sp, Parenthesized(Conjunction(first, second))));
    }
}
