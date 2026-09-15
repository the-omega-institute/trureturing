using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith;

internal sealed class SchulteLiouvilleCubeMobiusDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/SchulteLiouvilleCubeMobius.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Arith/schulte2018a299406");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Schulte's A299406 coefficients equal the Liouville function times A210826.",
        H("Schulte's Liouville and Cube-Mobius Identity"),
        Blocks(
            Paragraph(Text("N denotes the natural numbers including zero, Z the integers, and "
                + "ArithmeticFunction(Z) the integer-valued functions on N that vanish at zero. "
                + "The indices n and k are natural numbers, and f is such an arithmetic function. "
                + "The arithmetic function zeta is one on positive inputs and zero at zero; "
                + "mu is the Mobius function; intCast(zeta) is its integer-valued cast, the "
                + "coercion from ArithmeticFunction(N) to ArithmeticFunction(Z) that the "
                + "convolutions with the integer-valued mu require. Omega counts prime "
                + "factors with multiplicity, and "
                + "lambda denotes Mathlib's liouville, A008836: at a positive index it is minus "
                + "one raised to Omega of that index. A and B denote A299406 and A210826. "
                + "The binary star is Dirichlet convolution, while the centered dot is integer "
                + "multiplication of values. Nat.floorRoot divides each prime-factor exponent "
                + "by k using natural-number division and returns zero when k or n is zero; "
                + "it is the root for the divisibility order. The function liftPow keeps the "
                + "value of f at this root exactly when its k-th power equals n. For positive k, "
                + "its Dirichlet series is obtained by replacing the series variable s by k*s. "
                + "Reading the Dirichlet generating function coefficientwise sends zeta(6s) "
                + "to liftPow(6,zeta) and the reciprocals of zeta(2s) and zeta(3s) to "
                + "liftPow(2,mu) and liftPow(3,mu). In the Lambert series, x is a formal "
                + "variable: the sum of B(d) over positive divisors d of n equals the cube "
                + "indicator, so Mobius inversion gives B as mu convolved with that indicator. "
                + "Only the A299406 formula a(n) = A008836(n) * A210826(n) is asserted here, "
                + "under these coefficient readings. Analytic convergence and other OEIS "
                + "assertions are outside the claim. The positive-index hypothesis follows "
                + "the offset one of A299406.")),
            Node("liftPow", "The exact power lift", LiftFormula(),
                "The two defining clauses retain f at the factorization root on exact powers "
                + "and give zero otherwise. They also describe the total definition when k is "
                + "zero; the coefficient interpretation uses only positive k. Each displayed "
                + "zero in a value equality is an integer.",
                DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("A", "The A299406 coefficient function", AFormula(),
                "The four convolution factors encode zeta(s) zeta(6s) divided by "
                + "zeta(2s) zeta(3s). The zeta factors here are integer-valued, matching "
                + "the natural-to-integer coercions in the Lean definition.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("B", "The Lambert-series coefficient function", BFormula(),
                "The function liftPow(3,zeta) is one on positive cubes and zero elsewhere. "
                + "Convolution with mu inverts the positive-divisor sum in the Lambert "
                + "series defining A210826.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "Schulte's product formula", ResultFormula(),
                "Every convolution factor is multiplicative. On a prime power with exponent "
                + "e, both sides have values 1, 1, 0, -1, -1, 0 as e runs through the six "
                + "residue classes. Equality on all prime powers therefore gives equality "
                + "at every positive natural index.",
                DescribeRole.Theorem, AssessedProvenance.FromLiterature(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a299406-schulte-liouville-cube-mobius"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance, OpenProblemResolutionClaim? claim = null) =>
        Describe.Lean(DescribeId.Create("a299406-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
            provenance, Blocks(Paragraph(Text(prose))), role, claim);

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Integers() => Seq(Mathbb, Grp(F.Id("Z")));
    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula IntZeta() => Call(Named("intCast"), Named(Zeta));
    private static Formula Named(Formula symbol) => Seq(Operatorname, Grp(symbol));
    private static Formula Call(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Equal(Formula left, Formula right) => Seq(left, Sp, Eq, Sp, right);
    private static Formula Convolve(Formula left, Formula right) => Seq(left, Sp, Star, Sp, right);
    private static Formula Bound(Formula variable, Formula domain) =>
        Seq(Forall, Sp, variable, Sp, InMacro, Sp, domain, Comma, Sp);
    private static Formula Implication(Formula hypothesis, Formula conclusion) =>
        Seq(Parenthesized(hypothesis), Sp, Implies, Sp, Parenthesized(conclusion));

    private static Formula LiftFormula()
    {
        Formula k = F.Id("k"), f = F.Id("f"), n = F.Id("n");
        Formula root = Call(Named("floorRoot"), k, n);
        Formula power = new Formula.Power(root, k);
        Formula value = Call(Call(Named("liftPow"), k, f), n);
        Formula exact = Implication(Equal(power, n), Equal(value, Call(f, root)));
        Formula other = Implication(Seq(power, Sp, Neq, Sp, n), Equal(value, D(0)));
        return Disp(Seq(Bound(k, Naturals()), Bound(f, Call(Named("ArithmeticFunction"), Integers())),
            Bound(n, Naturals()), Parenthesized(exact), Sp, Land, Sp, Parenthesized(other)));
    }

    private static Formula AFormula() => Disp(Equal(Named("A"),
        Convolve(Parenthesized(Convolve(Parenthesized(Convolve(IntZeta(),
            Call(Named("liftPow"), D(6), IntZeta()))),
            Call(Named("liftPow"), D(2), Named(Mu)))),
            Call(Named("liftPow"), D(3), Named(Mu)))));

    private static Formula BFormula() => Disp(Equal(Named("B"),
        Convolve(Named(Mu), Call(Named("liftPow"), D(3), IntZeta()))));

    private static Formula ResultFormula()
    {
        Formula n = F.Id("n");
        return Disp(Seq(Bound(n, Naturals()),
            Implication(Seq(D(0), Sp, Lt, Sp, n),
                Equal(Call(Named("A"), n), new Formula.Binary(Call(Named(LambdaLower), n),
                    FormulaBinaryOperator.Multiply, Call(Named("B"), n))))));
    }
}
