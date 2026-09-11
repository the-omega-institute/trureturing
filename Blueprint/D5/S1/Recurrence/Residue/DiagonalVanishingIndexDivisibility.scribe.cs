using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Residue;

internal sealed class DiagonalVanishingIndexDivisibilityDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S1/Recurrence/Residue/DiagonalVanishingIndexDivisibility.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/ArithSums/hanna2016diagonalindex");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Normalized vanishing diagonals inherit index-power divisibility from their exponents.",
        H("Index Divisibility for Vanishing Diagonals"),
        Blocks(
            Paragraph(Text("The note hanna2016diagonalindex quotes Hanna's A266489, A300732, "
                + "A300733, A292394, and A300734. The normalized family has constant and "
                + "linear coefficients one and vanishing diagonals in degrees n>1. The NAMEs "
                + "of A300732 and A300733 print n>=1, which contradicts their published "
                + "linear coefficient one. Their instances below use the consistent n>1 "
                + "interpretation; the literal quotations remain in the note.")),
            Paragraph(Text("The function e maps natural numbers to natural numbers. "
                + "Indices n, m, j, depths d, and the divisibility exponent k are natural. "
                + "Write A(e) for generatingSeries(e), P(e,d) for the integer-series "
                + "approximation, and frozen(p,n) for NegativePowerDiagonalModPrime.a(p,n). "
                + "All series have integer coefficients. The operator intCast embeds a "
                + "natural number in the integers. Divisibility in the exponent hypothesis "
                + "is natural divisibility; divisibility of coefficients is integer divisibility.")),
            Paragraph(Text("The operators coeff, mk, subst, and invOfUnit are the Lean "
                + "power-series operations. For a normalized series, invOfUnit(A,1) is "
                + "its formal inverse, so subst(A,X*invOfUnit(A,1)^e(n)) means "
                + "A(x/A(x)^e(n)). In the engine identity U is a unit, val forgets its "
                + "unit structure, and N is an arbitrary integer, including negative values. "
                + "Subtraction in a coefficient index is natural subtraction; subtraction "
                + "from N is integer subtraction.")),
            Node("a", "The triangular coefficient construction", CoefficientDefinition(),
                "The update fixes degrees zero and one at one. At every higher degree it "
                + "negates the sum over smaller outer degrees. The degree-zero summand "
                + "vanishes, and every positive outer degree leaves a strictly smaller "
                + "degree in the inverse power. Each update therefore improves agreement "
                + "by one degree, making the indicated coefficients stable.", DescribeRole.Definition),
            Node("generatingSeries", "The generating series",
                Disp(Seq(Bound("e", ExponentType()),
                    Equal(A(), Call("mk", Lambda("n", Call("a", E(), N())))))),
                "The stabilized integer coefficients define A(e).", DescribeRole.Definition),
            Node("generating_equation", "The normalized vanishing-diagonal equation",
                Disp(Seq(Bound("e", ExponentType()),
                    Conjunction(Equal(Coefficient(D(0), A()), D(1)),
                        Conjunction(Equal(Coefficient(D(1), A()), D(1)), Equation(A()))))),
                "Expanding the substitution through outer degree n gives a(e,n) plus "
                + "the finite sum used in the update. The fixed-point identity thus proves "
                + "the displayed functional equation, with both normalization conditions."),
            Node("generating_unique", "Uniqueness", UniqueFormula(),
                "The normalized equation is equivalent to the triangular fixed-point "
                + "condition. The inverse-difference identity preserves coefficient "
                + "agreement, and the update increases its degree. Induction identifies "
                + "every normalized solution B with A(e)."),
            Node("power_coefficient_identity", "The integer-power engine", EngineFormula(),
                "Apply the formal derivative to integer powers of a unit. Multiplying "
                + "by U handles the successor step; cancellation by the same unit handles "
                + "the predecessor step. Extracting degree j-1 gives the identity for "
                + "every integer N. In particular, N divides j times the coefficient."),
            Node("index_power_divisibility", "The general index-power theorem", GeneralFormula(),
                "Strong induction reduces the result to each smaller-degree summand. "
                + "For each prime p, put alpha=v_p(n). If v_p(m)<alpha, then "
                + "v_p(n-m)=v_p(m). The engine applied to the inverse series with exponent "
                + "e(n)*m forces its coefficient to contain p^(k*alpha). If "
                + "v_p(m)>=alpha, the induction hypothesis supplies that factor in "
                + "a(e,m). Prime factorization assembles these factors into n^k, and "
                + "divisibility survives the finite sum and its negation."),
            Node("hanna_conjecture_a300732", "A300732: index divisibility",
                InstanceFormula(Mul(D(2), F.Id("m")), false),
                "Use e(m)=2*m and k=1 in the normalized family. The interpretation "
                + "of the source's degree-one boundary is stated above.",
                DescribeRole.Theorem, AssessedProvenance.FromLiterature(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a300732-diagonal-index-divisibility"),
                    ResolutionKind.Proved)),
            Node("hanna_conjecture_a300733", "A300733: index divisibility",
                InstanceFormula(Mul(D(3), F.Id("m")), false),
                "Use e(m)=3*m and k=1 in the normalized family. The interpretation "
                + "of the source's degree-one boundary is stated above.",
                DescribeRole.Theorem, AssessedProvenance.FromLiterature(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a300733-diagonal-index-divisibility"),
                    ResolutionKind.Proved)),
            Node("hanna_conjecture_a292394", "A292394: square-index divisibility",
                InstanceFormula(Power(F.Id("m"), D(2)), true),
                "Use e(m)=m^2 and k=2. The exponent-divisibility hypothesis is reflexive.",
                DescribeRole.Theorem, AssessedProvenance.FromLiterature(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a292394-diagonal-index-divisibility"),
                    ResolutionKind.Proved)),
            Node("hanna_conjecture_a300734", "A300734: square-index divisibility",
                InstanceFormula(Mul(D(2), Power(F.Id("m"), D(2))), true),
                "Use e(m)=2*m^2 and k=2. Every square m^2 divides this exponent.",
                DescribeRole.Theorem, AssessedProvenance.FromLiterature(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a300734-diagonal-index-divisibility"),
                    ResolutionKind.Proved)),
            Node("agreement_a266489", "Agreement with the frozen A266489 object",
                Disp(Seq(Bound("n", Naturals()), Equal(
                    Call("a", Lambda("m", F.Id("m")), N()), Call("frozen", D(2), N())))),
                "For p=2 and n>1, the frozen exponent (p-1)*(n-1)+1 equals n. "
                + "NegativePowerDiagonalModPrime.generating_unique identifies the two "
                + "normalized series. Coefficient extraction gives agreement at every degree."),
            Node("hanna_conjecture_a266489", "A266489: clause C1 on the frozen object",
                Disp(Seq(Bound("n", Naturals()), Implication(PositiveIndex(),
                    Divides(Call("intCast", N()), Call("frozen", D(2), N()))))),
                "The general theorem with e(m)=m and k=1 gives index divisibility. "
                + "The agreement lemma transfers it to the frozen coefficient function, "
                + "proving clause C1 on that existing object.",
                DescribeRole.Theorem, AssessedProvenance.FromLiterature(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a266489-diagonal-index-divisibility"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role = DescribeRole.Theorem, AssessedProvenance? provenance = null,
        OpenProblemResolutionClaim? claim = null) =>
        Describe.Lean(DescribeId.Create("diagonal-index-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
            provenance ?? AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role, claim);

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Integers() => Seq(Mathbb, Grp(F.Id("Z")));
    private static Formula ExponentType() => Seq(Naturals(), Sp, Longrightarrow, Sp, Naturals());
    private static Formula E() => F.Id("e");
    private static Formula N() => F.Id("n");
    private static Formula A() => Call("A", E());
    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Named(name), [.. arguments]);
    private static Formula Eval(Formula function, Formula argument) =>
        new Formula.Apply(function, [argument]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Equal(Formula left, Formula right) => Seq(left, Sp, Eq, Sp, right);
    private static Formula Divides(Formula left, Formula right) => Seq(left, Sp, Mid, Sp, right);
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Mul(Formula left, Formula right) =>
        new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Multiply, Parenthesized(right));
    private static Formula Power(Formula value, Formula exponent) =>
        new Formula.Power(Parenthesized(value), exponent);
    private static Formula Bound(string name, Formula type) =>
        Seq(Forall, Sp, F.Id(name), Colon, Sp, type, Comma, Sp);
    private static Formula Lambda(string name, Formula body) =>
        Parenthesized(Seq(F.Id(name), Colon, Sp, Naturals(), Sp, Mapsto, Sp, body));
    private static Formula Implication(Formula premise, Formula conclusion) =>
        Seq(Parenthesized(premise), Sp, Implies, Sp, Parenthesized(conclusion));
    private static Formula Conjunction(Formula left, Formula right) =>
        Seq(Parenthesized(left), Sp, Land, Sp, Parenthesized(right));
    private static Formula Coefficient(Formula n, Formula f) => Call("coeff", n, f);
    private static Formula Equation(Formula f) => Seq(Bound("n", Naturals()),
        Implication(Seq(D(1), Sp, Lt, Sp, N()), Equal(Coefficient(N(),
            Call("subst", f, Mul(F.Id("X"),
                Power(Call("invOfUnit", f, D(1)), Eval(E(), N()))))), D(0))));
    private static Formula PositiveIndex() => Seq(D(1), Sp, Le, Sp, N());
    private static Formula InstanceFormula(Formula exponent, bool square) => Disp(Seq(
        Bound("n", Naturals()), Implication(PositiveIndex(), Divides(
            square ? Power(Call("intCast", N()), D(2)) : Call("intCast", N()),
            Call("a", Lambda("m", exponent), N())))));

    private static Formula CoefficientDefinition()
    {
        var d = F.Id("d");
        var j = F.Id("j");
        var approximation = Call("P", E(), d);
        var summand = Mul(Coefficient(j, approximation), Coefficient(Subtract(N(), j),
            Power(Call("invOfUnit", approximation, D(1)), Mul(Eval(E(), N()), j))));
        var sum = Seq(new Formula.Subscript(F.Sum,
            Seq(j, Sp, InMacro, Sp, Call("range", N()))), Sp, Parenthesized(summand));
        var next = Seq(Named("if"), Sp, Parenthesized(Seq(N(), Sp, Le, Sp, D(1))),
            Sp, Named("then"), Sp, D(1), Sp, Named("else"), Sp, Minus, Parenthesized(sum));
        return Disp(new Formula.Aligned([
            Seq(Bound("e", ExponentType()), Equal(Call("P", E(), D(0)), D(1))),
            Seq(Bound("e", ExponentType()), Bound("d", Naturals()),
                Equal(Call("P", E(), Add(d, D(1))), Call("mk", Lambda("n", next)))),
            Seq(Bound("e", ExponentType()), Bound("n", Naturals()),
                Equal(Call("a", E(), N()), Coefficient(N(), Call("P", E(), Add(N(), D(1))))))
        ]));
    }

    private static Formula UniqueFormula()
    {
        var b = F.Id("B");
        return Disp(Seq(Bound("e", ExponentType()), Bound("B", Call("PowerSeries", Integers())),
            Implication(Equal(Coefficient(D(0), b), D(1)),
                Implication(Equal(Coefficient(D(1), b), D(1)),
                    Implication(Equation(b), Equal(b, A()))))));
    }

    private static Formula EngineFormula()
    {
        var u = F.Id("U");
        var exponent = F.Id("N");
        var j = F.Id("j");
        return Disp(Seq(Bound("U", Call("Units", Call("PowerSeries", Integers()))),
            Bound("N", Integers()), Bound("j", Naturals()),
            Implication(Seq(D(0), Sp, Lt, Sp, j), Equal(
                Mul(Call("intCast", j), Coefficient(j, Call("val", Power(u, exponent)))),
                Mul(exponent, Coefficient(Subtract(j, D(1)),
                    Mul(Call("val", Power(u, Subtract(exponent, D(1)))),
                        Call("derivative", Integers(), Call("val", u)))))))));
    }

    private static Formula GeneralFormula()
    {
        var k = F.Id("k");
        return Disp(Seq(Bound("e", ExponentType()), Bound("k", Naturals()),
            Implication(Seq(Bound("n", Naturals()), Divides(Power(N(), k), Eval(E(), N()))),
                Seq(Bound("n", Naturals()), Implication(PositiveIndex(),
                    Divides(Power(Call("intCast", N()), k), Call("a", E(), N())))))));
    }
}
