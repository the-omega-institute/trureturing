using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Periodic;

internal sealed class ScaledLogColumnPeriodicityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Periodic/ScaledLogColumnPeriodicity.";
    private static readonly LibraryNoteRef SquareSource =
        LibraryNoteRef.Create("D5/L/ArithSums/bala2026a383165");
    private static readonly LibraryNoteRef CubeSource =
        LibraryNoteRef.Create("D5/L/ArithSums/bala2026a383166");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every scaled logarithm column is eventually periodic modulo every positive integer.",
        H("Eventual Periods of Scaled Logarithm Columns"),
        Blocks(
            Paragraph(Text("Seiichi Manyama's entries A383165 and A383166, dated April 18, "
                + "2025, give the square and cube columns. Peter Bala's conjectures, dated "
                + "February 17, 2026, ask for eventual periodicity modulo every positive "
                + "integer. The notes bala2026a383165 and bala2026a383166 record the two "
                + "statements. The theorem below applies to every natural column r.")),
            Paragraph(Text("All indices, columns, moduli, onsets and periods are natural "
                + "numbers. The sequence a is integer-valued. Power series have rational "
                + "coefficients: exp is PowerSeries.exp over the rationals, rescale(c,F) "
                + "replaces X by cX, C embeds a rational constant, and logOf(H) is the "
                + "formal logarithm of H, namely PowerSeries.log substituted at H-1. "
                + "The function coeff(n,F) extracts a coefficient, mk forms a series from "
                + "its coefficient function, factorial is Nat.factorial, and rat denotes "
                + "a cast to the rationals. Every fraction displayed here is rational "
                + "division. The function num returns the reduced rational numerator; "
                + "residue(m,z) denotes the integer cast to ZMod m.")),
            Node("a", "The e.g.f. coefficient sequence", SequenceFormula(),
                "The definition extracts the factorial-scaled coefficient of "
                + "log(1+(exp(2X)-1)/2)^r/r!. The integral differential bridge proves "
                + "that this rational number has denominator one, so numerator "
                + "extraction loses no information.",
                DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("generating_equation", "The defining scaled logarithm e.g.f.",
                GeneratingFormula(),
                "Put H=(1+exp(2X))/2 and U=H inverse. Then H'=2H-1, U'=U squared "
                + "minus 2U, and (log H)'=2-U. Differentiating "
                + "B(r,j)=U^j (log H)^r/r! gives j B(r,j+1)-2j B(r,j), together with "
                + "2 B(r-1,j)-B(r-1,j+1) when r is positive. Its initial constant "
                + "coefficient is one for r=0 and zero otherwise. Induction identifies "
                + "the resulting integer recurrence with n! times coeff(n,B(r,j)). "
                + "At j=0 this proves integrality and the displayed generating identity.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("coefficient_periodicity", "Eventual periodicity of every column",
                PeriodFormula(V("r"), true),
                "Modulo m the differential recurrence depends on j only through its "
                + "residue. For fixed r, the values indexed by columns at most r and "
                + "auxiliary indices below m form a finite state. Equal states have "
                + "equal successors. The pigeonhole principle gives a repeated state, "
                + "and induction propagates that equality to all later indices. The "
                + "scaled coefficient bridge transfers the resulting positive period "
                + "to a. Neither a specific onset nor a minimal period is asserted.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("bala_conjecture_a383165", "Bala's conjecture on A383165",
                PeriodFormula(D(2), false),
                "Specialize the general theorem to r=2. The proved generating equation "
                + "identifies this column with the square divided by two in "
                + "bala2026a383165, proving the conjecture for every positive modulus.",
                DescribeRole.Theorem, AssessedProvenance.FromLiterature(SquareSource),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a383165-scaled-log-column-periodicity"),
                    ResolutionKind.Proved)),
            Node("bala_conjecture_a383166", "Bala's conjecture on A383166",
                PeriodFormula(D(3), false),
                "Specialize the general theorem to r=3. The proved generating equation "
                + "identifies this column with the cube divided by six in "
                + "bala2026a383166, proving the conjecture for every positive modulus.",
                DescribeRole.Theorem, AssessedProvenance.FromLiterature(CubeSource),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a383166-scaled-log-column-periodicity"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, string title, Formula formula,
        string prose, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? claim = null) => Describe.Lean(
        DescribeId.Create("scaled-log-" + name.Replace('_', '-').ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name), H(title),
        StatementSource.FromAuthor(formula), provenance, Blocks(Paragraph(Text(prose))), role, claim);

    private static Formula SequenceFormula() => Disp(Seq(Bound("r", "n"), Sp,
        Equality(Call("a", V("r"), V("n")), Call("num",
            Mul(Rat(Call("factorial", V("n"))), Call("coeff", V("n"), Egf()))))));

    private static Formula GeneratingFormula() => Disp(Seq(Bound("r"), Sp,
        Equality(Call("mk", Lambda("n", new Formula.Fraction(
            Rat(Call("a", V("r"), V("n"))), Rat(Call("factorial", V("n")))))), Egf())));

    private static Formula Egf() => Mul(
        Call("C", new Formula.Fraction(D(1), Rat(Call("factorial", V("r"))))),
        Power(Call("logOf", Parenthesized(Add(D(1), Mul(
            Call("C", new Formula.Fraction(D(1), D(2))),
            Parenthesized(Subtract(Call("rescale", D(2), V("exp")), D(1))))))), V("r")));

    private static Formula PeriodFormula(Formula column, bool general)
    {
        Formula Term(Formula index) => Call("a", column, index);
        var equality = Equality(Residue(Term(Add(V("n"), V("p")))), Residue(Term(V("n"))));
        var tail = Seq(Bound("n"), Sp,
            Implication(Seq(V("N"), Sp, Le, Sp, V("n")), equality));
        var period = Seq(Exists, Sp, V("N"), Comma, Sp, V("p"), Colon, Sp, Naturals(), Comma, Sp,
            Parenthesized(Seq(Parenthesized(Seq(D(0), Sp, Lt, Sp, V("p"))), Sp, Land, Sp,
                Parenthesized(tail))));
        return Disp(Seq(general ? Bound("r", "m") : Bound("m"), Sp,
            Implication(Seq(D(0), Sp, Lt, Sp, V("m")), period)));
    }

    private static Formula Rat(Formula x) => Call("rat", x);
    private static Formula Residue(Formula x) => Call("residue", V("m"), x);
    private static Formula V(string name) => F.Id(name);
    private static Formula Naturals() => Seq(Mathbb, Grp(V("N")));
    private static Formula Lambda(string variable, Formula body) => Parenthesized(Seq(
        V(variable), Colon, Sp, Naturals(), Sp, Mapsto, Sp, body));
    private static Formula Parenthesized(Formula x) => Seq(Open, x, Close);
    private static Formula Equality(Formula x, Formula y) => Seq(x, Sp, Eq, Sp, y);
    private static Formula Implication(Formula x, Formula y) =>
        Seq(Parenthesized(x), Sp, Implies, Sp, Parenthesized(y));
    private static Formula Power(Formula x, Formula y) => new Formula.Power(Parenthesized(x), y);
    private static Formula Add(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Add, y);
    private static Formula Subtract(Formula x, Formula y) =>
        new Formula.Binary(x, FormulaBinaryOperator.Subtract, y);
    private static Formula Mul(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Multiply, y);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(name))), [.. args]);
    private static Formula Bound(params string[] names)
    {
        List<Formula> variables = [];
        foreach (var name in names)
        {
            if (variables.Count > 0) variables.AddRange([Comma, Sp]);
            variables.Add(V(name));
        }
        return Seq(Forall, Sp, Seq([.. variables]), Colon, Sp, Naturals(), Comma);
    }
}
