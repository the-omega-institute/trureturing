using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Mertens.IntegratedExplicit;

internal sealed class PrimeCriticalResidualDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Weil/Mertens/IntegratedExplicit/PrimeCriticalResidual.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The root-scale prime-tail margin and the critical-width window",
        H("Prime-tail mass at the critical width"),
        Blocks(
            Describe.Lean(DescribeId.Create("eventually-prime-tail-root-scale"),
                DeclarationHandle.Create(Module + "eventually_prime_tail_root_scale"),
                H("A uniform margin at the square-root scale"), StatementSource.FromAuthor(RootBound()),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Analytic/zhao2025mertensmeans")),
                Blocks(
                    Paragraph(Text(
                        "Write Qθ(x) for the integral of (θ(v)−v)/v² on v>x, with each prime "
                        + "counted once in θ. Zhao's equation (14) identifies this tail in the "
                        + "cumulative Mertens error. Let Q be the corresponding complete "
                        + "Chebyshev tail that includes prime powers.")),
                    Paragraph(Text(
                        "Let ρ(k) run over all actual zero occurrences, with their analytic "
                        + "multiplicities, and put c(k)=1/(ρ(k)(1−ρ(k))). At a real-part upper bound "
                        + "β>1/2, let Pβ(u) be the negative real part of the β-line series, "
                        + "with term c(k) exp((ρ(k)−β)u) on that line. Write K(β) for the indices "
                        + "with 1/2<Re ρ(k)<β, and G(β,u) for the sum of the corresponding "
                        + "terms |c(k)| exp((Re ρ(k)−1/2)u). The coefficient norm "
                        + "sum converges. For fixed u each root-scale weight is at most "
                        + "exp(|u|/2), so the intermediate sum converges absolutely.")),
                    Paragraph(Text(
                        "At x=exp(u), the complete integrated explicit formula bounds "
                        + "√x Q(x) above by the negative real part of the root-scaled zero sum. "
                        + "Its β-line contribution is exp((β−1/2)u)Pβ(u). Its intermediate "
                        + "contribution is at most Gβ(u). For u≥0, all occurrences with real part "
                        + "at most one half have weight at most one. Their total contribution is "
                        + "at most the full coefficient norm sum, bounded by 101/100 via the "
                        + "inverse-square ordinate sum and the first Li mass.")),
                    Paragraph(Text(
                        "The prime-power correction √x (Q(x)−Qθ(x)) tends to 2 and eventually "
                        + "exceeds 7/4. After subtracting it, the upper bound on √x Qθ(x) is "
                        + "exp((β−1/2)u)Pβ(u)+Gβ(u)−1/2. The lower bound on u comes from "
                        + "the prime-power correction and x≥2, so it is uniform in β."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("prime-tail-mass-pos-or-intermediate-or-wider-zero-cluster"),
                DeclarationHandle.Create(Module + "prime_tail_mass_pos_or_intermediate_or_wider_zero_cluster"),
                H("A zero-mass window and the wider cluster value"),
                StatementSource.FromAuthor(WindowAlternative()),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Analytic/zhao2025mertensmeans")),
                Blocks(
                    Paragraph(Text(
                        "Let N(A,B) integrate max(−Qθ(x),0)/√x from A to B. Fix β>1/2, "
                        + "an upper bound for the actual zero real parts. For W>0 and a sufficiently "
                        + "late left log endpoint t−W, use the actual window [exp(t−W),exp(t)]. "
                        + "Either its mass is positive, Gβ(u) reaches 1/2 somewhere in [t−W,t], "
                        + "or zero is a cluster value of normalized mass at a width W′>W. "
                        + "For B>0 the wider window starts at exp(log B−W′)=B exp(−W′), and "
                        + "its normalization is exp((log B)(β−1/2))=B^(β−1/2).")),
                    Paragraph(Text(
                        "If the mass vanishes, continuity of the density and positivity of "
                        + "the weight give Qθ(exp(u))≥0 throughout the closed window, including "
                        + "both endpoints. If Gβ(u)<1/2 throughout that same window, the "
                        + "root-scale bound gives exp((β−1/2)u)Pβ(u)≥1/2−Gβ(u)>0. "
                        + "One threshold for the left endpoint applies the bound at every u.")),
                    Paragraph(Text(
                        "The line series is uniformly continuous, so its strict sign at t−W "
                        + "extends to the left. In the actual phase at t, the profile at lag −s "
                        + "equals Pβ(t−s). Its weighted negative part vanishes for 0≤s≤W′ "
                        + "for some W′>W. The phase-cluster equivalence sends this orbit value "
                        + "to a zero cluster value of the normalized mass as real B tends to infinity.")),
                    Paragraph(Text(
                        "Suppose a zero attains β and every zero strictly below β has real "
                        + "part at most one half. Then Gβ is zero. The attained-abscissa cutoff "
                        + "gives a unique W*>0 and a nonzero lower limit at every W′>W*. "
                        + "A zero cluster value would bound the real lower limit above by every "
                        + "positive number, while late nonnegativity bounds it below by zero. "
                        + "Thus the wider-window alternative is impossible at W*. For all "
                        + "sufficiently large B the mass at W* is strictly positive.")),
                    Paragraph(Text(
                        "For any W≥W* with B exp(−W)≥2, keep the same B. The interval at W* "
                        + "is contained in the interval at W, and the nonnegative density "
                        + "preserves the strict lower bound. This is the same interval "
                        + "containment used in FormBAt.mono in the pinned reference Window.lean, "
                        + "where Y^la ≤ Y^la′ gives the required inclusion at fixed Y≥1. "
                        + "https://github.com/the-omega-institute/riemann-hypothesis/blob/"
                        + "b8864ecd5798c6030a03d756fab95f0b89a12754/src/Formalism/"
                        + "SharpRestriction/RamificationFrobenius/TotientGaloisClasses/Window.lean#L37-L44"))),
                DescribeRole.Theorem))));

    private static Formula Real => Field("R");
    private static Formula Complex => Field("C");
    private static Formula Half => new Formula.Fraction(F.D(1), F.D(2));
    private static Formula Field(string name) => F.Seq(F.Mathbb, F.Grp(F.Id(name)));

    private static Formula Bind(FormulaQuantifier quantifier, string name, Formula domain, Formula body) =>
        new Formula.Bind(quantifier, FormulaIdentifier.Create(name), domain, body);

    private static Formula All(string name, Formula domain, Formula body) =>
        Bind(FormulaQuantifier.ForAll, name, domain, body);

    private static Formula AllAbscissae(Formula body) =>
        F.Seq(F.Forall, F.Sp, F.Beta, F.Sp, F.InMacro, F.Sp, Real, F.Comma, F.Sp, body);

    private static Formula Some(string name, Formula domain, Formula body) =>
        Bind(FormulaQuantifier.Exists, name, domain, body);

    private static Formula Lt(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);

    private static Formula Le(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula Or(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Or, right);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula Around(Formula body) => F.Seq(F.Open, body, F.Close);

    private static Formula Lambda(Formula variable, Formula domain, Formula body) =>
        Around(F.Seq(F.LambdaLower, F.Sp, variable, F.Colon, domain, F.Sp, F.Mapsto, F.Sp, body));

    private static Formula UpperBound(Formula beta)
    {
        var z = F.Id("z");
        return All("z", Complex, Implies(Call("NontrivialZero", z), Le(Call("Re", z), beta)));
    }

    private static Formula RootBound()
    {
        var beta = F.Beta;
        var u = F.Id("u");
        var k = F.Id("k");
        var re = Call("Re", F.Seq(F.Rho, F.Open, k, F.Close));
        var norm = F.Seq(F.Vert, Call("c", k), F.Vert);
        var term = Multiply(norm, Call("exp", Multiply(Around(Subtract(re, Half)), u)));
        var summability = AllAbscissae(All("u", Real,
            Call("Summable", Lambda(k, Call("K", beta), term))));
        var left = Multiply(Call("exp", new Formula.Fraction(u, F.D(2))),
            Call("Qtheta", Call("exp", u)));
        var line = Multiply(Call("exp", Multiply(Around(Subtract(beta, Half)), u)),
            Call("P", beta, u));
        var estimate = Le(left, Subtract(Add(line, Call("G", beta, u)), Half));
        var allBounds = AllAbscissae(Implies(Lt(Half, beta),
            Implies(Around(UpperBound(beta)), estimate)));
        return F.Disp(And(Around(summability),
            Call("Eventually", F.Id("atTop"), Lambda(u, Real, allBounds))));
    }

    private static Formula WindowAlternative()
    {
        var threshold = F.Id("T");
        var beta = F.Beta;
        var t = F.Id("t");
        var width = F.Id("W");
        var u = F.Id("u");
        var wider = F.Id("V");
        var endpoint = F.Id("B");
        var left = Subtract(t, width);
        var localMass = Lt(F.D(0), Call("N", Call("exp", left), Call("exp", t)));
        var intermediate = Some("u", Call("Icc", left, t), Le(Half, Call("G", beta, u)));
        var normalization = Call("exp",
            Multiply(Call("log", endpoint), Around(Subtract(beta, Half))));
        var mass = new Formula.Fraction(
            Call("N", Call("exp", Subtract(Call("log", endpoint), wider)), endpoint),
            normalization);
        var cluster = Call("MapClusterPt", F.D(0), F.Id("atTop"),
            Lambda(endpoint, Real, mass));
        var alternative = Or(localMass,
            Or(Around(intermediate), Around(Some("V", Real, And(Lt(width, wider), cluster)))));
        var window = All("t", Real, All("W", Real,
            Implies(Lt(F.D(0), width), Implies(Le(threshold, left), Around(alternative)))));
        return F.Disp(Some("T", Real, AllAbscissae(Implies(Lt(Half, beta),
            Implies(Around(UpperBound(beta)), window)))));
    }
}
