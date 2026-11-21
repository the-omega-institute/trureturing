using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Mertens.IntegratedExplicit;

internal sealed class PrimePhaseClusterDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Weil/Mertens/IntegratedExplicit/PrimePhaseCluster.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Cluster values of normalized prime-tail window mass",
        H("The actual zeta phase orbit at an attained maximal real part"),
        Blocks(
            Describe.Lean(DescribeId.Create("phase-orbit"), DeclarationHandle.Create(Module + "phaseOrbit"),
                H("Simultaneous zero phases"), StatementSource.FromAuthor(Orbit()),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                    "The index k runs over all actual zero occurrences via actualOccurrenceEquiv. "
                    + "Write γ(k)=Im(actualZero(k)). The coordinates are unit complex numbers."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("rightmost-coeff"),
                DeclarationHandle.Create(Module + "rightmostCoeff"),
                H("Coefficients on the selected line"), StatementSource.FromAuthor(Coefficient()),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                    "The real-part map r is fixed to Re in the theorem. The coefficient c(k) is "
                    + "actualCoeff(k), the reciprocal of ρ(k)(1−ρ(k)) at occurrence k."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("phase-profile"),
                DeclarationHandle.Create(Module + "phaseProfile"),
                H("The real complete-tail profile"), StatementSource.FromAuthor(Profile()),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                    "The minus sign comes from the actual integrated explicit formula. "
                    + "Norms of the original coefficients give one summable bound for all phases and lags."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("phase-window"),
                DeclarationHandle.Create(Module + "phaseWindow"),
                H("Weighted negative part over a log window"), StatementSource.FromAuthor(Window()),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                    "The real variable s runs backwards from the right endpoint in logarithmic coordinates."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("prime-tail-mass-cluster-iff-of-attained-zero"),
                DeclarationHandle.Create(Module + "prime_tail_mass_cluster_iff_of_attained_zero"),
                H("Exact cluster-set equivalence"), StatementSource.FromAuthor(Claim()),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Analytic/zhao2025mertensmeans")),
                Blocks(
                    Paragraph(Text(
                        "Let N(A,B) denote the Chapter 31 interval integral from A to B of "
                        + "max(−Qϑ(x),0)/√x. Here Qϑ is primeTail, the integral of (ϑ(u)−u)/u² "
                        + "over u>x, with each prime counted once in ϑ. Cluster means MapClusterPt "
                        + "along the real atTop filter. H is the closure of the range of the simultaneous real phase orbit.")),
                    Paragraph(Text(
                        "The product of circles is compact. Apply mapClusterPt_one_atTop_pow to φ(1). "
                        + "Multiplication by φ(t) sends those powers to φ(t+n), and t+n tends to infinity "
                        + "along the natural numbers. Thus every orbit point belongs to the closed set of "
                        + "forward cluster points. The reverse inclusion follows from containment in H.")),
                    Paragraph(Text(
                        "The common summable coefficient bound gives joint continuity in phase and lag. "
                        + "Parametric interval integration gives continuity of I. Its image of H is compact "
                        + "and hence closed. The continuous image of the real line under φ and its closure "
                        + "are connected, so the functional image is a compact interval.")),
                    Paragraph(Text(
                        "Put t=log B and p=Re ρ−1/2. The substitution x=exp(t−s) gives the exact "
                        + "normalized integral with weight exp(−ps) and signed input "
                        + "exp((1−Re ρ)(t−s))·Qϑ(exp(t−s)). On the orbit the profile is the negative "
                        + "real part of the actual maximal series at t−s. The complete-tail approximation "
                        + "and normalized prime-power error bound the difference of the signed inputs "
                        + "by δ on all of [t−W,t] once t is sufficiently large. The 1-Lipschitz "
                        + "negative part bounds the window error by δ times the integral of exp(−ps).")),
                    Paragraph(Text(
                        "The vanishing window error preserves cluster values by the triangle inequality "
                        + "in frequent metric balls. Continuity and forward recurrence yield every value "
                        + "in the phase image, and closedness of that image contains every cluster value "
                        + "of the phase windows. Exponentiation and logarithm preserve the real cofinal limit.")),
                    Paragraph(Text(
                        "Kaczorowski and Ramaré discuss translation hulls in Section 4 of "
                        + "Almost periodicity of some error terms in prime number theory "
                        + "(doi:10.4064/aa106-3-6). Lee et al. relate the uniform translation hull "
                        + "to the Bohr compactification in Appendix A.2 of arXiv:1907.07017."))),
                DescribeRole.Theorem))));

    private static Formula Field(string name) => Seq(Mathbb, Grp(F.Id(name)));
    private static Formula Real => Field("R");
    private static Formula Complex => Field("C");
    private static Formula Nat => Field("N");
    private static Formula Phases => new Formula.Power(Field("T"), Nat);
    private static Formula RealPartType => Seq(Open, Complex, Sp, To, Sp, Real, Close);
    private static Formula Half => new Formula.Fraction(D(1), D(2));
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula Equal(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Less(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula ImpliesClaim(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Implies, b);

    private static Formula Orbit()
    {
        var t = F.Id("t");
        var k = F.Id("k");
        return Disp(All("t", Real, All("k", Nat, Equal(Call("phi", t, k),
            Call("exp", Multiply(Multiply(F.Id("i"), Call("gamma", k)), t))))));
    }

    private static Formula Coefficient()
    {
        var r = F.Id("r");
        var beta = F.Id("beta");
        var k = F.Id("k");
        var onLine = Equal(Call("r", Call("actualZero", k)), beta);
        return Disp(All("r", RealPartType, All("beta", Real, All("k", Nat,
            Equal(Call("a", r, beta, k), Call("ite", onLine, Call("c", k), D(0)))))));
    }

    private static Formula Profile()
    {
        var r = F.Id("r");
        var beta = F.Id("beta");
        var h = F.Id("h");
        var u = F.Id("u");
        var k = F.Id("k");
        var terms = Seq(Sum, Underscore, Grp(k, Sp, InMacro, Sp, Nat), Sp,
            Multiply(Multiply(Call("a", r, beta, k), Call("h", k)), Call("phi", u, k)));
        var profile = new Formula.Negate(Call("Re", terms));
        return Disp(All("r", RealPartType, All("beta", Real, All("h", Phases, All("u", Real,
            Equal(Call("F", r, beta, h, u), profile))))));
    }

    private static Formula Window()
    {
        var r = F.Id("r");
        var beta = F.Id("beta");
        var width = F.Id("W");
        var h = F.Id("h");
        var s = F.Id("s");
        var exponent = Multiply(new Formula.Negate(Subtract(beta, Half)), s);
        var negativePart = Call("max", new Formula.Negate(Call("F", r, beta, h,
            new Formula.Negate(s))), D(0));
        var integral = Seq(Int, Underscore, Grp(D(0)), Caret, Grp(width), Sp,
            Multiply(Call("exp", exponent), negativePart), Sp, F.Id("d"), s);
        return Disp(All("r", RealPartType, All("beta", Real, All("W", Real, All("h", Phases,
            Equal(Call("I", r, beta, width, h), integral))))));
    }

    private static Formula Claim()
    {
        var rho = F.Id("rho");
        var z = F.Id("z");
        var beta = Call("Re", rho);
        var width = F.Id("W");
        var y = F.Id("y");
        var b = F.Id("B");
        var h = F.Id("h");
        var maximal = All("z", Complex, ImpliesClaim(Call("NontrivialZero", z),
            new Formula.Relation(Call("Re", z), FormulaRelationOperator.LessThanOrEqual, beta)));
        var mass = new Formula.Fraction(
            Call("N", Multiply(b, Call("exp", new Formula.Negate(width))), b),
            new Formula.Power(b, Subtract(beta, Half)));
        var massFunction = Seq(Open, LambdaLower, Sp, b, Colon, Real, Sp, Mapsto, Sp, mass, Close);
        var cluster = Call("MapClusterPt", y, F.Id("atTop"), massFunction);
        var image = new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create("h"), Phases,
            new Formula.Logic(Seq(h, Sp, InMacro, Sp, Call("closure", Call("range", F.Id("phi")))),
                FormulaLogicOperator.And,
                Equal(y, Call("I", F.Id("Re"), beta, width, h))));
        var equivalence = new Formula.Logic(cluster, FormulaLogicOperator.Iff, image);
        return Disp(All("rho", Complex, ImpliesClaim(Call("NontrivialZero", rho),
            ImpliesClaim(Less(Half, beta), ImpliesClaim(maximal,
                All("W", Real, ImpliesClaim(Less(D(0), width), All("y", Real, equivalence))))))));
    }
}
