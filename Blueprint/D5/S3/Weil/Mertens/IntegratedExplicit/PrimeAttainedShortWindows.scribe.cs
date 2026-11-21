using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Mertens.IntegratedExplicit;

internal sealed class PrimeAttainedShortWindowsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Positive prime-tail windows at an attained zeta abscissa",
        H("Positive prime-tail windows at an attained zeta abscissa"),
        Blocks(Describe.Lean(
            DescribeId.Create("prime-tail-positive-short-windows-of-attained-zero"),
            DeclarationHandle.Create("D5/S3/Weil/Mertens/IntegratedExplicit/"
                + "PrimeAttainedShortWindows.prime_tail_positive_short_windows_of_attained_zero"),
            H("Recurring whole windows of positivity"),
            StatementSource.FromAuthor(F.Disp(Claim())),
            AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Analytic/zhao2025mertensmeans")),
            Blocks(
                Paragraph(Text("Let Qθ(x) be the integral of (θ(u)−u)/u² over u>x, with θ "
                    + "summing log p once for each prime p≤u. This is the tail in Zhao's "
                    + "equation (14). Let N(A,B) be the integral of max(−Qθ(x),0)/√x from A "
                    + "to B, and let Q be the tail defined using ψ in place of θ.")),
                Paragraph(Text("Choose the positive-ordinate zero in the conjugate pair of the "
                    + "supplied zero. Write β for its real part and γ for its positive ordinate. "
                    + "A compact forward probability filter preserves this pair and cancels "
                    + "all other modes right of a cutoff strictly between one half and β. "
                    + "The resulting leading cosine gives a positive value of Q(exp u) at "
                    + "some u in every sufficiently late log window of length W=2π/γ+h, "
                    + "where h is the filter support bound. Since β<1, the normalized value "
                    + "exp((1−β)u)Q(exp u) exceeds a single c>0 at these peaks.")),
                Paragraph(Text("The maximal real-part projection gives a uniformly continuous "
                    + "approximant to the normalized unfiltered tail. It keeps all modes "
                    + "with real part β. Absolute summability controls the strict lower modes "
                    + "even when their real parts approach β. The root-scale prime-power "
                    + "correction tends to two, so after normalization at β>1/2 the correction "
                    + "tends to zero. The normalized prime-only tail therefore has the same "
                    + "approximant and retains a positive margin at each sufficiently late peak.")),
                Paragraph(Text("Choose δ>0 so that the approximant moves by less than c/4 "
                    + "over distances less than δ. The margin and the approximation errors "
                    + "at both points give positivity for every v in [u,u+δ/2]. Starting at "
                    + "log X and exponentiating gives A=exp u, K=exp W, and R=exp(δ/2). "
                    + "Positivity holds at both endpoints. For each ratio k in [1,R], "
                    + "the integrand of N(A,kA) vanishes on the entire interval.")),
                Paragraph(Text("Kaczorowski's bounded-gap level crossings and discussion of "
                    + "the attained case give a precedent for the almost-periodic method "
                    + "on different observables. See pp. 232 and 234, DOI 10.4064/aa-57-3-231-244."))),
            DescribeRole.Theorem))));

    private static Formula Field(string name) => F.Seq(F.Mathbb, F.Grp(F.Id(name)));

    private static Formula Bind(FormulaQuantifier quantifier, string name, Formula domain, Formula body) =>
        new Formula.Bind(quantifier, FormulaIdentifier.Create(name), domain, body);

    private static Formula Le(Formula x, Formula y) =>
        new Formula.Relation(x, FormulaRelationOperator.LessThanOrEqual, y);

    private static Formula Lt(Formula x, Formula y) =>
        new Formula.Relation(x, FormulaRelationOperator.LessThan, y);

    private static Formula Implies(Formula p, Formula q) => new Formula.Logic(p, FormulaLogicOperator.Implies, q);
    private static Formula And(Formula p, Formula q) => new Formula.Logic(p, FormulaLogicOperator.And, q);

    private static Formula Claim()
    {
        var complex = Field("C");
        var real = Field("R");
        var rho = F.Id("rho");
        var z = F.Id("z");
        var beta = Call("Re", rho);
        var ratio = F.Id("R");
        var k = F.Id("k");
        var gap = F.Id("K");
        var threshold = F.Id("S");
        var startScale = F.Id("X");
        var left = F.Id("A");
        var x = F.Id("x");
        var zero = F.D(0);
        var one = F.D(1);
        var two = F.D(2);
        var half = new Formula.Fraction(one, two);
        var maximal = Bind(FormulaQuantifier.ForAll, "z", complex,
            Implies(Call("NontrivialZero", z), Le(Call("Re", z), beta)));
        var positive = Bind(FormulaQuantifier.ForAll, "x", Call("Icc", left, Multiply(ratio, left)),
            Lt(zero, Call("Qtheta", x)));
        var negativeMass = Bind(FormulaQuantifier.ForAll, "k", Call("Icc", one, ratio),
            Equal(Call("N", left, Multiply(k, left)), zero));
        var windows = Bind(FormulaQuantifier.ForAll, "X", real, Implies(Le(threshold, startScale),
            Bind(FormulaQuantifier.Exists, "A", Call("Icc", startScale, Multiply(gap, startScale)),
                And(positive, negativeMass))));
        var constants = Bind(FormulaQuantifier.Exists, "R", real,
            Bind(FormulaQuantifier.Exists, "K", real,
                Bind(FormulaQuantifier.Exists, "S", real,
                    And(Lt(one, ratio), And(Le(one, gap), And(Le(two, threshold), windows))))));
        return Bind(FormulaQuantifier.ForAll, "rho", complex,
            Implies(Call("NontrivialZero", rho), Implies(Lt(half, beta), Implies(maximal, constants))));
    }
}
