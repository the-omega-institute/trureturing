using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Mertens.IntegratedExplicit;

internal sealed class PrimeGrowingWidthClusterDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Weil/Mertens/IntegratedExplicit/PrimeGrowingWidthCluster.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Cluster values for growing prime-tail windows",
        H("Growing logarithmic widths"),
        Blocks(
            Describe.Lean(DescribeId.Create("phase-window-infinite"),
                DeclarationHandle.Create(Module + "phaseWindowInfinite"),
                H("Exponentially weighted infinite phase window"), StatementSource.FromAuthor(Window()),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                    "The profile F uses the coefficients on the line r(ρ)=β. Each coordinate of h "
                    + "is indexed by an actual zero occurrence, including multiplicities. "
                    + "The integral uses Lebesgue measure on s>0. Including s=0 gives the same value."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("prime-tail-growing-width-cluster-iff-of-upper-bound"),
                DeclarationHandle.Create(Module + "prime_tail_growing_width_cluster_iff_of_upper_bound"),
                H("Exact cluster values for moving left endpoints"), StatementSource.FromAuthor(Claim()),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Analytic/zhao2025mertensmeans")),
                Blocks(
                    Paragraph(Text(
                        "Write Qϑ(x) for the actual prime-only tail, the integral of (ϑ(u)−u)/u² "
                        + "over u>x from Zhao's equation (14). The mass N(A,B) integrates "
                        + "max(−Qϑ(x),0)/√x from A to B. The variable B tends to +∞ through real values. "
                        + "The left endpoint A(B) is chosen pointwise. The constant choice A(B)=2 "
                        + "gives the cumulative mass.")),
                    Paragraph(Text(
                        "Let H be the closure of the simultaneous orbit φ of the actual zero occurrences, "
                        + "and put p=β−1/2>0. If S is the sum of the norms of the complete-tail coefficients, "
                        + "the infinite phase integral minus its truncation at L≥0 lies between zero and "
                        + "(S/p) exp(−pL) for every phase. Thus the continuous finite-width integrals "
                        + "converge uniformly, and the infinite phase integral is continuous.")),
                    Paragraph(Text(
                        "Fix L≥0 and put D=B exp(−L). Eventually A(B)≤D≤B. Let X≥2 be a fixed "
                        + "threshold beyond which the arithmetic density is bounded by C x^(p−1). "
                        + "For B with D≥X, split the added segment [A(B),D] at max(A(B),X). "
                        + "Its early contribution is at most C₀=N(2,X). Integrating the power "
                        + "bound on the rest and dividing by B^p bounds the normalized added mass by "
                        + "(C/p) exp(−pL)+C₀/B^p, uniformly in the admissible left endpoint.")),
                    Paragraph(Text(
                        "At fixed L the logarithmic change of variables and the signed-input estimate "
                        + "approximate the normalized rightmost window by the finite phase integral at "
                        + "φ(log B). Taking L large and then B large makes the moving mass differ "
                        + "from the infinite integral at that very phase by a quantity tending to zero. "
                        + "Forward recurrence of φ and compactness of H give both directions of the "
                        + "cluster equivalence. If the β-line is empty, the phase image is {0}. "
                        + "In particular β=1 is an admissible upper bound and its line is empty.")),
                    Paragraph(Text(
                        "Bugajewski, Diagana and Mahop study integrable-kernel convolution of "
                        + "asymptotically almost periodic functions in Theorem 3.3 and the exponential "
                        + "kernel in §4 (doi:10.4171/zaa/1292). Bingham and Gashi's logarithmic moving "
                        + "averages use logarithmic summability normalization (arXiv:1408.1301)."))),
                DescribeRole.Theorem))));

    private static Formula Field(string name) => Seq(Mathbb, Grp(F.Id(name)));
    private static Formula Real => Field("R");
    private static Formula Complex => Field("C");
    private static Formula Phases => new Formula.Power(Field("T"), Field("N"));
    private static Formula FunctionType(Formula domain, Formula range) =>
        Seq(Open, domain, Sp, To, Sp, range, Close);
    private static Formula Half => new Formula.Fraction(D(1), D(2));
    private static Formula InfiniteWindow => Seq(F.Id("I"), Underscore, Grp(Infty));
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula Equal(Formula x, Formula y) =>
        new Formula.Relation(x, FormulaRelationOperator.Equal, y);
    private static Formula Le(Formula x, Formula y) =>
        new Formula.Relation(x, FormulaRelationOperator.LessThanOrEqual, y);
    private static Formula And(Formula x, Formula y) => new Formula.Logic(x, FormulaLogicOperator.And, y);
    private static Formula ImpliesClaim(Formula x, Formula y) =>
        new Formula.Logic(x, FormulaLogicOperator.Implies, y);
    private static Formula Lambda(Formula variable, Formula body) =>
        Seq(Open, LambdaLower, Sp, variable, Colon, Real, Sp, Mapsto, Sp, body, Close);
    private static Formula WindowAt(Formula r, Formula beta, Formula h) =>
        Seq(InfiniteWindow, Open, r, Comma, Sp, beta, Comma, Sp, h, Close);

    private static Formula Window()
    {
        var r = F.Id("r");
        var beta = F.Id("beta");
        var h = F.Id("h");
        var s = F.Id("s");
        var exponent = Multiply(new Formula.Negate(Subtract(beta, Half)), s);
        var negativePart = Call("max", new Formula.Negate(Call("F", r, beta, h,
            new Formula.Negate(s))), D(0));
        var integral = Seq(Int, Underscore, Grp(Call("Ioi", D(0))), Sp,
            Multiply(Call("exp", exponent), negativePart), Sp, F.Id("d"), s);
        return Disp(All("r", FunctionType(Complex, Real), All("beta", Real, All("h", Phases,
            Equal(WindowAt(r, beta, h), integral)))));
    }

    private static Formula Claim()
    {
        var z = F.Id("z");
        var beta = F.Id("beta");
        var y = F.Id("y");
        var b = F.Id("B");
        var a = Call("A", b);
        var h = F.Id("h");
        var atTop = F.Id("atTop");
        var betaBound = new Formula.Relation(Half, FormulaRelationOperator.LessThan, beta);
        var upperBound = All("z", Complex,
            ImpliesClaim(Call("NontrivialZero", z), Le(Call("Re", z), beta)));
        var admissible = Call("Eventually", Lambda(b, And(Le(D(2), a), Le(a, b))), atTop);
        var widthLimit = Call("Tendsto", Lambda(b, Call("log", new Formula.Fraction(b, a))),
            atTop, atTop);
        var mass = new Formula.Fraction(Call("N", a, b), new Formula.Power(b, Subtract(beta, Half)));
        var cluster = Call("MapClusterPt", y, atTop, Lambda(b, mass));
        var image = new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create("h"), Phases,
            And(Seq(h, Sp, InMacro, Sp, Call("closure", Call("range", F.Id("phi")))),
                Equal(y, WindowAt(F.Id("Re"), beta, h))));
        var equivalence = new Formula.Logic(cluster, FormulaLogicOperator.Iff, image);
        return Disp(All("beta", Real, ImpliesClaim(betaBound, ImpliesClaim(upperBound,
            All("A", FunctionType(Real, Real), ImpliesClaim(admissible, ImpliesClaim(widthLimit,
                All("y", Real, equivalence))))))));
    }
}
