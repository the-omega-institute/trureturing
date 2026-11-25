using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.PriceRecord;

internal sealed class PolynomialCanonicalRecordCriterionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Canonical records on integer meshes characterize the closed zero strip",
        H("The power-saving gap criterion and its polynomial specialization"),
        Blocks(
            Describe.Lean(DescribeId.Create("canonical-record-power-saving-gap-strip-iff"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/PriceRecord/PolynomialCanonicalRecordCriterion.result_of_power_saving_gaps"),
                H("Strictly increasing natural meshes with a power-saving gap"),
                StatementSource.FromAuthor(ClaimPowerSavingGaps()), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For each strictly increasing mesh N of natural numbers "
                        + "with the displayed eventual gap bound and each real "
                        + "0<alpha<=1/2, the eventual Robin lower bound is equivalent to "
                        + "Re(rho)<=1-alpha for every actual nontrivial zeta zero. "
                        + "The sample is strictInteger(firstLayerPrice(N(k)+1)). "
                        + "This is the least full golden-resource optimizer, with every "
                        + "prime-power layer considered and cutoff-equal layers excluded. "
                        + "Taking N(k)=k and G=eta=1 gives the criterion on the full "
                        + "natural tail, including prime cutoffs.")),
                    Paragraph(Text("For the lower-bound-to-strip direction, let Theta "
                        + "be the supremum of actual zero real parts and suppose "
                        + "Theta>1-alpha. Set delta=min(eta,1), choose "
                        + "max(1-alpha,Theta-delta)<sigma<Theta, and put a=1-sigma, "
                        + "epsilon=(sigma+delta-Theta)/2 and beta=Theta+epsilon. "
                        + "sample_exponent_lower transfers the same M to weight a. "
                        + "For N(k)>=12, half_shift_cutoff and continuity of price give "
                        + "X(k) strictly between N(k)+1 and N(k)+3/2, with "
                        + "price(X(k))=firstLayerPrice(N(k)+1). At this point the "
                        + "pressure potential bounds the sampled margin from above, "
                        + "and the weight comparison gives the pressure sample bound "
                        + "with constant 4*M.")),
                    Paragraph(Text("The exact-price points form a strictly increasing "
                        + "real mesh tending to infinity. Its eventual gap bound uses "
                        + "G+1/2 and delta. clock_power bounds the discrepancy of the "
                        + "complete clock with exponent beta, and a+beta-delta<=1 "
                        + "allows pressure_mesh_samples_to_all to give an all-real "
                        + "pressure lower bound. The choice of sigma applies also "
                        + "when Theta=1 or the supremum is unattained.")),
                    Paragraph(Text("At the actual integer clock, the pressure potential "
                        + "is at most the record margin. The eventual bounds "
                        + "P/2<=theta(P)<=log(m) for P=largestPrime(m) and record_weight "
                        + "transfer the lower bound to original strict records. "
                        + "margin_identity, fullC_leading and B_prefix then give an "
                        + "all-real lower envelope for B through the canonical "
                        + "prime-prefix normalization. B_lower_envelope_strip uses "
                        + "critical_theta_tail_peak to force Theta<=sigma, "
                        + "contradicting the choice of sigma.")),
                    Paragraph(Text("For the strip-to-lower-bound direction, "
                        + "actual_B_critical_strip_envelope applies at alpha, including "
                        + "alpha=1/2. Strict increase sends N(k) and its canonical "
                        + "prime prefix to infinity. fullC_leading gives an eventually "
                        + "nonnegative arithmetic correction, so margin_identity and "
                        + "B_prefix bound the sampled margin below by B(N(k))."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("polynomial-canonical-record-strip-iff"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/PriceRecord/PolynomialCanonicalRecordCriterion.result"),
                H("The closed zero strip criterion on the powers k^r"),
                StatementSource.FromAuthor(Claim()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For each natural r>=2, take N(k)=k^r, "
                    + "G=r*2^(r-1) and eta=1/r in result_of_power_saving_gaps. "
                    + "power_strictMono and polynomial_gap give the two mesh "
                    + "hypotheses. The sample remains the strict record at "
                    + "firstLayerPrice(k^r+1), with the weight evaluated at k^r. "
                    + "An eventual bound gives the displayed threshold by replacing "
                    + "it with its maximum with 2. The zero condition includes the "
                    + "boundary Re(rho)=1-alpha."))),
                DescribeRole.Theorem))));

    private static Formula Real => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Nat => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Complex => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Ex(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Lt(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Le(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula WeightedMargin(Formula alpha, Formula x)
    {
        var integer = Call("strictInteger", Call("firstLayerPrice", Add(x, D(1))));
        return Multiply(Multiply(Call("rpow", x, alpha), Call("log", x)),
            Call("robinLogMargin", integer));
    }

    private static Formula StripCriterion(Formula lower)
    {
        var alpha = F.Id("alpha");
        var rho = F.Id("rho");
        var strip = All("rho", Complex, Imp(Call("IsNontrivialZero", rho),
            Le(Call("re", rho), Subtract(D(1), alpha))));
        return All("alpha", Real, Imp(Lt(D(0), alpha),
            Imp(Le(alpha, new Formula.Fraction(D(1), D(2))),
                new Formula.Logic(lower, FormulaLogicOperator.Iff, strip))));
    }

    private static Formula ClaimPowerSavingGaps()
    {
        var mesh = F.Id("N");
        var k = F.Id("k");
        var threshold = F.Id("K");
        var m = F.Id("M");
        var g = F.Id("G");
        var eta = F.Id("eta");
        Formula Point(Formula index) => Call("cast", new Formula.Apply(mesh, [index]));
        var n = Point(k);
        var next = Point(Add(k, D(1)));
        var gap = Ex("K", Nat, All("k", Nat, Imp(Le(threshold, k),
            Le(Subtract(next, n), Multiply(g, Call("rpow", n, Subtract(D(1), eta)))))));
        var value = WeightedMargin(F.Id("alpha"), n);
        var lower = Ex("M", Real, And(Le(D(0), m), Ex("K", Nat,
            All("k", Nat, Imp(Le(threshold, k), Le(new Formula.Negate(m), value))))));
        var withGap = All("G", Real, All("eta", Real, Imp(Le(D(0), g),
            Imp(Lt(D(0), eta), Imp(gap, StripCriterion(lower))))));
        return Disp(All("N", new Formula.TypeArrow(Nat, Nat),
            Imp(Call("StrictMono", mesh), withGap)));
    }

    private static Formula Claim()
    {
        var r = F.Id("r");
        var k = F.Id("k");
        var k0 = F.Id("K");
        var m = F.Id("M");
        var n = Call("cast", Call("pow", k, r));
        var value = WeightedMargin(F.Id("alpha"), n);
        var lower = Ex("M", Real, And(Le(D(0), m), Ex("K", Nat,
            And(Le(D(2), k0), All("k", Nat, Imp(Le(k0, k),
                Le(new Formula.Negate(m), value)))))));
        return Disp(All("r", Nat, Imp(Le(D(2), r), StripCriterion(lower))));
    }
}
