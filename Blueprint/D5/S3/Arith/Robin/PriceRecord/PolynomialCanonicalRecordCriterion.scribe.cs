using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.PriceRecord;

internal sealed class PolynomialCanonicalRecordCriterionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Polynomial canonical records characterize the closed zero strip",
        H("The full polynomial sampling criterion"),
        Blocks(Describe.Lean(DescribeId.Create("polynomial-canonical-record-strip-iff"),
            DeclarationHandle.Create("D5/S3/Arith/Robin/PriceRecord/PolynomialCanonicalRecordCriterion.result"),
            H("All natural powers and all real strip exponents"),
            StatementSource.FromAuthor(Claim()), AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("For each natural r>=2 and each real 0<alpha<=1/2, one "
                    + "nonnegative constant M bounds all sufficiently late natural samples. "
                    + "The sampled integer is strictInteger(firstLayerPrice(k^r+1)); "
                    + "strictInteger is the least full golden-resource optimizer, with every "
                    + "prime-power layer retained and equality excluded at the strict cutoff. "
                    + "robinLogMargin has its original arithmetic definition. The right side "
                    + "quantifies over every actual nontrivial zeta zero, including the closed "
                    + "boundary Re(rho)=1-alpha. This criterion does not prove RH or the "
                    + "sample lower bound.")),
                Paragraph(Text("Write W(a,X)=X^a*log(X) and "
                    + "S(X)=EulerGamma+log(log(X))-1/log(X)-pressure(price(X)). "
                    + "The complete pressure FTC gives the compact-interval modulus "
                    + "|S(b)-S(a)|<=E*(price(a)-price(b)) when |u-clock(u)|<=E on [a,b]. "
                    + "The primitive derivative is u*weight(u); the clock integrand uses "
                    + "the original complete inventory. The polynomial mesh has endpoints "
                    + "N=k^r and (k+1)^r, width at most r*2^(r-1)*N/k, and a fixed "
                    + "multiplicative enclosure. These estimates fill all real X, with no "
                    + "public mesh hypothesis.")),
                Paragraph(Text("For the lower-bound-to-strip direction, let Theta be the "
                    + "supremum of actual zero real parts. If Theta>1-alpha, choose "
                    + "max(1-alpha,Theta-1/r)<sigma<Theta and set a=1-sigma, "
                    + "epsilon=(sigma+1/r-Theta)/2>0, beta=Theta+epsilon. "
                    + "The same M descends from alpha to a because 0<N^(a-alpha)<=1 "
                    + "and M>=0. Only the difference between two margins with the same "
                    + "prime prefix uses the existing square-root normalization; W/D<=1 "
                    + "scales that difference. The full clock discrepancy is O(X^beta), "
                    + "and a+beta-1-1/r=-epsilon pays the mesh error. Beta may exceed one; "
                    + "Theta=1 and an unattained supremum are included.")),
                Paragraph(Text("Pressure at the actual integer clock is at most its "
                    + "margin. For every original strict predecessor record, "
                    + "log(m)>=theta(P)>=P/2 eventually, where P=largestPrime(m). "
                    + "Thus W(a,P)<=4*W(a,log(m)), and sign-sensitive rescaling transports "
                    + "the all-real pressure lower bound to all original records. "
                    + "The exact margin_identity, fullC_leading and B_prefix then give "
                    + "an all-real lower B envelope. The correction upper bound is scaled "
                    + "before normalization, without assuming its sign. The proved canonical "
                    + "prime-prefix normalization transfers the fixed nonpositive constant. "
                    + "The exact one-sided B converse forces Theta<=sigma, a contradiction.")),
                Paragraph(Text("For the strip-to-lower-bound direction, "
                    + "actual_B_critical_strip_envelope is used at the original alpha. "
                    + "The full arithmetic correction is eventually positive at all these "
                    + "actual records. The exact prime-prefix B identity then bounds each "
                    + "margin below by B(k^r). This direction needs no PNT normalization "
                    + "ratio and retains alpha=1/2. All constants and thresholds may depend "
                    + "on r and alpha; no finite surrogate replaces either natural tail "
                    + "quantifier or the full zero strip."))),
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

    private static Formula Claim()
    {
        var r = F.Id("r");
        var alpha = F.Id("alpha");
        var k = F.Id("k");
        var k0 = F.Id("K");
        var m = F.Id("M");
        var rho = F.Id("rho");
        var n = Call("pow", k, r);
        var integer = Call("strictInteger", Call("firstLayerPrice", Add(n, D(1))));
        var value = Multiply(Multiply(Call("rpow", n, alpha), Call("log", n)),
            Call("robinLogMargin", integer));
        var lower = Ex("M", Real, And(Le(D(0), m), Ex("K", Nat,
            And(Le(D(2), k0), All("k", Nat, Imp(Le(k0, k),
                Le(new Formula.Negate(m), value)))))));
        var strip = All("rho", Complex, Imp(Call("IsNontrivialZero", rho),
            Le(Call("re", rho), Subtract(D(1), alpha))));
        return Disp(All("r", Nat, Imp(Le(D(2), r), All("alpha", Real,
            Imp(Lt(D(0), alpha), Imp(Le(alpha, new Formula.Fraction(D(1), D(2))),
                new Formula.Logic(lower, FormulaLogicOperator.Iff, strip)))))));
    }
}
