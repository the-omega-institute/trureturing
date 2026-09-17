using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith;

internal sealed class GoldenConicFourierNoCancellationDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Arith/GoldenConicFourierNoCancellation.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual two and four stationary phases cannot cancel in an odd-modulus golden orbit.",
        H("No Complete Cancellation in the Golden Conic Fourier Sum"),
        Blocks(
            Paragraph(Text("The modulus N is nonzero. Every exponential in the formulas "
                + "is the actual canonical additive character ZMod.stdAddChar on ZMod N, "
                + "with complex values. It is not an arbitrary measured function. The "
                + "four-term scalar i is a ring element satisfying i squared equals minus one; "
                + "it is distinct from the complex imaginary unit in the exponential notation.")),
            Describe.Lean(DescribeId.Create("golden-fourier-pair-period"),
                DeclarationHandle.Create(Owner + "pairPeriod"), H("Two opposite actual phases"),
                StatementSource.FromAuthor(PairFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a in ZMod N and s in Complex, pairPeriod(a,s) "
                    + "is e_N(a)+s*e_N(-a). Only the theorem restricts s to plus or minus one. "
                    + "Both signs are needed because the odd-precision quadratic Gauss "
                    + "coefficient can change sign at the opposite stationary point."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("golden-fourier-quarter-period"),
                DeclarationHandle.Create(Owner + "quarterPeriod"), H("Four scalar-root phases"),
                StatementSource.FromAuthor(QuarterFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("quarterPeriod(a,i,s) is pairPeriod(a,1) plus "
                    + "s*pairPeriod(i*a,1). With i squared equal to minus one, it is "
                    + "the actual four-phase expression on the scalar stabilizer "
                    + "{1,-1,i,-i}. The definition does not assume its nonvanishing."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("golden-fourier-phase-noncancellation"),
                DeclarationHandle.Create(Owner + "result"), H("Both Gauss signs remain nonzero"),
                StatementSource.FromAuthor(ResultFormula()), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For every odd natural N at least three, and every "
                        + "a,ainv in ZMod N with a*ainv=1, both pairPeriod(a,1) and "
                        + "pairPeriod(a,-1) are nonzero. For every i with i^2=-1, "
                        + "quarterPeriod(a,i,1) and quarterPeriod(a,i,-1) are also "
                        + "nonzero. The modulus need not be prime.")),
                    Paragraph(Text("The proof first shows that canonical character values "
                        + "have odd order and cannot equal minus one. Faithfulness and "
                        + "the displayed inverse rule out equal or reciprocal phases "
                        + "when i^2=-1. Writing x=e_N(a), y=e_N(i*a), multiplication "
                        + "by x*y factors the plus expression as (x+y)*(x*y+1) and "
                        + "the minus expression as (x-y)*(x*y-1). Every zero factor "
                        + "would contradict those arithmetic exclusions.")),
                    Paragraph(Text("Section 7 of the existing li2026nonwieferich theory "
                        + "note uses this kernel after proving that the original "
                        + "golden orbit has scalar stabilizer of size tau/rho in "
                        + "{1,2,4}. It completes the previously unresolved cancellation "
                        + "step in the full Fourier support. The rank quotient, "
                        + "all-precision support, first-zero criterion and moment "
                        + "formulas are ordinary proofs there, not additional "
                        + "claims of kernel-certified conclusions of this declaration."))),
                DescribeRole.Theorem))));

    private static Formula V(string name) => F.Id(name);
    private static Formula C(string name, params Formula[] xs) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(name))), xs);
    private static Formula Nats() => Seq(Mathbb, Grp(V("N")));
    private static Formula Complexes() => Seq(Mathbb, Grp(V("C")));
    private static Formula Ring() => C("ZMod", V("N"));
    private static Formula All(string x, Formula t, Formula body) =>
        Seq(Forall, Sp, V(x), Sp, InMacro, Sp, t, Comma, Sp, body);
    private static Formula Eqn(Formula x, Formula y) => Seq(x, Sp, Eq, Sp, y);
    private static Formula Ne(Formula x, Formula y) => Seq(x, Sp, Neq, Sp, y);
    private static Formula Neg(Formula x) => C("neg", x);
    private static Formula Add(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Add, y);
    private static Formula Mul(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Multiply, y);
    private static Formula E(Formula x) => C("ZMod.stdAddChar", x);
    private static Formula Pair(Formula x, Formula s) => C("pairPeriod", x, s);
    private static Formula Quarter(Formula x, Formula i, Formula s) => C("quarterPeriod", x, i, s);
    private static Formula Sign() => C("Or", Eqn(V("s"), D(1)), Eqn(V("s"), Neg(D(1))));
    private static Formula WithModulus(Formula body) => All("N", Nats(),
        C("Implies", C("Lt", D(0), V("N")), body));
    private static Formula PairFormula() => Disp(WithModulus(All("a", Ring(), All("s", Complexes(),
        Eqn(Pair(V("a"), V("s")), Add(E(V("a")), Mul(V("s"), E(Neg(V("a"))))))))));
    private static Formula QuarterFormula() => Disp(WithModulus(All("a", Ring(), All("i", Ring(),
        All("s", Complexes(), Eqn(Quarter(V("a"), V("i"), V("s")),
            Add(Pair(V("a"), D(1)), Mul(V("s"), Pair(Mul(V("i"), V("a")), D(1))))))))));
    private static Formula ResultFormula()
    {
        var pair = All("s", Complexes(), C("Implies", Sign(), Ne(Pair(V("a"), V("s")), D(0))));
        var quarter = All("i", Ring(), C("Implies",
            Eqn(new Formula.Power(V("i"), D(2)), Neg(D(1))), All("s", Complexes(),
                C("Implies", Sign(), Ne(Quarter(V("a"), V("i"), V("s")), D(0))))));
        var domain = C("And", C("Le", D(3), V("N")), C("Odd", V("N")));
        return Disp(All("N", Nats(), C("Implies", domain, All("a", Ring(), All("ainv", Ring(),
            C("Implies", Eqn(Mul(V("a"), V("ainv")), D(1)), C("And", pair, quarter)))))));
    }
}
