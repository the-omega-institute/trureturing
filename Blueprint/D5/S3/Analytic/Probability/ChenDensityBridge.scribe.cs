using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Probability;

internal sealed class ChenDensityBridgeDocument : IScribeDocumentDefinition
{
    private static Formula V(string name) => F.Id(name);
    private static Formula Nat => Seq(Mathbb, Grp(V("N")));
    private static Formula Real => Seq(Mathbb, Grp(V("R")));
    private static Formula All(string name, Formula type) =>
        Seq(Forall, Sp, V(name), Colon, Sp, type, Comma, Sp);
    private static Formula Integral(Formula integrand) =>
        Seq(Int, Sp, integrand, Sp, V("d"), Mu);
    private static Formula Event => Call("inclusion", V("A"));

    private static Formula Statement() => Disp(new Formula.Aligned([
        Seq(Forall, Sp, V("m"), Comma, V("r"), Colon, Nat, Comma, Sp,
            All("g", new Formula.TypeArrow(Real, Real)),
            Call("Measurable", V("g")), Sp, Rightarrow),
        Seq(Open, All("x", Real), D(0), Sp, Leq, Sp, Call("g", V("x")), Close, Sp, Rightarrow,
            Integral(Call("g", V("x"))), Eq, D(1), Sp, Rightarrow),
        Seq(Open, All("i", Nat), D(0), Sp, Lt, Sp, V("i"), Sp, Leq, Sp, V("r"), Sp, Rightarrow,
            Integral(Seq(new Formula.Power(V("x"), V("i")), Open, Call("g", V("x")),
                Minus, D(1), Close)), Eq, D(0), Close, Sp, Rightarrow),
        Seq(Call("map", V("X"), V("Q")), Eq,
            Call("withDensity", Mu, Seq(Operatorname, Grp(V("ofReal")), Sp, Circ, Sp, V("g"))),
            Sp, Land),
        Seq(Open, All("A", Call("Finset", Call("Population", V("m")))),
            Call("card", V("A")), Sp, Leq, Sp, V("r"), Sp, Rightarrow, Sp,
            Call("Q", Event), Eq, Call("P", Event), Close)
    ]));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Real density tilts on fixed-size samples preserve inclusion events up to the matched moment order.",
        H("Density tilts and exact inclusion probabilities"),
        Blocks(
            Describe.Lean(DescribeId.Create("chen-density-tilt"),
                DeclarationHandle.Create("D5/S3/Analytic/Probability/ChenDensityBridge.tiltedSample_spec"),
                H("Lifting a real density to the same finite sample space"),
                StatementSource.FromAuthor(Statement()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For stage m, P is uniform on Sample m, X is the common estimator, and the real law mu is map(X,P). The law Q on Sample m has density ofReal(g(X(S))) at a sample S relative to P. Normalization against mu makes Q a probability measure.")),
                    Paragraph(Text("Integrating on a real event under the pushforward of Q gives the same integral as tilting mu by g. For a prescribed subset A, the finite sampling identity converts the restricted integral of g(X)-1 into the integral of the centered density against an inclusion polynomial of degree at most card(A). The constant coefficient is controlled by normalization and the other coefficients by the centered moment equations. The resulting equality of event masses holds in ENNReal."))),
                DescribeRole.Theorem))));
}
