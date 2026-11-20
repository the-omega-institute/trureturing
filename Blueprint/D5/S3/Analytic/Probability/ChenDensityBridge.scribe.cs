using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Probability;

internal sealed class ChenDensityBridgeDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Analytic/Probability/ChenDensityBridge.";
    private static Formula V(string name) => F.Id(name);
    private static Formula Nat => Seq(Mathbb, Grp(V("N")));
    private static Formula Real => Seq(Mathbb, Grp(V("R")));
    private static Formula Parenthesized(Formula body) => Seq(Left, Open, body, Right, Close);
    private static Formula Typed(Formula value, Formula type) => Seq(value, Sp, Colon, Sp, type);
    private static Formula All(Formula name, Formula type) =>
        Seq(Forall, Sp, Typed(name, type), Comma, Sp);
    private static Formula AsMeasure(Formula law, Formula carrier) =>
        Parenthesized(Typed(law, Call("Measure", carrier)));
    private static Formula M => V("m");
    private static Formula G => V("g");
    private static Formula X => V("x");
    private static Formula A => V("A");
    private static Formula Sample => Call("Sample", M);
    private static Formula Uniform => Call("uniformSampleMeasure", M);
    private static Formula Baseline => Call("uniformEstimatorLaw", M);
    private static Formula Estimator => Call("estimator", M);
    private static Formula DensityArgs => Seq(All(M, Nat), All(G, new Formula.TypeArrow(Real, Real)));
    private static Formula MeasureIntegral(Formula integrand) =>
        Seq(Int, Sp, integrand, Sp, V("d"), Baseline);
    private static Formula Measurability => Call("Measurable", G);
    private static Formula Nonnegative => Parenthesized(Seq(All(X, Real), D(0), Sp, Leq, Sp, Call("g", X)));
    private static Formula Normalization => Seq(MeasureIntegral(Call("g", X)), Sp, Eq, Sp, D(1));
    private static Formula DensityHypotheses => Seq(
        Parenthesized(Typed(V("hg"), Measurability)), Sp,
        Parenthesized(Typed(V("hn"), Nonnegative)), Sp,
        Parenthesized(Typed(V("hm"), Normalization)));
    private static Formula Tilt => Call("tiltedSample", M, G, V("hg"), V("hn"), V("hm"));
    private static Formula Event => Call("inclusion", M, A);
    private static Formula OfReal(Formula value) => new Formula.Apply(
        Seq(Operatorname, Grp(V("ENNReal"), Dot, V("ofReal"))), [value]);
    private static Formula Map(Formula law) => Call("map", law, Estimator);

    private static Formula Specification() => new Formula.Aligned([
        Seq(All(Seq(M, Comma, V("r")), Nat), All(G, new Formula.TypeArrow(Real, Real)),
            Forall, Sp, DensityHypotheses, Comma),
        Seq(Parenthesized(Seq(All(V("i"), Nat), D(0), Sp, Lt, Sp, V("i"), Sp, Rightarrow, Sp,
            V("i"), Sp, Leq, Sp, V("r"), Sp, Rightarrow, Sp,
            MeasureIntegral(Seq(new Formula.Power(X, V("i")), Sp,
                Parenthesized(Seq(Call("g", X), Minus, D(1))))), Sp, Eq, Sp, D(0))),
            Sp, Rightarrow),
        Seq(Parenthesized(Seq(AsMeasure(Map(Tilt), Real), Sp, Eq, Sp,
            Call("withDensity", Baseline, Seq(X, Sp, Mapsto, Sp, OfReal(Call("g", X)))))), Sp, Land),
        Parenthesized(Seq(All(A, Call("Finset", Call("Population", M))),
            Call("card", A), Sp, Leq, Sp, V("r"), Sp, Rightarrow, Sp,
            new Formula.Apply(AsMeasure(Tilt, Sample), [Event]), Sp, Eq, Sp,
            new Formula.Apply(AsMeasure(Uniform, Sample), [Event])))
    ]);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Real density tilts on fixed-size samples preserve inclusion events up to the matched moment order.",
        H("Density tilts and exact inclusion probabilities"),
        Blocks(
            Describe.Lean(DescribeId.Create("chen-uniform-estimator-law"),
                DeclarationHandle.Create(Prefix + "uniformEstimatorLaw"),
                H("Underlying measure of the uniform estimator law"),
                StatementSource.FromAuthor(Disp(Seq(All(M, Nat),
                    Typed(Baseline, Call("Measure", Real)), Sp, Eq, Sp, AsMeasure(Map(Uniform), Real)))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The estimator maps uniform samples of the prescribed size to real observations."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("chen-tilted-sample"),
                DeclarationHandle.Create(Prefix + "tiltedSample"),
                H("Tilted probability law on the same samples"),
                StatementSource.FromAuthor(Disp(new Formula.Aligned([
                    Seq(DensityArgs, Forall, Sp, DensityHypotheses, Comma),
                    Seq(Typed(Tilt, Call("ProbabilityMeasure", Sample)), Comma),
                    Seq(AsMeasure(Tilt, Sample), Sp, Eq, Sp, Call("withDensity", AsMeasure(Uniform, Sample),
                        Seq(V("S"), Sp, Mapsto, Sp, OfReal(Call("g", Call("estimator", M, V("S")))))))
                ]))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Normalization against the uniform estimator law makes this lifted measure a probability measure."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("chen-density-tilt"),
                DeclarationHandle.Create(Prefix + "tiltedSample_spec"),
                H("Lifting a real density to the same finite sample space"),
                StatementSource.FromAuthor(Disp(Specification())),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Integrating on a real event under the pushforward of the tilted sample law gives the same integral as tilting the uniform estimator law by g.")),
                    Paragraph(Text("For a prescribed subset A, the finite sampling identity converts the restricted integral of the centered density into an integral against an inclusion polynomial of degree at most the cardinality of A. Normalization handles the constant coefficient. The centered moment equations handle every other coefficient. The resulting equality of event masses holds in ENNReal."))),
                DescribeRole.Theorem))));
}
