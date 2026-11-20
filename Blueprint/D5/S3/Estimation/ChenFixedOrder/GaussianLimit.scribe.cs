using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Estimation.ChenFixedOrder;

internal sealed class GaussianLimitDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Estimation/ChenFixedOrder/GaussianLimit.";
    private static Formula V(string name) => F.Id(name);
    private static Formula Real => Seq(Mathbb, Grp(V("R")));
    private static Formula Gaussian => Seq(Operatorname, Grp(V("standardGaussian")));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A Gaussian limit for the balanced-sign estimator under uniform fixed-size sampling.",
        H("Gaussian limit for balanced finite populations"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("chen-baseline-gaussian"),
                DeclarationHandle.Create(Prefix + "standardGaussian"),
                H("Standard Gaussian probability law"),
                StatementSource.FromAuthor(Disp(Seq(
                    Gaussian, Sp, Colon, Sp, Call("ProbabilityMeasure", Real), Comma, Sp,
                    Open, Gaussian, Sp, Colon, Sp, Call("Measure", Real), Close, Sp, Eq, Sp,
                    Call("gaussianReal", D(0), D(1))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("This is the Gaussian limit of the balanced-sign estimator."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("chen-uniform-subset-gaussian-limit"),
                DeclarationHandle.Create(Prefix + "uniformSampleLaw_tendsto"),
                H("Estimator law on uniform subsets"),
                StatementSource.FromAuthor(Disp(Call("Tendsto",
                    Seq(V("m"), Sp, Mapsto, Sp, Call("map", Call("uniformSampleMeasure", V("m")),
                        Call("estimator", V("m")))),
                    Seq(Operatorname, Grp(V("atTop"))), Call("nhds", Gaussian)))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "With replacement, the uniform label law gives each sign probability 1/2. "
                        + "The centered estimator is the normalized partial sum in the independent "
                        + "central limit theorem along the square sample sizes.")),
                    Paragraph(Text(
                        "The union bound over distinct position pairs bounds the probability of "
                        + "a repeated label by the square of the sample size divided by the population size. "
                        + "This tends to zero, and conditioning on distinct labels changes each bounded "
                        + "test expectation by at most twice its bound times the collision probability.")),
                    Paragraph(Text(
                        "Erasing order takes the conditioned draw law to the uniform law on fixed-size "
                        + "subsets and preserves the estimator on distinct draws. Thus the Gaussian limit "
                        + "passes to the uniform subset law."))),
                DescribeRole.Theorem))));
}
