using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arithmetic.HigherOrderFourier;

internal sealed class GowersU2FourierIdentityDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Arithmetic/HigherOrderFourier/GowersU2FourierIdentity.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Plancherel and autocorrelation diagonalization imply the finite U2 Fourier fourth-moment identity.",
        H("Finite U2 Fourier Fourth-Moment Identity"),
        Blocks(
            Def("autocorrelation", "additiveAutocorrelation", "Additive autocorrelation",
                "Each direction is assigned the summed multiplicative derivative correlation."),
            Def("system", "FiniteFourierPlancherelSystem", "Finite Fourier-Plancherel system",
                "A finite transform carries an explicit Plancherel scale and diagonalizes additive autocorrelation."),
            Def("fourth", "finiteFourierFourthMoment", "Scaled Fourier fourth moment",
                "Fourth powers of Fourier coefficient norms are summed with the Plancherel scale."),
            Thm("correlation", "finiteGowersU2Energy_eq_autocorrelation_norm", "U2 is autocorrelation energy",
                "The derivative definition of finite U2 is the squared norm sum of the autocorrelation function."),
            Thm("identity", "finiteGowersU2Energy_eq_fourierFourthMoment", "Fourier fourth-moment identity",
                "Plancherel and autocorrelation diagonalization convert finite U2 energy into the scaled coefficient fourth moment."),
            Thm("nonnegative", "finiteFourierFourthMoment_nonneg", "Fourier fourth moment is nonnegative",
                "A nonnegative Plancherel scale and fourth powers of norms give a nonnegative sum."),
            Thm("zero", "finiteGowersU2Energy_eq_zero_iff_fourier", "Positive-scale zero criterion",
                "With positive scale, zero U2 energy is equivalent to vanishing of every Fourier coefficient.")),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Arithmetic/HigherOrderFourier/GowersTranslationModulationInvariance")),
        ]));

    private static DocumentBlock.Describe Def(string id, string declaration, string heading, string paragraph) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(heading),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(paragraph))), DescribeRole.Definition);

    private static DocumentBlock.Describe Thm(string id, string declaration, string heading, string paragraph) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(heading),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(paragraph))), DescribeRole.Theorem);
}
