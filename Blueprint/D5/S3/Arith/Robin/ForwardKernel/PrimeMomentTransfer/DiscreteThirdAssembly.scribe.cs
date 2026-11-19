using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer;

internal sealed class DiscreteThirdAssemblyDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/DiscreteThirdAssembly.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Normalized discrete cubic moments vanish uniformly for supported bounded variation weights.",
        H("Uniform discrete cubic moments"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("eventual-discrete-third"),
                DeclarationHandle.Create(Prefix + "eventual_discrete_third"),
                H("Uniform decay over polynomial length bands"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let zero be less than alpha, alpha less than beta, and beta less than one third. "
                        + "Assume the singular series equals one on the empty set and on every singleton, "
                        + "satisfies the three-point mean-square correlation bound at exponent beta, "
                        + "and satisfies the interval correlation estimates. Fix an endpoint window M at least one. "
                        + "For every positive delta, all sufficiently large real N have the following property: "
                        + "for every natural length H between N to the power alpha and N to the power beta, "
                        + "every supported bounded variation weight w with bound B, and every three intervals "
                        + "in the endpoint window, the absolute weighted discrete cubic sum divided by "
                        + "N times (H log N) to the power three halves is at most B delta. "
                        + "The threshold is independent of H, B, w, and all interval endpoints.")),
                    Paragraph(Text(
                        "The arithmetic transfer error and the integrated formal cubic envelope give "
                        + "the bound (C1+C2) B times the sum of the correlation modulus, "
                        + "the square root of log N divided by H, and "
                        + "N to the power minus one half plus epsilon times H to the power three halves "
                        + "times log N to the power minus three halves. Choose epsilon positive and less than "
                        + "one half minus three halves times beta. Each of the three rates is eventually at most "
                        + "delta divided by three times (C1+C2+1), uniformly in H. "
                        + "The integral envelope, normalization identity, and rate estimates are supplied by "
                        + "integrated_third_envelope, arithmetic_ratio_three, sqrt_rate, "
                        + "arithmetic_rate_three, and antitone_modulus_rate."))),
                DescribeRole.Theorem))));
}
