using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.FiniteSieve;

internal sealed class SieveSmoothingErrorDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SieveSmoothingError.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Positive averages of translated interval indicators approximate finite sieve sums in the fourth norm.",
        H("Positive averages of translated interval indicators approximate finite sieve sums in the fourth norm."),
        Blocks(
            Describe.Lean(
                DescribeId.Create("sieve-smoothing-norm4-bound"),
                DeclarationHandle.Create(Prefix + "sieve_smoothing_norm4_bound"),
                H("Uniform smoothing estimate"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Assume MSFinite and B>=1. There is C>=1 such that, "
                    + "for all sufficiently large real H, every modulus Q with "
                    + "P(Q)<=B log H, every 0<delta<=1, and all 0<=a<=b, "
                    + "the fourth norm of X_(a,b]/A_H-X_f/A_H is at most "
                    + "C*(sqrt(delta)+H^(-1/4)). The constant and the threshold "
                    + "are uniform in Q, delta, and the interval endpoints. "
                    + "The averaging estimate uses only nonnegativity, total mass one, "
                    + "the shift support, and the stated integrability properties "
                    + "of the normalized kernel."))),
                DescribeRole.Theorem))));
}
