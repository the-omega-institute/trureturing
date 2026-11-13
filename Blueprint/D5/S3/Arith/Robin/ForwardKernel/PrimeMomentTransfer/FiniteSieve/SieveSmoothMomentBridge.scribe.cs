using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.FiniteSieve;

internal sealed class SieveSmoothMomentBridgeDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SieveSmoothMomentBridge.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The weighted moment identity.",
        H("The weighted moment identity"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("sieve-weighted-moment-eq-raw"),
                DeclarationHandle.Create(Prefix + "sieve_weighted_moment_eq_raw"),
                H("The weighted moment identity"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every order k, squarefree positive modulus Q, positive natural h and family of smooth real weights compactly supported in (0,infinity), the complex cast of the uniform finite-sieve product moment equals kuperbergRawMoment(Q,h,f). Compact support restricts every sample sum to a finite set. Positive support makes all negative integer samples vanish, identifying weightedExponentialSum with its natural sample sum. The centred Ramanujan expansion removes precisely the divisor q=1. Splitting the positive phase of x+d and distributing finite products gives one divisor and one reduced residue for each weight. The uniform residue average retains exactly the tuples whose rational total frequency is integral. The character sum Q cancels the average denominator Q, with no additional density factor or conjugation."))),
                DescribeRole.Theorem))));
}
