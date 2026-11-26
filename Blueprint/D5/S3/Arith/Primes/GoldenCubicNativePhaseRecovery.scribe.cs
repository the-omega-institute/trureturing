using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Primes;

internal sealed class GoldenCubicNativePhaseRecoveryDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A five-prime decoder is optimal for the native synchronized cubic observations.",
        H("Sharp phase recovery for the synchronized native cubic clock"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("native-phase-recovery"),
                DeclarationHandle.Create("D5/S3/Arith/Primes/GoldenCubicNativePhaseRecovery.native_phase_recovery"),
                H("Every positive native phase is recovered by five probes and no fewer"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Use the base-field scalar cubic readout on the image of the integer Lucas recurrence. On the specified 21-prime alphabet, the observations live in a recurrent 24-phase clock with one exceptional first-level word.")),
                    Paragraph(Text("The five readings at 5, 7, 47, 53 and 83 distinguish the first-level exception and recover every other level modulo 24. No four readings in that alphabet suffice; every separating set must read prime 47. The lower bound follows from a finite collision certificate and symbolic cardinality, not a prime-density argument. Replacing 53 by 109 recovers the common orientation without the separate calibrating probe 23.")),
                    Paragraph(Text("The checked result concerns literal Lucas levels and operational cubic observations. Identification with a candidate's global tame conductor character, the candidate-prime Chebotarev density, and Wall-Sun-Sun are not conclusions of this theorem."))),
                DescribeRole.Theorem))));
}
