using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.FourierFibers;

internal sealed class FinitePronyKoopmanObservationBridgeDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ObserverMemory/FourierFibers/"
            + "FinitePronyKoopmanObservationBridge.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite Prony moments and shifted Hankel entries are exactly the existing "
            + "diagonal spectral-fiber observations and delay coordinates.",
        H("Finite Prony to Koopman Observation Bridge"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("finite-prony-moment-is-crystal-time-sample"),
                DeclarationHandle.Create(
                    Prefix + "finite_prony_moment_eq_crystal_time_sample"),
                H("A Prony moment is a scalar spectral-fiber time sample"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The finite Prony moment and the repository's crystalTimeSample have "
                            + "the same weighted power-sum definition. The equality identifies "
                            + "the rational-transfer and observer-dynamics views without adding "
                            + "another time-sampling API."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("finite-prony-hankel-entry-is-transported-delay-sample"),
                DeclarationHandle.Create(
                    Prefix + "finite_prony_shifted_hankel_entry_eq_transported_sample"),
                H("A shifted Hankel entry is a transported delay-coordinate sample"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "A Hankel entry at row and column delays is the scalar observation at "
                            + "their summed delay after the hidden amplitudes have undergone the "
                            + "requested diagonal spectral-fiber time shift.")),
                    Paragraph(Text(
                        "Thus the shifted Hankel family is a finite Koopman-style delay table "
                            + "for the same hidden modal transport."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("finite-prony-first-window-faithful"),
                DeclarationHandle.Create(
                    Prefix + "finite_prony_first_window_injective"),
                H("Separated modes give a faithful first Prony delay window"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "When the modal nodes are distinct, the first matching number of Prony "
                            + "moments uniquely determines the hidden amplitude vector.")),
                    Paragraph(Text(
                        "The proof reuses the frozen finite crystal-time observability theorem. "
                            + "It makes no infinite-delay, continuous-spectrum, or noisy "
                            + "embedding claim."))),
                DescribeRole.Theorem)),
        []));
}
