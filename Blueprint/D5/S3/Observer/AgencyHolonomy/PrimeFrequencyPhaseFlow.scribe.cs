using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.AgencyHolonomy;

internal sealed class PrimeFrequencyPhaseFlowDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Observer/AgencyHolonomy/PrimeFrequencyPhaseFlow.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Fourier characters supply unitary log-frequency time flow while scalar phase products erase sequence order.",
        H("Prime-Frequency Fourier Phase Flow"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("fourier-phase"),
                DeclarationHandle.Create(Prefix + "fourierPhase"),
                H("Fourier phase character"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Evaluate the complex character exp(-i times time times frequency). "
                        + "This is the unit-circle kernel underlying finite Fourier synthesis."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("log-address-phase"),
                DeclarationHandle.Create(Prefix + "logAddressPhase"),
                H("Logarithmic address phase"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Specialize the frequency to the real logarithm of a natural-number "
                        + "address. Prime addresses recover the oscillatory phase in a local "
                        + "Euler channel."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("finite-fourier-synthesis"),
                DeclarationHandle.Create(Prefix + "finiteFourierSynthesis"),
                H("Finite Fourier synthesis"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Sum finitely many complex amplitudes multiplied by their Fourier phase "
                        + "characters at a common time parameter."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("ordered-phase-product"),
                DeclarationHandle.Create(Prefix + "orderedPhaseProduct"),
                H("Listed scalar phase product"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Multiply the scalar phase characters attached to a listed sequence of "
                        + "frequencies."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("fourier-phase-character-laws"),
                DeclarationHandle.Create(Prefix + "fourier_phase_character_laws"),
                H("Time-frequency character laws"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The phase at zero time is one. Addition in time and addition in "
                            + "frequency both become multiplication of phases, and every phase "
                            + "has unit norm.")),
                    Paragraph(Text(
                        "The kernel is symmetric in the numerical time-frequency pairing. This "
                            + "does not identify their semantic roles in an observer model."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("ordered-phase-product-collapse"),
                DeclarationHandle.Create(Prefix + "ordered_phase_product_collapse"),
                H("Scalar phase products forget order"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The product along a listed frequency sequence equals the single phase "
                            + "whose frequency is the list sum. The scalar phase layer therefore "
                            + "retains total frequency and discards sequence order.")),
                    Paragraph(Text(
                        "Observable chronology requires an additional memory-bearing or "
                            + "noncommutative lift, such as the holonomy updates developed by "
                            + "the preceding truth sources."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("finite-fourier-synthesis-laws"),
                DeclarationHandle.Create(Prefix + "finite_fourier_synthesis_laws"),
                H("Finite synthesis shift and norm laws"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "A time shift multiplies each spectral channel by its shift phase. The "
                            + "norm of the synthesized signal is at most the sum of its amplitude "
                            + "norms because all phase factors are unitary.")),
                    Paragraph(Text(
                        "No inversion theorem, Plancherel identity, time orientation, "
                            + "irreversibility, prime-zero domination, or zero-location theorem "
                            + "is asserted."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Observer/AgencyHolonomy/FiniteHolonomyEnergy")),
        ]));
}
