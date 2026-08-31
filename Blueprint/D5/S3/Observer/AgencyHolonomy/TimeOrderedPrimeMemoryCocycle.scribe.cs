using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.AgencyHolonomy;

internal sealed class TimeOrderedPrimeMemoryCocycleDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Observer/AgencyHolonomy/TimeOrderedPrimeMemoryCocycle.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Fourier-timed prime events form an affine memory cocycle whose swap defect is prime curvature.",
        H("Time-Ordered Prime Memory Cocycle"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("timed-prime-memory-event"),
                DeclarationHandle.Create(Prefix + "TimedPrimeMemoryEvent"),
                H("Timed prime memory event"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A local event stores a scalar factor, a base memory injection, a real "
                        + "frequency, and a real Fourier time. Prime channels are obtained by "
                        + "using logarithmic prime frequency."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("time-ordered-memory-cocycle"),
                DeclarationHandle.Create(Prefix + "timeOrderedMemoryCocycle"),
                H("Time-ordered memory cocycle"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The memory summary weights an earlier event by the stable powers of all "
                        + "later slots and by the scalar factors accumulated before later "
                        + "injections. It is normalized at zero initial memory and unit scalar "
                        + "input."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("time-ordered-evolution"),
                DeclarationHandle.Create(Prefix + "timeOrderedEvolution"),
                H("Chronological affine evolution"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The event list acts from left to right. The list head acts first, so list "
                        + "order is an operational chronology distinct from the real Fourier "
                        + "time stored in each event."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("timed-injection-shift"),
                DeclarationHandle.Create(Prefix + "timed_injection_shift"),
                H("Fourier time translation of an injection"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Shifting the event time multiplies its effective injection by the Fourier "
                        + "character of the shift. This imports the additive time-character law "
                        + "without adding an arrow of time."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("time-ordered-evolution-affine"),
                DeclarationHandle.Create(Prefix + "time_ordered_evolution_affine"),
                H("Exact affine word action"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Every finite chronological word acts by a stable power on initial memory, "
                        + "the time-ordered memory cocycle on scalar input, and the commutative "
                        + "scalar word on the scalar coordinate."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("time-ordered-cocycle-append-laws"),
                DeclarationHandle.Create(Prefix + "time_ordered_cocycle_append_laws"),
                H("Twisted cocycle law under concatenation"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Scalar summaries multiply under list concatenation. Memory summaries "
                            + "obey the twisted law in which the suffix length transports the "
                            + "prefix memory by a stable power and the prefix scalar transports "
                            + "the suffix memory.")),
                    Paragraph(Text(
                        "The full affine evolution of a concatenated list is the composition of "
                            + "the prefix evolution followed by the suffix evolution."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("time-ordered-two-event-swap-curvature"),
                DeclarationHandle.Create(Prefix + "time_ordered_two_event_swap_curvature"),
                H("Two-event chronology defect"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Reversing two timed events leaves the scalar coordinate unchanged. The "
                        + "memory-coordinate difference is exactly the gauge-invariant prime "
                        + "swap curvature evaluated on their Fourier-rotated injections."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("timed-residual-two-event-swap"),
                DeclarationHandle.Create(Prefix + "timed_residual_two_event_swap"),
                H("Residual chronology with independent event times"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For residual local factors at possibly different Fourier times, the "
                        + "chronology defect is stable residual curvature evaluated on the two "
                        + "independently phase-rotated channels."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("common-time-residual-swap"),
                DeclarationHandle.Create(
                    Prefix + "common_time_residual_swap_recovers_phase_twisted_curvature"),
                H("Recovery of the common-time phase-twisted curvature"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "When the two event times coincide, the list-level chronology defect "
                        + "specializes exactly to the existing common-time phase-twisted stable "
                        + "swap curvature."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Observer/AgencyHolonomy/PrimeFrequencyPhaseFlow")),
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Observer/AgencyHolonomy/PrimeSwapCurvature")),
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Observer/AgencyHolonomy/PhaseTwistedStableSwapCurvature")),
        ]));
}
