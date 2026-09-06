using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.WeylChronology;

internal sealed class UniversalMagnusWeylPhaseBridgeDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Quantum/WeylChronology/UniversalMagnusWeylPhaseBridge.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The universal tensor and free-Lie chronology map to the same integer center that controls the concrete Weyl phase.",
        H("Universal Magnus to Weyl Phase"),
        Blocks(
            Paragraph(Text(
                "This is a representation adapter over existing owners. The current "
                    + "StepTwoFreeLieBridge already maps the universal primitive tensor "
                    + "logarithm to represented associative commutators and free-Lie "
                    + "brackets. BinaryParikhStepTwoBridge already identifies the canonical "
                    + "central matrix entry with the integer Magnus center. The Weyl lane "
                    + "already derives the phase a*b*m from the literal wavefunction action.")),
            Paragraph(Text(
                "The older draft PR #4504 was audited first. Its relevant tensor/free-Lie "
                    + "ideas have since evolved into stronger owners already present on the "
                    + "current stack, so this module consumes those owners rather than "
                    + "copying the stale draft definitions.")),
            Describe.Lean(
                DescribeId.Create("binary-universal-signature"),
                DeclarationHandle.Create(Prefix + "binaryUniversalSignature"),
                H("Canonical binary universal tensor signature"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The binary word is lifted through the existing chronological tensor signature using the canonical Parikh letter observation."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("universal-central-entry"),
                DeclarationHandle.Create(Prefix + "binary_universal_magnus_central_entry"),
                H("Universal primitive logarithm recovers the Magnus center"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Tensor multiplication maps the universal primitive logarithm to the represented doubled-Magnus matrix, whose central entry is exactly the existing integer m=2P-rz."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("universal-central-entry-real"),
                DeclarationHandle.Create(Prefix + "binary_universal_magnus_central_entry_real"),
                H("The central coordinate casts to the Weyl scalar"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Casting the represented universal central entry from integers to reals gives the exact scalar Magnus center used by the continuous displacement action."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("weyl-normal-form-universal"),
                DeclarationHandle.Create(Prefix + "run_word_normal_form_via_universal_magnus"),
                H("The Weyl normal form is a universal-Magnus representation"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The previously derived wavefunction normal form is rewritten so its geometric phase is controlled directly by the represented universal primitive tensor logarithm. No second chronology counter is introduced."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("free-lie-central-unit"),
                DeclarationHandle.Create(Prefix + "binary_free_lie_true_false_central_entry"),
                H("The elementary free-Lie bracket has unit central coefficient"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Under the canonical binary Parikh interpretation, the universal long-before-short free-Lie bracket evaluates to a matrix whose central entry is one."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("free-lie-weyl-swap"),
                DeclarationHandle.Create(Prefix + "two_letter_weyl_swap_phase_from_free_lie"),
                H("The free-Lie coefficient exponentiates to the Weyl swap phase"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For one long event followed by one short event, the concrete Weyl word differs from the reversed word by exp(i*2*a*b) raised through the unit central free-Lie coefficient.")),
                    Paragraph(Text(
                        "The factor two is the word-versus-reversal group-commutator phase. The count-compensated single-history protocol retains the half phase a*b*m."))),
                DescribeRole.Theorem),
            Paragraph(Text(
                "The bridge is finite and algebraic. It does not introduce unbounded "
                    + "infinitesimal generators, a completed free Lie algebra, a BCH "
                    + "convergence theorem, or a physical claim that every abstract "
                    + "chronology representation is realized by this oscillator control."))))));
}
