using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.WeylChronology;

internal sealed class ClosedPathChronologyAmbiguityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/WeylChronology/ClosedPathChronologyAmbiguity.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact endpoint closure can hide a differential phase large enough to erase chronology.",
        H("Closed-Path Chronology Ambiguity"),
        Blocks(
            Paragraph(Text("This is a candidate mathematical audit of the existing compensation model. It does not claim an external open problem solved, experimental advantage, or a Lean compilation verdict.")),
            Describe.Lean(DescribeId.Create("phase-error-vector"),
                DeclarationHandle.Create(Prefix + "phaseErrorVector"), H("Attaining error vector"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A perpendicular half-error vector realizes any specified real phase at a nonzero endpoint."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("closed-error-phase"),
                DeclarationHandle.Create(Prefix + "closed_error_phase"), H("Closed differential error"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Opposite pre/post errors give zero final displacement and phase Y hx - X hy."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("closed-phase-energy-identity"),
                DeclarationHandle.Create(Prefix + "closed_phase_energy_identity"), H("Exact quadratic remainder"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The squared radial component is the exact remainder between the norm bound and the squared symplectic phase."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("closed-phase-energy-bound"),
                DeclarationHandle.Create(Prefix + "closed_phase_energy_bound"), H("Necessary phase budget"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Squared phase is bounded by squared endpoint norm times squared half-error norm."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("phase-error-vector-exact"),
                DeclarationHandle.Create(Prefix + "phase_error_vector_exact"), H("Attainment"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The constructed vector realizes the phase and saturates the bound. This supplies necessity and sufficiency, rather than only an inequality."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("bounded-closed-phase-iff"),
                DeclarationHandle.Create(Prefix + "bounded_closed_phase_iff"), H("Exact real-phase threshold"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A real phase eta is attainable with squared budget R exactly when eta squared is at most (X squared + Y squared) R."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("closed-error-word-normal-form"),
                DeclarationHandle.Create(Prefix + "closed_error_word_normal_form"), H("Actual closed action"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The existing word action becomes a pure phase on every wavefunction. No Gaussian-state assumption is needed."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("bounded-real-phase-collision-iff"),
                DeclarationHandle.Create(Prefix + "bounded_real_phase_collision_iff"), H("Sharp collision threshold"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Two unwrapped phases admit identical acquired phases exactly when their squared gap is at most four times the squared endpoint norm times the per-half squared budget. The nuisance records may differ between hypotheses."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("same-inventory-bounded-action-collision"),
                DeclarationHandle.Create(Prefix + "same_inventory_bounded_action_collision"), H("Complete action ambiguity"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For histories with the same inventory, bounded differential errors can make the entire actions identical. Repetition at this fixed setting cannot repair that collision. Shared nuisance and adaptive changes of control settings are not covered."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("distinct-legal-factors-closed-action-collision"),
                DeclarationHandle.Create(Prefix + "distinct_legal_factors_closed_action_collision"), H("Legal golden failure certificate"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The actual LSLL and LLSL factors admit identical full actions at squared half-error budget a squared/10 when both displacement amplitudes equal a. This does not contradict the earlier matched-half theorem."))), DescribeRole.Theorem))));
}
