using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.PureState;

internal sealed class PhaseRecordRelaxationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Orthogonality makes the diagonal budget sharp in the effect relaxation.",
        H("Effects attaining a feasible diagonal profile"),
        Blocks(
            Describe.Lean(DescribeId.Create("phase-memory-relaxed-effects-attainment"),
                DeclarationHandle.Create("D5/S3/Quantum/PureState/PhaseRecordRelaxation.relaxed_effects_attain"),
                H("Every feasible profile attains its relaxed score for flat orthogonal phases"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Sandwich each normalized phase effect by the diagonal matrix with entries √dᵢ. Column orthogonality gives sum diag(d), hence a positive family with total effect bounded by the identity and total trace at most M. For each of the N labels, the phases cancel in the rank-one pairing and the score is the square of the profile value divided by N. Common-channel realizability is addressed separately by the finite Fourier construction."))),
                DescribeRole.Theorem))));
}
