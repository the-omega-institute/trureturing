using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra;

internal sealed class OriginalAbsoluteGhostCompletenessDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/OriginalAbsoluteGhostCompleteness.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual finite original-Q HPL constructs relative representatives of unrestricted absolute degree-one cycles.",
        H("Absolute Ghost-One Representative Completeness"),
        Blocks(
            Describe.Lean(DescribeId.Create("absolute-cycle-physical-representative"),
                DeclarationHandle.Create(Prefix + "absolute_ghost_one_representative"),
                H("Explicit Same-Sector Ghost-Zero Preimage"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Start with any originalEnergySector Q-cycle in ghostPart one; there is no input antighost-kernel condition. The actual J0 commutators prove the finite inverse and inclusion preserve integral number degree and the transfer projection preserves it through its normalizer and Q-minus-delta factors. The existing private homotopy-degree supplier is consumed without changing its source or visibility. Native support proves B(0) of the projected state is zero. The actual on-shell B(0) inclusion compatibility makes I(R(state)) relative. The actual chain homotopy supplies state minus this representative equal to Q of energyHomotopy(state), in the same sector and degree zero. Both Gram inverses, critical rank, the exact null-frame equations and the original mass-shell condition remain explicit."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("absolute-other-degrees-boundaries"),
                DeclarationHandle.Create(Prefix + "other_ghost_cycle_boundary"),
                H("Actual Boundaries In Every Other Degree"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For any integer degree other than one and two, actual degree preservation and native coefficient support make R(state) zero. The same finite HPL identity gives the explicit same-sector degree-minus-one boundary preimage. This is not an off-shell contraction wrapper and does not assume completeness of a relative definition."))),
                DescribeRole.Theorem))));
}
