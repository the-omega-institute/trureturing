using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra;

internal sealed class OriginalAbsoluteGhostDoubletDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/OriginalAbsoluteGhostDoublet.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual singleton-three native branch computes the original degree-two on-shell quotient.",
        H("Transferred Absolute Up Realization"),
        Blocks(
            Describe.Lean(DescribeId.Create("actual-up-coordinate-recovery"),
                DeclarationHandle.Create(Prefix + "upState_coordinates"),
                H("Exact Native Up Coefficients"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a P-fixed original energy-sector state homogeneous of ghost degree two, the actual finite native support excludes the empty ghost branch. Every nonzero coefficient has singleton-three support, absent longitudinal powers and the required transverse level; site three contributes zero conformal energy. Finsupp comap and the full finite expansion therefore recover the exact state from upCoordinates. No supplied support or homogeneity of an abstract equivalence is assumed."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("actual-up-quotient-recovery"),
                DeclarationHandle.Create(Prefix + "upQuotient_right_inverse"),
                H("Original Quotient Completeness In Degree Two"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("upInput is built from actual native singleton-three words in the original sector and actual range P. upLift applies the actual finite transferred inclusion, which is a Q-cycle because the already computed transferred differential vanishes on the exact mass shell. J0 proves degree two. upReadout applies the actual transferred projection before reading up coordinates. The projection vanishes on original boundaries; the unrestricted-boundary intersection is supplied by AbsolutePhysicalNoGhost. The finite chain homotopy gives the explicit degree-one preimage of the difference. Together with upQuotient_left_inverse this defines nativeUpEquiv between transverse coefficients and the actual original degree-two ghostCohomology."))),
                DescribeRole.Theorem),
            Paragraph(Text("The up map uses original Q, native up words and the actual HPL inclusion. It does not assert that literal C(0) commutes with Q or acts on unrestricted cohomology without correction. Parameter and class-map adapters carry no independent novelty. Both Gram inverses, critical rank, exact adapted-null frame equations and original mass shell remain explicit; OriginalAbsoluteGradedSector constructs this frame internally. Raw Reg source bridges are not complete owning-interface registrations.")))));
}
