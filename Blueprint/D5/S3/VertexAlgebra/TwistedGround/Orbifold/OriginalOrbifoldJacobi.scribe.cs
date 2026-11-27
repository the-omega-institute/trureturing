using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.TwistedGround.Orbifold;

internal sealed class OriginalOrbifoldJacobiDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalOrbifoldJacobi.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Signed Jacobi Identities for the Original Orbifold Field",
        H("Signed Jacobi Identities for the Original Orbifold Field"),
        Blocks(
            Paragraph(Text("The fixed lattice vertex algebra supplies the all-fixed Jacobi law and fixed-sector skew. "
                + "The identities with three twisted states and with two twisted sources acting on a fixed state remain open "
                + "for the assembled field.")),
            Entry("divided-state", "divided_state_translation", "Divided translation of the source",
                "Iterating the rank-24 coefficient derivative on the source gives the signed binomial coefficient for each divided power."),
            Entry("divided-mode", "divided_mode_translation", "Divided translation of the input",
                "Iterating the rank-24 covariance relation moves translation across a mode as a finite binomial sum."),
            Entry("skew-mv", "skew_mv", "Twisted source and fixed input",
                "The original right coefficient is the signed sum of divided translates of the reversed fixed-action modes."),
            Entry("skew-vm", "skew_vm", "Fixed source and twisted input",
                "Reversing the finite signed translation sum collapses it to its zeroth diagonal by the binomial identity."),
            Entry("defect-vvm", "defect_vvm", "Two fixed sources and a twisted input",
                "The fixed-fixed-twisted Borcherds identity makes the signed coefficient defect vanish at every integer index."),
            Entry("defect-vmm", "defect_vmm", "Fixed source followed by two twisted states",
                "In rank 24, the original mixed coefficient law gives the three sums after inclusion into the fixed sector. "
                + "Lower truncation bounds the signed sum that uses the fixed action on the last twisted state."),
            Entry("defect-vmv", "defect_vmv", "Twisted state in the middle of two fixed states",
                "In rank 24, divided input translation and twisted-fixed skew exchange the last two slots. "
                + "Every resulting term has the fixed-fixed-twisted order."),
            Entry("defect-mvv", "defect_mvv", "Twisted state followed by two fixed states",
                "In rank 24, divided source translation and twisted-fixed skew exchange the first two slots "
                + "and reduce to the fixed-twisted-fixed identity."),
            Entry("defect-mvm", "defect_mvm", "Fixed state in the middle of two twisted states",
                "In rank 24, the first-slot exchange reduces the twisted-fixed-twisted identity to the fixed-twisted-twisted law."))));

    private static DocumentBlock Entry(string id, string declaration, string heading, string prose) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(heading), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);
}
