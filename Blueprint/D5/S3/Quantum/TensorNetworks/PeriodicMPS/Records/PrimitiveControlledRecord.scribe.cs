using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks.PeriodicMPS.Records;

internal sealed class PrimitiveControlledRecordDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/PeriodicMPS/Records/PrimitiveControlledRecord";
    private const string Title = "The controlled channel of the primitive periodic collision";
    private static LibraryNoteRef CollisionSource =>
        LibraryNoteRef.Create("D5/L/Geometry/critchmorton2014mps");
    private static LibraryNoteRef DiamondSource =>
        LibraryNoteRef.Create("D5/L/QuantumChannels/watrous2009completelybounded");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The common adjacent-pair state and the exact separation of two address-retaining channels.",
        H(Title),
        Blocks(
            Paragraph(Text(
                "The address values 0 and 1 select the false and true cores of the checked primitive "
                + "periodic binary bond-two collision. Flatten the normalized ring amplitudes using sites "
                + "zero and one as the visible row index and the remaining m sites as the hidden column "
                + "index. The total ring length is n = 2 + m. The channel statements use m ≥ 5.")),
            Claim("records_common_visible", "Both records reduce to the same adjacent pair",
                "For m ≥ 5, the reduction of either record onto the adjacent pair is the common "
                + "trace-one collisionMarginal. The supplier collisionFlattening_common_visible uses "
                + "PeriodicMPSPrimitiveCollision.primitive_two_site_collision at n = 2 + m.",
                AssessedProvenance.FromRepo(CollisionSource)),
            Claim("records_cross", "The cross reduction of the literal record pair",
                "For each m, the zero record times the adjoint of the one record is the matrix "
                + "collisionNormalizedCross(m) from PeriodicMPSPrimitiveCollisionOverlap, by "
                + "collisionFlattening_cross. Write Cₘ for this matrix."),
            Claim("jointChannel_eq_partialTrace", "The joint channel is the actual partial trace",
                "The controlled isometry prepares the normalized periodic ring while keeping the "
                + "address. Tracing out the last m sites gives jointChannel on the address and first two sites."),
            Claim("dephasedChannel_apply", "The comparator completely dephases the address",
                "For each address matrix X, dephasedChannel gives diagonal blocks Xᵢᵢ collisionMarginal "
                + "and zero off-diagonal blocks."),
            Claim("jointChannel_coherence", "The retained address and pair carry cross coherence",
                "The (0,1) address block of jointChannel applied to X is X₀₁ Cₘ on the observed pair."),
            Claim("visible_pair_agrees", "The adjacent-pair observer sees the same state",
                "For every address matrix X, discarding the address from either readout yields "
                + "tr(X) collisionMarginal. On every density input the adjacent pair is therefore "
                + "exactly the same for both channels."),
            Claim("address_coherence", "The address alone carries the scalar overlap",
                "For every m and address matrix X, tracing out the visible pair in the joint readout "
                + "gives the (0,1) entry collisionNormalizedOverlap(2 + m) X₀₁."),
            Claim("amplified_bound", "The operational bound holds with every finite reference",
                "For m ≥ 5 and every joint input matrix X with a finite reference with decidable equality, "
                + "the trace norm of the amplified channel difference is at most ‖Cₘ‖₁‖X‖₁."),
            Claim("plus_attains", "A balanced address input attains the separation",
                "The balanced address projector gives readout outputs separated by ‖Cₘ‖₁ in "
                + "trace norm without a reference."),
            Claim("product_attains", "An arbitrary reference state preserves attainment",
                "For m ≥ 5 the product of the balanced address projector and any finite reference "
                + "density state attains an amplified output separation of ‖Cₘ‖₁."),
            Claim("jointChannel_distance", "Exact unhalved diamond distance at each ring length",
                "At every ring length n = 2 + m ≥ 7, the unhalved diamond distance from "
                + "jointChannel to dephasedChannel is ‖Cₘ‖₁. This evaluates the supremum with finite "
                + "references for the actual primitive collision. Critch and Morton supply the MPS "
                + "marginal setting, and Watrous supplies the distance convention.",
                AssessedProvenance.FromRepo(CollisionSource, DiamondSource)),
            Claim("reconstruction_lower", "An adjacent-pair-only prediction has a worst-case error",
                "For the balanced address input, any single proposed joint output has maximum "
                + "trace-norm error at least ‖Cₘ‖₁/2 across the two readout maps. With m ≥ 5, "
                + "their identical adjacent-pair output gives the same data to a prediction rule "
                + "that only has access to that pair."),
            Paragraph(Text(
                "The ring length is a size parameter. A physical preparation or evolution and any "
                + "heat or work assertion require separate assumptions.")))));

    private static DocumentBlock Claim(string name, string title, string prose,
        AssessedProvenance? provenance = null) =>
        Describe.Lean(DescribeId.Create("primitive-controlled-record-" + name.ToLowerInvariant().Replace('_', '-')),
            DeclarationHandle.Create(Module + "." + name), H(title), StatementSource.WithoutFormula(),
            provenance ?? AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);
}
