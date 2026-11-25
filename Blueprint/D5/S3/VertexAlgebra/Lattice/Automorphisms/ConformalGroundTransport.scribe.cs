// Apache-2.0.
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.Lattice.Automorphisms;

internal sealed class ConformalGroundTransportDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/Lattice/Automorphisms/ConformalGroundTransport.";
    private static readonly LibraryNoteRef LatticeSource =
        LibraryNoteRef.Create("D5/L/VertexAlgebra/bakalovkac2004lattice");
    private static readonly LibraryNoteRef VoaSource =
        LibraryNoteRef.Create("D5/L/VertexAlgebra/flm1988monster");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual conformal automorphisms recover integral charge isometries and transport charge ground lines.",
        H("Conformal Ground Transport on a Rootless Lattice VOA"),
        Blocks(
            Paragraph(Text("D is ordinary even integral LatticeData. The physical carrier is the actual finite-support charge direct sum of complex oscillator polynomials. The transport statements assume a real positive-definite Gram matrix hPos and rootlessness hRoot, namely no integral charge has bilinear norm two. For the chosen quadratic state omega(D,H), hHG states H * gramComplex(D) = 1. The reverse identity follows because H and gramComplex(D) are finite square complex matrices. A complex-linear automorphism U must preserve every integer vertex mode through hMode and fix omega(D,H) through hOmega.")),
            Paragraph(Text("The grade-one current basis is the rootless energy-one basis. The mode-one calculation reduces the product of two canonical currents to the neutral mode coefficient and gives (Y(currentState D i))[[1]] (currentState D j) = (D.G i j : ℂ) • vacuum D. Bilinearity then identifies arbitrary current mode-one products with the complex Gram form. The mode-zero coefficient theorem reads every coefficient of a state by its Gram pairing with that coefficient's charge, so the joint zero-mode eigenvalues determine the transported integral charge.")),
            Describe.Lean(
                DescribeId.Create("conformalgroundtransport-current"),
                DeclarationHandle.Create(Prefix + "current"),
                H("Complex linear combinations of canonical currents"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LatticeSource),
                Blocks(Paragraph(Text("The state current(D,x) is the finite complex linear combination of the canonical grade-one current states indexed by Fin(rank)."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("conformalgroundtransport-current-one-current"),
                DeclarationHandle.Create(Prefix + "current_one_current"),
                H("Mode-one current Gram identity"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LatticeSource, VoaSource),
                Blocks(Paragraph(Text("The actual neutral mode calculation gives the lattice Gram entry times the vacuum for every pair of basis currents. This is the invariant form recovered from the mode-one product."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("conformalgroundtransport-current-zero-coeff"),
                DeclarationHandle.Create(Prefix + "current_zero_coeff"),
                H("Current zero modes read charge"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LatticeSource),
                Blocks(Paragraph(Text("For every state coefficient q, the zero mode of current(D,x) multiplies that coefficient by the complex Gram pairing of x with q's integral charge. This supplies the joint spectral readout used below."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("conformalgroundtransport-charge"),
                DeclarationHandle.Create(Prefix + "conformal_charge_transport"),
                H("Recovered additive integral isometry"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LatticeSource, VoaSource),
                Blocks(Paragraph(Text("Under hPos, hRoot, hHG, hMode and hOmega, U induces a unique additive equivalence s of the actual charge lattice preserving bilinear. Every occupied coefficient of U(single(a,p)) has charge s(a), so s is recovered by the current zero-mode spectrum on the actual carrier. The nonzero image of each ground state determines the charge at that input."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("conformalgroundtransport-ground"),
                DeclarationHandle.Create(Prefix + "conformal_ground_transport"),
                H("Charge ground lines are transported"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LatticeSource, VoaSource),
                Blocks(Paragraph(Text("With the same hypotheses, each ground state single(a,1) is sent to a nonzero unit scalar times single(s(a),1). Preservation of the Sugawara grade and of the lattice norm forces oscillator energy zero in the image. The charge map is determined by the zero-mode labels, while eta records the remaining line scalar."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("conformalgroundtransport-projection"),
                DeclarationHandle.Create(Prefix + "conformal_ground_projection"),
                H("Conformal group actions project to the integral isometry group"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LatticeSource, VoaSource),
                Blocks(Paragraph(Text("For groups G and K, an injective additive identification mu from K into charge automorphisms must have range containing every bilinear isometry. A mode-preserving, omega-fixing representation U of G then yields a group homomorphism pi : G →* K and ground-line units eta with charge action mu(pi(g)). Composition of ground-line maps gives the group law for pi, because nonzero ground states at distinct charges have disjoint support."))),
                DescribeRole.Theorem),
            Paragraph(Text("This projection supplies the ground-line action in finite-group obstructions for the rootless lattice theory. The isometry-group identification and the twisted-sector lowest-weight conditions are separate inputs to those obstructions.")))));
}
