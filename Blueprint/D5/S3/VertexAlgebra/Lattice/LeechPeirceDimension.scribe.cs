using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.Lattice;

internal sealed class LeechPeirceDimensionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The complete ordinary fixed energy-two one-sixteenth eigenspace is counted by the actual positive pairing-one shell fiber, giving 47104 for an explicit Golay Leech axis.",
        H("The Ordinary Leech One-Sixteenth Multiplicity"),
        Blocks(
            Paragraph(Text("Let D be positive definite even integral charge data with no norm-two charge, "
                + "and let B(a,a)=4. Write S for the literal intersection of fixedSpace(D) with eigenvalue two "
                + "of sugawaraMode(D,inverse gramComplex(D),0), and L for the actual mode(D,a,1,0). "
                + "The eigenspace considered here is the intersection of S with the ambient eigenvalue-one-sixteenth "
                + "space of L. All oscillator and charge sectors of S are included.")),
            Describe.Lean(
                DescribeId.Create("actual-one-sixteenth-finrank"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Lattice/LeechPeirceDimension.actual_one_sixteenth_finrank"),
                H("A whole-space dimension formula"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/VertexAlgebra/bakalovkac2004lattice"),
                    LibraryNoteRef.Create("D5/L/VertexAlgebra/flm1988monster")),
                Blocks(Paragraph(Text("For every such D and a, the complex finrank of S intersect eigenspace(L,1/16) "
                    + "equals Nat.card of the entire norm-four charge fiber B(a,b)=1. No count or finite-model "
                    + "hypothesis occurs in this formula."))), DescribeRole.Theorem),
            Paragraph(Text("The complete actualFixedEnergyTwoBasis consists of neutral unordered colour pairs "
                + "and norm-four sign orbits, whose charged vector is E(b)=single(b,1)+single(-b,1). "
                + "The character chi fixes neutral basis vectors and multiplies E(b) by the parity sign of B(a,b). "
                + "For odd pairing, b cannot equal a or -a. The rootless norm-four bound then forces B(a,b)=1 or -1, "
                + "and the actual middle action gives L E(b)=E(b)/16. The odd-orbit vectors are linearly independent "
                + "as a subfamily of the full basis.")),
            Paragraph(Text("For completeness, set P=(I-chi)/2 on S, with values in the actual carrier. "
                + "Its values on the full basis are zero on even vectors and the original vector on odd ones; "
                + "therefore its entire image lies in the odd-orbit span. The existing whole-space spectral-sign "
                + "identity chi=I-(8192/217)L(L-I/2)(L-2I) evaluates to chi(v)=-v whenever L(v)=v/16. "
                + "Such a v equals P(v), so every vector of the full one-sixteenth eigenspace lies in that span. "
                + "Conversely the middle action places every odd basis vector in the eigenspace. Each odd sign orbit "
                + "has exactly one representative with positive pairing one, proving the dimension formula.")),
            Describe.Lean(
                DescribeId.Create("actual-leech-one-sixteenth-dimension"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Lattice/LeechPeirceDimension.actual_leech_one_sixteenth_dimension"),
                H("The explicit actual Golay Leech axis has multiplicity 47104"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/VertexAlgebra/bakalovkac2004lattice"),
                    LibraryNoteRef.Create("D5/L/VertexAlgebra/flm1988monster")),
                Blocks(Paragraph(Text("There exist actual positive even unimodular rank-twenty-four data D, "
                    + "an integral linear equivalence e to the real Golay Leech lattice preserving every pairing, "
                    + "and a norm-four charge a whose raw real coordinates are (4,4,0,...,0), such that the literal "
                    + "intersection fixedSpace(D) intersect eigenspace(sugawaraMode(D,inverse gramComplex(D),0),2) "
                    + "intersect eigenspace(mode(D,a,1,0),1/16) has complex dimension 47104. "
                    + "The theorem also retains rootlessness and the exact real coordinate identity."))), DescribeRole.Theorem),
            Paragraph(Text("The complete coordinate-compatible shell equivalence from LeechLowSpectrum is used "
                + "to pull back the sphere point supplied by LeechMinimalCount.sphereEquiv: support {0,1}, with "
                + "both signs zero. Its literal raw vector is single(0,4)+single(1,4). The real lattice stores these "
                + "raw cast coordinates and pairs by dot product divided by eight; equivalently its standard "
                + "Euclidean coordinates are divided by square root of eight. Full pairing compatibility identifies "
                + "B(a,b)=1 with dot(raw(a),raw(b))=8 on every admissible square-sum-thirty-two integer vector. "
                + "LeechAxisDistribution.axis_distribution counts this entire unbounded fiber as 47104. "
                + "No transitivity, assumed incidence, selected finite shell or inference from total shell size is used.")),
            Paragraph(Text("The lattice Fock construction follows Bakalov-Kac and Frenkel-Lepowsky-Meurman. "
                + "The norm-four Virasoro formula retains the Dong-Mason-Zhu attribution described in the imported "
                + "NormFourVirasoroVector source. The statement concerns the ordinary theta-fixed space and its "
                + "actual zero mode. It asserts no twisted-sector completion, reflection orbifold, Monster action "
                + "or string-theoretic identification.")))));
}
