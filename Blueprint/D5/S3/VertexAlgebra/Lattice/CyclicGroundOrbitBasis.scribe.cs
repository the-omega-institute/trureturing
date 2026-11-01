using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.Lattice;

internal sealed class CyclicGroundOrbitBasisDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Phase-filtered charged-ground orbit vectors for an actual finite-order cyclic lattice lift.",
        H("Cyclic Ground Orbit Fixed Vectors"),
        Blocks(
            Paragraph(Text(
                "For an actual lattice isometry g of finite order, CyclicIsometryLift supplies a sign-character correction on the existing Carrier. The phase-filtered charged-ground orbit is the finite sum of the corrected operator powers applied to the literal norm-four ground vector. Because the corrected operator has the stated period, the geometric-sum identity makes this vector fixed.")),
            Describe.Lean(
                DescribeId.Create("cyclicgroundorbitbasis-actual-normfour-phase-filtered-orbit-fixed"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Lattice/CyclicGroundOrbitBasis.actual_normFour_phase_filtered_orbit_fixed"),
                H("Actual phase-filtered norm-four orbit fixed vector"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every lattice datum D, bilinear-preserving additive isometry g, positive period m and periodicity proof, there exists a charge character chi such that the complete m-term corrected orbit sum of every actual norm-four charge ground vector belongs to the corrected fixed submodule. The theorem is an actual Carrier statement and does not assert orbit independence or a shell cardinality."))),
                DescribeRole.Theorem),
            Paragraph(Text(
                "The proof is a finite geometric telescoping identity on the existing actual Carrier. The cyclic lift theorem supplies the correction and its exact m-th power identity; no replacement coordinate module, enumeration, positivity premise or numerical shell count is introduced.")))));
}
