using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Geometry.Permutohedra;

internal sealed class FaceLatticeDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Combinatorics/Geometry/Permutohedra/FaceLattice";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/FiniteGeometry/rossi2026permutohedron");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The permutohedron face lattice.",
        H("The permutohedron face lattice"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("facelattice-facesup-lub"),
                DeclarationHandle.Create(Module + ".faceSup_lub"),
                H("Join"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("A cut is a proper nonempty subset of the labels. A cut chain is a family of cuts totally ordered by inclusion. Faces order these chains by reverse inclusion, with a bottom below every chain. The least upper bound of two chains consists of their common cuts. Joining with bottom leaves the other face."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("facelattice-faceinf-glb"),
                DeclarationHandle.Create(Module + ".faceInf_glb"),
                H("Meet"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The greatest lower bound of two chains is the union of their cuts when the union is a chain. Otherwise it is bottom. The meet with bottom is bottom."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("facelattice-sup-cuts"),
                DeclarationHandle.Create(Module + ".sup_cuts"),
                H("Finite joins"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("When a finite join is a cut chain, a cut belongs to that chain exactly when it belongs to every member that lies above bottom. The empty join is bottom, whose rank is minus one."))),
                DescribeRole.Theorem))));
}
