using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Covering;

internal sealed class Erdos203LatticeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Constructive rectangular transversals identify the exact indices of the six-row and seven-row homogeneous kernels.",
        H("Original base lattices and full-period geometry"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("erdos203-erdos203lattice-latticemap"),
                DeclarationHandle.Create("D5/S3/Arith/Covering/Erdos203Lattice.latticeMap"),
                H("Triangular lattice map"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The additive homomorphism maps (u,v) to (A u + C v,D v)."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("erdos203-erdos203lattice-sixlattice"),
                DeclarationHandle.Create("D5/S3/Arith/Covering/Erdos203Lattice.sixLattice"),
                H("Six-row homogeneous lattice"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The image of latticeMap 360 228 24 has basis columns (360,0),(228,24)."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("erdos203-erdos203lattice-sevenlattice"),
                DeclarationHandle.Create("D5/S3/Arith/Covering/Erdos203Lattice.sevenLattice"),
                H("Seven-row homogeneous lattice"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The image of latticeMap 3960 3108 24 has basis columns (3960,0),(3108,24)."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("erdos203-erdos203lattice-latticecoset"),
                DeclarationHandle.Create("D5/S3/Arith/Covering/Erdos203Lattice.latticeCoset"),
                H("Rectangular quotient representatives"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For q in Fin A times Fin 24, latticeCoset A C is the quotient class of the corresponding integer pair modulo the image of latticeMap A C 24."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("erdos203-erdos203lattice-0"),
                DeclarationHandle.Create("D5/S3/Arith/Covering/Erdos203Lattice.base_lattice_geometry"),
                H("Kernel geometry"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The seven-row kernel has basis (3960,0),(3108,24). The six-row and seven-row rectangles are complete transversals with indices 8640 and 95040. Both kernels contain every translate by the original period in either coordinate."))),
                DescribeRole.Theorem)),
        []));
}
