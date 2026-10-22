using StrataLint.Scribe;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra;

internal sealed class LatticeHalfFockPhysicalGeneratorLocalityDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Background =
        LibraryNoteRef.Create("D5/L/VertexAlgebra/flm1988monster");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Physical current jet finite differences",
        H("Physical current jet finite differences"),
        Blocks(
            Paragraph(Text("All operators are the unrestricted original half-integer tensor currents and charged coefficient slices. No positive Gram form, rank constraint, inverse matrix or locality premise is introduced.")),
            Describe.Lean(
                DescribeId.Create("latticehalffockphysicalgenerator-ward"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeHalfFockPhysicalGeneratorLocality.physicalCurrent_charge_ward"),
                H("The original negative Ward shift gives the physical parity carry"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Background),
                Blocks(Paragraph(Text("The commutator at physical modes m and k is the original charge pairing times the opposite parity slice at mode k plus m plus parity. The cover law uses exponent minus two times m minus one. Increasing either physical input mode by one therefore produces exactly the same commutator, so one ordinary delta kills it."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticehalffockphysicalgenerator-jetcharged"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeHalfFockPhysicalGeneratorLocality.physicalJet_charge_locality"),
                H("The actual jet of order r has charged locality order r plus one"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Background),
                Blocks(Paragraph(Text("The proof uses the actual factorial-normalized jetScalar successor identity and a proved iterated finite-difference Leibniz identity. Multiplication by a linear mode factor raises an already established killing order by one. This is not an appeal to polynomial-degree intuition."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticehalffockphysicalgenerator-jetpair"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeHalfFockPhysicalGeneratorLocality.physicalJet_pair_locality"),
                H("The actual jet pair of orders r and s has locality order r plus s plus two"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Background),
                Blocks(Paragraph(Text("The tensor Heisenberg commutator retains support on m plus n plus one equal to zero and its coefficient m plus one half times the Gram entry. Its second difference is proved directly on that diagonal; the two jet orders are then added by the same finite-difference identity and the existing ordinary symmetry theorem. The source lattice VOA is bosonic throughout."))),
                DescribeRole.Theorem),
            Paragraph(Text("Full four-slot escape registration and publication are distinct from kernel checking. The larger twisted Jacobi, fusion, anomaly and string/AdS objectives remain open.")))));
}
