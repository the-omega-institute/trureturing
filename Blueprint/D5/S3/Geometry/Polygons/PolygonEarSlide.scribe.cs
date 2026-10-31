using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.Polygons;

internal sealed class PolygonEarSlideDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Geometry/Polygons/PolygonEarSlide.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual polygon ear-slide carrier and raw erase-insert map",
        H("Concrete polygon data"),
        Blocks(
            Describe.Lean(DescribeId.Create("polygon-ear-slide-carrier"),
                DeclarationHandle.Create(Prefix + "Carrier.IsTriangulation"), H("Actual maximal diagonal carrier"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The carrier uses unordered pairs of vertices in ZMod n. IsDiagonal is the internal segment condition, Cross is the cyclic endpoint crossing relation, and IsTriangulation contains diagonal, noncrossing, and maximality fields."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("polygon-ear-slide-swap-transport"),
                DeclarationHandle.Create(Prefix + "Actual.cross_chordSwap_of_avoidTwo"), H("Crossing transport away from the deleted centre"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The vertex permutation swaps labels 1 and 2. For chords whose endpoints avoid 2, the finite cyclic order proof transports both crossing witnesses through that permutation, including the cyclic seam."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("polygon-ear-slide-exclusion"),
                DeclarationHandle.Create(Prefix + "Actual.avoidTwo_of_mem_triangulation"), H("Ear-centre exclusion"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("An actual triangulation containing t={1,3} cannot contain an internal diagonal incident with 2: every such diagonal crosses t. The proof uses the actual maximal carrier and the local cyclic cases."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("polygon-ear-slide-raw-map"),
                DeclarationHandle.Create(Prefix + "Actual.phi"), H("Erase, swap, and insert"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("phi erases t={1,3}, maps every retained chord by the concrete vertex swap, and inserts s={0,2}. psi performs the inverse erase, swap, and insert operation."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("polygon-ear-slide-raw-inverse"),
                DeclarationHandle.Create(Prefix + "Actual.psi_phi"), H("Raw Finset inverse law"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Under actual source diagonal membership, t membership, and s exclusion, psi(phi T)=T. This is a complete Finset inverse law; triangulation preservation and the independent observed-trace fibre equivalence remain the next mathematical obligations."))),
                DescribeRole.Theorem)), []));
}
