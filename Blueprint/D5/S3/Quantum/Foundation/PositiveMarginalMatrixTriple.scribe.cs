using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Foundation;

internal sealed class PositiveMarginalMatrixTripleDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Quantum/Foundation/PositiveMarginalMatrixTriple.";
    private static readonly LibraryNoteRef Note =
        LibraryNoteRef.Create("D5/L/QuantumStates/barnumhilgert2019spectral");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A normalized positive spectator recovers both missing singleton marginals of one actual full-Hermitian triple.",
        H("Missing singleton marginals on one actual triple"),
        Blocks(
            Describe.Lean(DescribeId.Create("actual-triple-data"),
                DeclarationHandle.Create(Owner + "TripleMarginals"), H("Actual one-triple input in (24)"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Note),
                Blocks(Paragraph(Text("The fixed real-bilinear preparations are M from A times A into D and L from D times A into E, with full complex Hermitian carriers and canonical traces. Both preparations are positive on every pair of positive inputs. The actual primitive maps r, p12, p13 and p23 are positive on their entire source cones and trace preserving. The four all-vector readback identities are those of (24), with the same M in each pair output."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("recover-singleton-marginals"),
                DeclarationHandle.Create(Owner + "triple_recover"), H("Recover the two missing singleton marginals"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Note),
                Blocks(Paragraph(Text("Given Spans M and any positive c0 of trace one, take r2 = r composed with p23 composed with L(-,c0), as in (26). Its actual preparation readback is r2(M(x,y)) = tr(x)y, as in (27). Take r3 = r2 composed with p13. The trace factorization (25) and real spanning in D extend the calculated r3 readback on products to r3(L(d,c)) = tr(d)c for every d and c. The theorem returns Marginals M r r2 and Marginals L p12 r3, including global positivity and trace preservation for both recovered maps. To apply the binary structure results to L, supply Spans L. This proof covers singleton recovery on the given left triple. Orientation and abstract Euclidean Jordan classification are separate results."))),
                DescribeRole.Theorem))));
}
