using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaBridge;

internal sealed class FiniteOrbitBurnolPacketDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Weil/ZetaBridge/FiniteOrbitBurnolPacket.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finite separated nonreal off-line orbit frame admits one common unit peak and simultaneous finite-exception killers.",
        H("Simultaneous Orbit Burnol Packet"),
        Blocks(
            Describe.Lean(DescribeId.Create("frame-certificate-implies-actual-orbit-disjointness"),
                DeclarationHandle.Create(Prefix + "frame_orbits_pairwise_disjoint"),
                H("Frame node separation forbids orbit overlap"),
                StatementSource.FromAuthor(Disp(F.Id("i != j implies disjoint actual four-point zero orbits"))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Injectivity of the node equivalence excludes coincident selected frequencies, while sign separation excludes their negatives. The four symmetry images are checked explicitly, so disjointness is derived rather than an extra packet premise."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("simultaneous-orbit-burnol-packet-exists"),
                DeclarationHandle.Create(Prefix + "exists_orbitBurnolPacket"),
                H("The localization packet is constructed"),
                StatementSource.FromAuthor(Disp(F.Id("Nonempty (OrbitBurnolPacket F)"))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A common peak is interpolated to one on the actual target union. Closed-strip decay supplies a finite exceptional spectral ball. Each killer is then interpolated on that same ball to signed Kronecker data on the selected orbits and to zero on the rest. All packet fields are proved from existing analysis."))),
                DescribeRole.Theorem)), []));
}
