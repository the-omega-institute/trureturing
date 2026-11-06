// SOURCE STATUS: UNCOMPILED. Native emit, handle resolution and rendered fidelity are pending.
using StrataLint.Engine;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.FiniteCriticalCellSphere;

internal sealed class CertificateSphereDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Geometry/FiniteCriticalCellSphere/CertificateSphere.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        DocumentHeader.Create(
            GidRef.Create("D5/S3/Geometry/FiniteCriticalCellSphere/CertificateSphere"), Generality.General,
            GidRef.Create("D5/B/S3/Geometry/FiniteCriticalCellSphere/CertificateSphere"),
            new EvidenceMirror.Waiver(WaiverReason.Create("finite-critical-cell-sphere")),
            [Anchor.ParseCanonical("mathlib/module/Mathlib.Topology.CompactOpen")],
            Digest.Create("The computed finite Alexander certificate supplies the original-K based sphere maps and retained-label equations.")),
        H("The finite certificate on the original K"),
        Blocks(
            Paragraph(Text("These UNCOMPILED source attempts consume the current finite Alexander certificate and the attachment sphere construction. They retain literal j, original ambient labels, the whole retained endpoint and both based inverse homotopies. Availability for unrestricted arbitrary-plane-H original-K inputs remains open.")),
            Node("certificate-attachment", "attachment", "Computing every attachment input",
                "For the exact frozen AlexanderDual Certificate, use X=c.X, P=c.P, face=c.lambda, the included original apex c.a, c.cell_decomposition, c.cell_intersection, c.arithmetic and the already computed standalone c.pContraction. No desired collar or sphere outcome is added to Certificate.", DescribeRole.Definition),
            Node("certificate-apex", "apex", "The original apex in K",
                "Include the original cone point a into the original realization of K by the existing actual coordinate inclusion.", DescribeRole.Definition),
            Node("certificate-reductionequivalence", "reductionEquivalence", "The computed original reduction",
                "Use c.reductionSDR.retraction from K to X and c.reduction.inclusion from X to K. The whole-endpoint SDR supplies the left inverse homotopy; the exact retraction-inclusion identity supplies the right one. Both fix the original apex.", DescribeRole.Definition),
            Node("certificate-spherepoint", "spherePoint", "The sphere point for the original certificate",
                "Use the actual attachment sphere basepoint in the exact existing StdSphere(c.d), with c.d=lambda.card-1.", DescribeRole.Definition),
            Node("certificate-sphereequivalence", "sphereEquivalence", "The actual original-K based sphere endpoint",
                "Compose the computed original reduction based equivalence with the actual attachment sphere equivalence. The output is a BasedEquivalence between the original realization of c.K and the existing EuclideanSphereJoin.StdSphere(c.d), including both genuine inverse homotopies.", DescribeRole.Definition),
            Node("certificate-sphere-maps", "sphere_maps", "Original maps with computed reduction operands",
                "The forward is sphereHomeomorph after q after c.reductionSDR.retraction. The backward is c.reduction.inclusion after quotientInverse after sphereHomeomorph inverse. All operands come from the existing owners or the actual collar construction.", DescribeRole.Theorem),
            Node("certificate-sphere-representative", "sphere_representative", "Original disk representatives retain rational Psi",
                "For lambda.card>=2 and any literal complementary simplex point, the original K sphere map on its existing reduction inclusion equals the same exact rational spherePsi representative.", DescribeRole.Theorem),
            Node("certificate-sphere-poles", "sphere_poles", "Original barycenter and boundary equations",
                "For lambda.card>=2, the actual barycenter included into the original K maps to the reindexed north pole; every full-boundary representative maps to the reindexed south pole.", DescribeRole.Theorem),
            Node("certificate-sphere-based-laws", "sphere_based_laws", "Both original pointwise based homotopies",
                "The forward and backward send the original included apex and actual sphere point to each other. At every time the original-K inverse homotopy fixes the apex and the sphere inverse homotopy fixes the actual sphere point.", DescribeRole.Theorem),
            Node("certificate-reduction-fixed", "reduction_fixed", "The entire retained endpoint stays fixed",
                "For every actual x in c.X and every time, the original computed reductionSDR homotopy fixes c.reduction.inclusion(x). This preserves whole-endpoint fixedness, not only the apex.", DescribeRole.Theorem),
            Node("certificate-disk-original-coordinates", "disk_original_coordinates", "Original-K disk coordinates and ambient labels",
                "After the literal disk inclusion and existing reduction inclusion into K, each original lambda coordinate equals the input coordinate and every original label outside lambda is zero.", DescribeRole.Theorem),
            Node("certificate-ambient-ghost", "ambient_ghost", "True original ambient ghosts stay zero",
                "For every actual K point and every original label outside insert(a,W), that coordinate is zero. Thus all actual K-valued inverse and homotopy outputs retain these ghosts. A label outside lambda that is an actual core vertex is not incorrectly called a ghost.", DescribeRole.Theorem),
            Node("certificate-originalattachingmap", "originalAttachingMap", "The unchanged original j",
                "This is exactly c.j from the actual realization of D dual to the actual realization of E dual. No null or zero map is substituted and no homotopy equivalence of j is inferred.", DescribeRole.Definition)
        )));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromLean(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
