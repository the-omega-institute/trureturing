using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Fibers;

internal sealed class NamedEdgeSectionTransportDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Named edge transport retains parallel edges, loops and dependent fibres in the root evaluation criterion.",
        H("Named Edge Section Transport"),
        Blocks(
            Paragraph(Text("Let V and E be arbitrary vertex and named edge types with endpoint maps s,t:E to V. A signed generator is an original named edge or the formal inverse of that same edge. Finite paths use the symmetrified original quiver. No finiteness, simplicity, chosen spanning tree or commutativity assumption is imposed.")),
            Paragraph(Text("Each edge e is represented by the three-segment path s(e), source(e), target(e), t(e). The two ports are distinct constructors and retain the original edge name, including when s(e)=t(e) or another edge has the same endpoints. The port fibres are the original endpoint fibres. The middle segment carries exactly U(e), the outer segments carry identity maps, and reverse traversal uses the inverse of that same map.")),
            Describe.Lean(
                DescribeId.Create("incidence-path-transport"),
                DeclarationHandle.Create("D5/S3/ConceptDynamics/Fibers/NamedEdgeSectionTransport.incidence_path_transport"),
                H("Transport on every actual finite path"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("An outer segment projects to an empty path. A middle segment projects to its signed original generator. Concatenation projects every finite incidence walk, including walks beginning at ports. Each signed original generator lifts to its three-segment path or its reverse. The projection and lift preserve the actual dependent-fibre composite. Projecting a lifted path returns its literal signed original path, retaining the named generators even when their transport operators happen to agree.")))),
            Describe.Lean(
                DescribeId.Create("named-unitary-root-classification"),
                DeclarationHandle.Create("D5/S3/ConceptDynamics/Fibers/NamedEdgeSectionTransport.named_unitary_root_classification"),
                H("Root evaluation and unitary holonomy"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Place a normed complex vector space F(v) at each vertex and a linear isometric equivalence U(e) at each named edge. The finite-dimensional unitary setting is obtained by taking the original fibres isometric to the same complex d-space. Connectedness means that every vertex admits an actual finite signed path from the chosen root. Compatible sections satisfy every original named edge equation.")),
                    Paragraph(Text("Extension to the ports and restriction to the original vertices are inverse maps on sections. Projection and lifting identify the common fixed vectors of all root loops. Applying ConfigurationPathTransport.rootSectionMap_bijective to this faithful incidence graph supplies the section bijection. The comparison is root evaluation. Its inverse at any vertex is transport along every root-to-vertex path, and the target is the intersection of the kernels of all actual root-loop operators minus the identity.")),
                    Paragraph(Text("Every compatible section has the same norm in each fibre as at the root. The comparison preserves the norm of differences measured in the root fibre. This is the root-fibre metric on sections; no product norm or summability on the vertex set is assumed. Every root vector transports independently of path exactly when every root-loop operator is the identity. Existence of a fixed vector or the zero section does not imply that all-vector condition.")),
                    Paragraph(Text("No assertion is made here about two-cell attaching boundaries or continuous path homotopy. For a simply connected two-dimensional cell complex, passing from flat attaching faces to identity transport on every loop requires a separate topological correspondence. Local face flatness on a punctured region does not supply that correspondence, and nontrivial holonomy around its hole remains possible.")))))));
}
