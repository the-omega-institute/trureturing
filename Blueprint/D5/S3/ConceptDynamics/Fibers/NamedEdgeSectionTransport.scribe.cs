using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Fibers;

internal sealed class NamedEdgeSectionTransportDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Transport through distinct edge ports retains named generators and their signed inverses.",
        H("Named Edge Section Transport"),
        Blocks(
            Paragraph(Text("Let V and E be arbitrary types with endpoint maps s,t:E to V and dependent fibres F. Each original named edge e has its own source port and target port. Its subdivided path is s(e), source(e), target(e), t(e). The ports remain distinct for loops and parallel edges. The middle segment carries exactly U(e), the outer segments carry identity maps, and reverse traversal uses the inverse of the same map.")),
            Describe.Lean(
                DescribeId.Create("incidence-path-transport"),
                DeclarationHandle.Create("D5/S3/ConceptDynamics/Fibers/NamedEdgeSectionTransport.incidence_path_transport"),
                H("Exact finite path transport correspondence"),
                StatementSource.FromAuthor(Disp(All("p", Call("IncidenceWalk"), Rel(Call("NamedTransport", Call("ProjectWalk", F.Id("p"))), Eq, Call("IncidenceTransport", F.Id("p")))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A port segment projects to an empty path. The middle segment projects to the signed traversal of its original named edge. Concatenation defines the projection of every finite walk, including walks beginning or ending at ports. Conversely each signed original generator lifts to its three-segment path or the reverse of that same path. Both operations preserve the dependent-fibre composite. No cell, attaching boundary, or topological homotopy relation is asserted.")))))));
}
