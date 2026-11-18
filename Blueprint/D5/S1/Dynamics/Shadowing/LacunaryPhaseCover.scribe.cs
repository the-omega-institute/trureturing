using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Dynamics.Shadowing;

internal sealed class LacunaryPhaseCoverDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S1/Dynamics/Shadowing/LacunaryPhaseCover.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Periodic phase covers at every finite level", H("Periodic phase covers at every finite level"), Blocks(
        Paragraph(Text("For every m>=3 and signed-window radius R, construct m-1 periodic masks. Every mask preserves the initial window, one whole mask preserves each translated future window, and no mask retains three vertices of any m-term progression of step (m+1)^k once k is sufficiently large.")),
        Describe.Lean(DescribeId.Create("lacunary-phase-cover"), DeclarationHandle.Create(Owner + "lacunary_phase_cover"), H("The full phase-cover construction"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The scale K and all masks are constructed from m and R. The returned bound R<=(m-1)(m+1)^K controls the pseudo-orbit overlap used for the remaining short scales. The masks have a common neighborhood of phase zero and cover every sufficiently short phase window. Long progressions reduce to equally spaced polygons because (m+1)^(k-K) is congruent to one modulo m. Open arcs of length two retain at most two integer-spaced vertices; each interior mask is a union of two arcs of lengths one half and one, each retaining at most one vertex."))), DescribeRole.Theorem))));
}
