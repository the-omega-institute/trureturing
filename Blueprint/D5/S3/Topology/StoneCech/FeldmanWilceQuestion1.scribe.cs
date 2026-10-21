using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology.StoneCech;

internal sealed class FeldmanWilceQuestion1Document : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Topology/StoneCech/FeldmanWilceQuestion1.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Topology/feldmanwilce2026compactnesscliques");

    private static Formula ResultStatement => Disp(Seq(Exists, Sp, Id("Y"), Colon, Sp,
        Call("Set", Call("Ultrafilter", Id("Block"))), Comma, Sp,
        Call("Q1Witness", Id("Y"))));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The finite-block instance supplies a countably compact Hausdorff space with a closed orthogonality relation and finite, unbounded cliques.",
        H("Feldman–Wilce Question 1: finite unbounded cliques"), Blocks(
            Paragraph(Text(
                "Block is the countable disjoint union Sigma (fun n : Nat => Fin (n+1)); blockIndex sends a point to its first coordinate. "
                + "For a set Y of ultrafilters on Block, X=principalExtension(Y) is the actual subtype range(pure) union Y with its inherited topology. "
                + "The relation is the adjacency field of fibreGraph(blockIndex,Y) : SimpleGraph X. Thus symmetry and irreflexivity are structural properties of the relation.")),
            Paragraph(Text(
                "Q1Witness(Y) is the conjunction of CountablyCompactSpace X, T2Space X, T1Space X, "
                + "closedness of {p : X times X | (fibreGraph blockIndex Y).Adj p.1 p.2}, "
                + "finiteness of every clique K, existence of a finite clique with ncard n for every natural n, "
                + "and the nonexistence of one natural bound on all clique ncards. The closed set is in the entire product X squared, including the diagonal. "
                + "These are native topological and SimpleGraph predicates; no sequential compactness assertion is substituted for countable compactness.")),
            Describe.Lean(DescribeId.Create("feldman-wilce-question-one"),
                DeclarationHandle.Create(Owner + "result"),
                H("A countably compact Hausdorff witness"),
                StatementSource.FromAuthor(ResultStatement), AssessedProvenance.FromRepo(Source), Blocks(
                    Paragraph(Text(
                        "The block fibre over b is contained in the finite range of Sigma.mk b. The range of Sigma.mk n has ncard n+1 by injectivity, "
                        + "so the fibre sizes are unbounded. The source is countable. Applying SectionClosedGraph.exists_countablyCompact_closed_fibreGraph "
                        + "therefore constructs Y without assuming a selector or a countable compactness supplier. Hausdorffness and the T1 property are inherited from the ambient ultrafilter space.")),
                    Paragraph(Text(
                        "The generic endpoint supplies full-product closedness, finiteness of every clique and every prescribed finite size. "
                        + "If bound were a uniform finite bound, the clique of size bound+1 would contradict it. "
                        + "The sizes 1,2,... reindex the nonempty finite blocks proposed in the primary paper. "
                        + "The paper uses the restricted ambient closure of the finite-block relation; Q1 asks for any closed orthogonality relation, "
                        + "and the constructed projection-injective selector makes this principal-only relation itself closed.")),
                    Paragraph(Text(
                        "This is the concrete application of the repository's existing arbitrary-map supplier and graph construction. "
                        + "The application proof is bind-only with consumed finite-fibre auxiliaries; its admission basis is the named external Question 1. "
                        + "The arXiv record and the authors' repository retain Q1 as open. This claim addresses that question and does not assert global priority or resolve Questions 2 and 3."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("feldman-wilce-countably-compact-unbounded-cliques"),
                    ResolutionKind.Proved))), []));
}
