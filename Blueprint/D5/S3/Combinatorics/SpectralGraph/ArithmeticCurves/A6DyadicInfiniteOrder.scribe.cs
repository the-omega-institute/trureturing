using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.SpectralGraph.ArithmeticCurves;
internal sealed class A6DyadicInfiniteOrderDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/GraphInvariants/idealintersection2026sixsupport");
    private static DocumentBlock Item(string id, string name, string title, bool taskLocal) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create("D5/S3/Combinatorics/SpectralGraph/ArithmeticCurves/A6DyadicInfiniteOrder." + name),
            H(title), StatementSource.WithoutFormula(), taskLocal ? AssessedProvenance.FromRepo(Source) : AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text("The current compiler statement supplies the exact full telescope. Attribution and remaining boundaries above apply."))), DescribeRole.Theorem);
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual point-group infinite order and full Galois-fiber obstruction", H("Actual point-group infinite order and full Galois-fiber obstruction"),
        Blocks(
            Paragraph(Text("For the actual E0 over Q(sqrt43645), negative dyadic horizontal valuation yields an infinite doubling orbit. This task-local proof establishes infinite order of the received T and original rational chart S, every nonzero integer multiple of every P in the entire fiber P-sigma(P)=T is nonrational, integer independence of S and T, actual rational rank at least1 and quadratic rank at least2. The original Nagell-Lutz proof remains supplied evidence. Exact ranks, full bases and saturation are not claimed. A6ModelEquivalences supplies full transfers to the original E/Ed models. A6FullTorsion uses this dyadic theorem to prove the complete received torsion conclusions, and A6RationalCurveIsogeny proves the full-coset obstruction in the field-universal rational coordinate-atlas representation. No separate intrinsic scheme-isogeny API equivalence theorem is claimed.")),
            Paragraph(Text("Original Nikandish problem and Ma/Nikandish/Zhang supplied manuscripts at PR9 revision6d491f77b35dec808fc777b69939c56cdae5dc02. Exact original blobs are attributed in Lean. Full O1-O9, L1-L21/F1-F17, C1-C16, n7 and paused exclusions, generalQ3, a6 certification, finite-enumeration reproduction limits and rights/publication boundaries remain unchanged. Issue28398 records unfinished faithful escape registration, not an audit certificate.")),
            Item("infinite-order-of-negative-dyadic", "infinite_order_of_negative_dyadic", "infinite order of negative dyadic", true),
            Item("t-infinite-order", "T_infinite_order", "T infinite order", false),
            Item("s-received-chart", "S_received_chart", "S received chart", false),
            Item("s-infinite-order", "S_infinite_order", "S infinite order", false),
            Item("embedded-s-infinite-order", "embedded_S_infinite_order", "embedded S infinite order", false),
            Item("nonzero-multiple-nonrational", "nonzero_multiple_nonrational", "nonzero multiple nonrational", false),
            Item("sigma-t", "sigma_T", "sigma T", false),
            Item("independent-witnesses", "independent_witnesses", "independent witnesses", false),
            Item("two-witnesses-linearindependent", "two_witnesses_linearIndependent", "two witnesses linearIndependent", false),
            Item("quadratic-group-rank-lower", "quadratic_group_rank_lower", "quadratic group rank lower", false),
            Item("rational-group-rank-lower", "rational_group_rank_lower", "rational group rank lower", false)),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/SpectralGraph/ArithmeticCurves/A6GaloisCoset"))]));
}
