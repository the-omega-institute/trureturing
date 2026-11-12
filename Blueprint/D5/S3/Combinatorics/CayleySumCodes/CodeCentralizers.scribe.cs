using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.CayleySumCodes;

internal sealed class CodeCentralizersDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/CayleySumCodes/CodeCentralizers.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create(
        "D5/L/GraphInvariants/Nikandish/manikandishzhang2026sumcodes");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Centralizers and the normal core of a total perfect subgroup code.",
        H("Centralizer constraints in both total-code cases"),
        Blocks(
            Describe.Lean(DescribeId.Create("core-centralizes-connection"),
                DeclarationHandle.Create(Prefix + "core"), H("The whole normal core centralizes Y"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "For a finite group G and a total perfect subgroup code H, every "
                    + "member of the actual normal core of H centralizes every connection "
                    + "element. Conjugation preserves the normal transversal and its coset; "
                    + "representative uniqueness forces equality. The extra identity in "
                    + "case (b) is handled separately. This is Proposition 3.1(ii)."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("internal-centralizer"),
                DeclarationHandle.Create(Prefix + "internal"), H("H centralizes its internal connection elements"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "H centralizes each element of Y intersect H, in both branches of the "
                    + "criterion. H need not be normal. This is Proposition 3.1(i), retaining "
                    + "both internal elements in the exceptional branch."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("normal-internal-center"),
                DeclarationHandle.Create(Prefix + "normal_inter_central"), H("Centrality when H is normal"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "If H is normal, every element of Y intersect H is central in the "
                    + "ambient group G. All its conjugates stay in H, so uniqueness in "
                    + "the specified normal transversal applies to every ambient conjugator. "
                    + "This includes the central singleton used in Corollary 2.4; normality "
                    + "is essential to this ambient-center conclusion."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("two-conjugacy-classes"),
                DeclarationHandle.Create(Prefix + "two_classes"), H("Two genuine conjugacy classes"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "For a normal subgroup code and a connection set of size greater than "
                    + "one, there are two connection elements that are not conjugate in G. "
                    + "An internal connection element is central, so its conjugacy class is "
                    + "a singleton; any distinct element of Y lies in another class. This "
                    + "is Proposition 3.1(iv), and does not rely on a class-count proxy."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("connected-implies-generating"),
                DeclarationHandle.Create(Prefix + "connected_generates"), H("Connectedness forces generation"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "Along each actual sum-graph edge, membership in the subgroup generated "
                    + "by Y propagates by h=g inverse times (g h). Following a path from 1 "
                    + "in a connected graph therefore puts every vertex in that subgroup. "
                    + "Only connectedness implies generation is asserted; generation alone "
                    + "is not claimed sufficient for connectedness."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("connected-core-obstruction"),
                DeclarationHandle.Create(Prefix + "connected_core"), H("The connected-code obstruction"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "A connected normal-connection sum graph with H as a total perfect "
                    + "code forces core G(H) into Z(G). Core centralization of Y extends "
                    + "to its generated subgroup, which connectedness makes the full group. "
                    + "Thus a noncentral core excludes every connected witness. This retains "
                    + "the Zhang 4.5 consequence cited after Proposition 3.1, without using "
                    + "the faulty singleton-only total-transversal criterion. The additional "
                    + "conjugacy-class index sum needs its own evidence."))),
                DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create(
            "D5/S3/Combinatorics/CayleySumCodes/NormalTransversal"))]));
}
