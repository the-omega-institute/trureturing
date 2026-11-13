using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.CayleySumCodes;

internal sealed class SubgroupCodeRestrictionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/CayleySumCodes/SubgroupCodeRestriction.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create(
        "D5/L/FiniteGroups/manikandishzhang2026sumcodes");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Perfect and total perfect subgroup codes in the actual induced sum graph.",
        H("Code inheritance along every intermediate subgroup"),
        Blocks(
            Describe.Lean(DescribeId.Create("restricted-connection"),
                DeclarationHandle.Create(Prefix + "connection"), H("The same connection inside the subgroup"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("The connection is the preimage of the given ambient normal subset under the subgroup inclusion. No inverse closure or choice of a transversal is added."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("restricted-normal-subset"),
                DeclarationHandle.Create(Prefix + "normal"), H("Inherited conjugation invariance"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("Conjugation by a subgroup element is the ambient conjugation, so the restricted connection remains normal as a subset of the subgroup."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("actual-induced-graph"),
                DeclarationHandle.Create(Prefix + "graph_induce"), H("Equality with the induced loopless graph"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("The restricted sum graph is exactly the ambient simple graph induced on the subgroup. Self-neighbors remain excluded; this is a graph equality on all subgroup vertices, not merely an equivalence of existential code witnesses."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("total-code-inheritance"),
                DeclarationHandle.Create(Prefix + "total"), H("Every intermediate subgroup preserves the total code"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("For H contained in M contained in G, every vertex of M retains its unique open neighbor in H, since that neighbor belongs to M. The connection set is the specified ambient connection restricted to M. No subnormality of M, normality of H, finiteness, or singleton-transversal criterion is used. This supplies a direct repaired route for the total-code part of antecedent Theorem 2.7 and stays distinct from normal-transversal inheritance. It asserts no quotient total-code inheritance."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("perfect-code-inheritance"),
                DeclarationHandle.Create(Prefix + "perfect"), H("Perfect codes restrict through the closed neighborhood"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("The unique member of H in each closed neighborhood of a vertex of M remains unique in the induced graph. This separately proves the perfect-code part, for arbitrary intermediate subgroups and arbitrary groups. The correction's unaffected-antecedent attribution is preserved; no CFSG case or quotient-class perfect-code criterion is certified by this restriction argument."))), DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create(
            "D5/S3/Combinatorics/CayleySumCodes/PerfectCodeTransversal"))]));
}
