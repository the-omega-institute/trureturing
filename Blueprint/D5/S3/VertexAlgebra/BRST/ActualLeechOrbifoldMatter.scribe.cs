using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.BRST;

internal sealed class ActualLeechOrbifoldMatterDocument : IScribeDocumentDefinition
{
    private static DocumentBlock DescribeDeclaration(string name, string title, string statement,
        DescribeRole role) => Describe.Lean(
        DescribeId.Create("actual-leech-orbifold-matter-" + name.Replace('_', '-')),
        DeclarationHandle.Create("D5/S3/VertexAlgebra/BRST/ActualLeechOrbifoldMatter." + name),
        H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
        Blocks(Paragraph(Text(statement))), role);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The assembled Leech orbifold stress field supplies Virasoro matter of central charge 24.",
        H("Virasoro matter on the actual Leech orbifold"), Blocks(
            DescribeDeclaration("mode_apply", "Stress modes on both sectors",
                "For every integer n and orbifold state x, the coefficient at n+1 of the assembled "
                + "field at the fixed stress state acts on the underlying fixed component by the Leech "
                + "Sugawara mode n, and on the negative twisted component by the corrected tensor "
                + "half-Fock mode n. Both use the actual inverse Gram matrix. The twisted extraction "
                + "uses doubled exponent −2n−4 and retains the rank/16 term in mode zero.",
                DescribeRole.Theorem),
            DescribeDeclaration("virasoro", "Central charge 24",
                "For all integers m and n, the commutator of the two assembled modes is "
                + "(m−n) times mode m+n plus the identity multiplied by (24/12)(m³−m) "
                + "when m+n is zero, with zero central term otherwise.",
                DescribeRole.Theorem),
            DescribeDeclaration("positive_mode_truncation", "Statewise truncation",
                "For every orbifold state x there is an integer B such that mode n annihilates x "
                + "for every integer n greater than B.", DescribeRole.Theorem),
            DescribeDeclaration("matter", "Orbifold matter datum",
                "The actual fixed and negative twisted sectors, assembled stress modes, charge 24, "
                + "Virasoro commutator and statewise truncation give the matter datum.",
                DescribeRole.Definition))));
}
