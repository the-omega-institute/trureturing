using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.BRST;

internal sealed class ActualLeechOrbifoldCriticalMatterDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The literal Leech orbifold and hyperbolic lattice field give critical matter.",
        H("Critical matter on the orbifold and hyperbolic lattice"), Blocks(
            Describe.Lean(DescribeId.Create("actual-leech-orbifold-hyperbolic-matter"),
                DeclarationHandle.Create(
                    "D5/S3/VertexAlgebra/BRST/ActualLeechOrbifoldCriticalMatter.hyperbolicMatter"),
                H("Hyperbolic lattice matter"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The standalone even hyperbolic plane with Gram matrix U "
                    + "has U as its inverse. Its Sugawara field gives integer Virasoro modes of "
                    + "central charge 2. Hahn order gives statewise positive-mode truncation."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("actual-leech-orbifold-critical-matter"),
                DeclarationHandle.Create(
                    "D5/S3/VertexAlgebra/BRST/ActualLeechOrbifoldCriticalMatter.matter"),
                H("Central charge 26"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("On the tensor product of the actual orbifold carrier and "
                    + "hyperbolic lattice carrier, each mode is the sum of the two original modes "
                    + "acting on their respective factors. These actions commute across factors. "
                    + "The central terms add to 26, and tensor induction gives a positive-mode "
                    + "bound for every state."))), DescribeRole.Definition))));
}
