using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.LocalGL.Green;

internal sealed class LabelDegreeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Label Degree", H("Label Degree"),
        Blocks(
            Paragraph(Text("Induction on squarefree labels; lower bound from the degree of Green's characters.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/LocalGL/Green/LabelDegree.labelChar_degree_bounds"),
                H("labelChar_degree_bounds"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("For a label c of degree r = |n| over a field with q elements, Re Ξ_c(1) ≥ 0, and the coefficient at 1 of the group algebra element attached to Ξ_c by labelIdem has real part at least (1 − r/q) q^{−r}.")))))));
}
