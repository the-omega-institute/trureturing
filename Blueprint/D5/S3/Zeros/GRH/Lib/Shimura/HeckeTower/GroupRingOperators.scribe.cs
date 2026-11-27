using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.Shimura.HeckeTower;

internal sealed class GroupRingOperatorsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Group Ring Operators", H("Group Ring Operators"),
        Blocks(
            Paragraph(Text("spans in the group ring k[G]; elements sending K-fixed vectors to eigenvectors.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/Shimura/HeckeTower/GroupRingOperators.asAlgebraHom_eq_sum_support"),
                H("asAlgebraHom_eq_sum_support"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("For a representation π of G on a k-module W, an element a = ∑ a_g [g] of the group ring k[G] acts as ∑ a_g π(g), summed over the support of a.")))))));
}
