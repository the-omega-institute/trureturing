using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra;

internal sealed class CharacterCarryCompletionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A section character determines the record of every finite binary label tree.",
        H("Character carry in binary trees"),
        Blocks(
            Paragraph(Text("Let E and C be commutative groups and let ell assign a character "
                + "record to each coarse label. The carry of g and h is "
                + "ell(g)+ell(h)-ell(g+h). A leaf has a coarse label and zero record; "
                + "at a fork, the coarse labels add and the records add with their carry. "
                + "No normalization of ell at zero is assumed.")),
            Describe.Lean(
                DescribeId.Create("binary-tree-character-record"),
                DeclarationHandle.Create(
                    "D5/S3/VertexAlgebra/CharacterCarryCompletion.tree_expansion"),
                H("Every binary tree has the same expanded record formula"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("T"), Comma, Sp,
                    Call("evaluate", F.Id("T")), Eq,
                    Open, Call("total", F.Id("T")), Comma, Sp,
                    Call("characterTotal", F.Id("T")), Minus,
                    F.Id("ell"), Open, Call("total", F.Id("T")), Close, Close))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Induction cancels both child section values "
                    + "against the carry at each fork. The resulting record is the "
                    + "sum of all leaf characters minus the character of the total "
                    + "coarse label, for every finite branching shape and "
                    + "parenthesization."))),
                DescribeRole.Theorem))));
}
