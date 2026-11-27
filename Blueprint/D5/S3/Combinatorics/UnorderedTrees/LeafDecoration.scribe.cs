using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.UnorderedTrees;

internal sealed class LeafDecorationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Internal subtrees with matching original leaf fibres determine an actual rooted isomorphism.",
        H("Reconstructing a rooted tree from its leaf fibres"),
        Blocks(Describe.Lean(
            DescribeId.Create("unordered-iso-iff-fibres"),
            DeclarationHandle.Create("D5/S3/Combinatorics/UnorderedTrees/LeafDecoration.iso_iff_fibres"),
            H("Restriction and extension of rooted isomorphisms"),
            StatementSource.FromAuthor(FibreCriterion()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Let T and S be finite rooted parent trees with internal roots. The pruned "
                    + "tree P retains the actual internal vertices. The fibre L(T,p) comprises "
                    + "the original leaf children of the internal vertex p.")),
                Paragraph(Text(
                    "An actual isomorphism preserves child edges and the internal predicate. "
                    + "It therefore restricts to an isomorphism of the pruned trees and to a "
                    + "bijection on each leaf fibre. Conversely, every original vertex is either "
                    + "internal or a leaf over its unique internal parent. Combining the given "
                    + "isomorphism with the chosen bijections of the finite fibres preserves "
                    + "each parent edge and the root.")),
                Paragraph(Text(
                    "Inflation attaches the desired number of fresh leaves at each skeleton "
                    + "vertex. Positive multiplicities at the skeleton tips make every skeleton "
                    + "vertex internal after inflation. Pruning then recovers the skeleton and "
                    + "the fibre sizes are the prescribed multiplicities."))),
            DescribeRole.Theorem))));

    private static Formula FibreCriterion()
    {
        var t = F.Id("T");
        var s = F.Id("S");
        var p = F.Id("p");
        var e = F.Id("e");
        return Disp(Seq(
            Call("Nonempty", Call("Iso", t, s)), Sp, Iff, Sp, Exists, Sp, e, Colon, Sp,
            Call("Iso", Call("P", t), Call("P", s)), Comma, Sp,
            Forall, Sp, p, Sp, InMacro, Sp, Call("P", t), Comma, Sp,
            Lvert, Sp, Call("L", t, p), Rvert, Sp, Eq, Sp,
            Lvert, Sp, Call("L", s, Call("e", p)), Rvert));
    }

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
}
