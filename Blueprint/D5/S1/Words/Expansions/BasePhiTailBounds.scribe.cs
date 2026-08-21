using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Expansions;

internal sealed class BasePhiTailBoundsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A nonempty canonical negative base-phi tail lies in the unit interval, with its first digit selecting the side of the inverse-golden cut.",
        H("Canonical Negative Base-Phi Tail Bounds"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("negative-tail-real-bounds"),
                DeclarationHandle.Create(
                    "D5/S1/Words/Expansions/BasePhiTailBounds.negative_tail_real_bounds"),
                H("The first negative digit selects the inverse-golden interval"),
                StatementSource.FromAuthor(Disp(Seq(
                    D(0), Lt, F.Id("T"), Underscore, F.Id("N"), Lt, D(1), Comma, Esc,
                    F.Id("d"), Underscore, Grp(Minus, D(1)), Eq, D(1), Sp, Rightarrow, Sp,
                    Varphi, Caret, Grp(Minus, D(1)), Leq, Sp, F.Id("T"), Underscore, F.Id("N"), Comma, Esc,
                    F.Id("d"), Underscore, Grp(Minus, D(1)), Eq, D(0), Sp, Rightarrow, Sp,
                    F.Id("T"), Underscore, F.Id("N"), Lt, Varphi, Caret, Grp(Minus, D(1))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Reindexing the finite negative support turns it into a binary nonadjacent word. "
                    + "Its inverse-golden evaluation is positive and below one; a leading one gives "
                    + "the closed upper side of the inverse-golden cut, while a leading zero gives "
                    + "the open lower side."))),
                DescribeRole.Theorem))));
}
