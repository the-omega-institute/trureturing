using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Expansions;

internal sealed class BasePhiRecursiveStructureDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Golden floor coordinates have the two local fiber shapes needed to recurse across a fixed negative base-phi tail.",
        H("Golden-Coordinate Recursive Tail Structure"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("positive-coordinate-fiber-small"),
                DeclarationHandle.Create(
                    "D5/S1/Words/Expansions/BasePhiRecursiveStructure.positiveCoordinate_fiber_small"),
                H("Below the inverse-golden cut a coordinate fiber has three consecutive values"),
                StatementSource.FromAuthor(Disp(Seq(
                    D(0), Lt, F.Id("T"), Lt, Varphi, Caret, Grp(Minus, D(1)), Sp,
                    Rightarrow, Sp, OpenBrace, F.Id("v"), Sp, Colon, Sp,
                    F.Id("B"), Open, F.Id("v"), Close, Eq, F.Id("B"), CloseBrace, Eq,
                    OpenBrace, F.Id("s"), Comma, F.Id("s"), Plus, D(1), Comma,
                    F.Id("s"), Plus, D(2), CloseBrace))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The Beatty-floor coordinate of the nonnegative half is constant on exactly "
                    + "three consecutive natural coordinates when the fixed negative-tail value lies "
                    + "strictly below the inverse-golden cut."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("positive-coordinate-fiber-large"),
                DeclarationHandle.Create(
                    "D5/S1/Words/Expansions/BasePhiRecursiveStructure.positiveCoordinate_fiber_large"),
                H("Above the inverse-golden cut a coordinate fiber has two consecutive values"),
                StatementSource.FromAuthor(Disp(Seq(
                    Varphi, Caret, Grp(Minus, D(1)), Leq, Sp, F.Id("T"), Lt, D(1), Sp,
                    Rightarrow, Sp, OpenBrace, F.Id("v"), Sp, Colon, Sp,
                    F.Id("B"), Open, F.Id("v"), Close, Eq, F.Id("B"), CloseBrace, Eq,
                    OpenBrace, F.Id("s"), Comma, F.Id("s"), Plus, D(1), CloseBrace))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "At or above the inverse-golden cut the same floor fiber contains exactly "
                        + "two consecutive coordinates. The canonical seam condition removes the "
                        + "second coordinate when the first negative digit is one.")),
                    Paragraph(Text(
                        "Together these two floor classifications are the cropped recursive structure "
                        + "needed for complete negative-tail fibers. They do not formalize all word "
                        + "appendants or the conjectural finite-prefix classification in Dekking's paper."))),
                DescribeRole.Theorem))));
}
