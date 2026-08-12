using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Diagonal;

internal sealed class PigeonholeFiberDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Winkler =
        LibraryNoteRef.Create("D5/L/Diagonal/winkler2020pigeonhole");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A reading space of smaller cardinality cannot distinguish every object.",
        H("Pigeonhole Fibers"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("finite-reading-has-a-fiber"),
                DeclarationHandle.Create("D5/S0/Diagonal/PigeonholeFiber.finite_reading_has_fiber"),
                H("A smaller reading space forces a nontrivial fiber"),
                StatementSource.FromAuthor(Disp(Seq(
                    Operatorname, Grp(F.Id("card")), Open, F.Id("Readings"), Close,
                    Sp, Lt, Sp,
                    Operatorname, Grp(F.Id("card")), Open, F.Id("Objects"), Close,
                    Sp, Rightarrow, Sp,
                    Exists, Sp, F.Id("x"), Comma, Sp, F.Id("y"),
                    Sp, InMacro, Sp, F.Id("Objects"), Comma, Sp,
                    F.Id("x"), Sp, Neq, Sp, F.Id("y"),
                    Sp, Land, Sp,
                    F.Id("read"), Open, F.Id("x"), Close,
                    Sp, Eq, Sp,
                    F.Id("read"), Open, F.Id("y"), Close))),
                AssessedProvenance.FromLiterature(Winkler),
                Blocks(
                    Paragraph(Text(
                        "For any object type, reading type, and reading map, a strict cardinal "
                        + "inequality from readings to objects rules out injectivity. Therefore "
                        + "two distinct objects have the same reading. The proof is the cardinal "
                        + "form of the pigeonhole principle: an assumed injection would reverse "
                        + "the strict inequality by making the object cardinal no larger than "
                        + "the reading cardinal.")),
                    Paragraph(Text(
                        "The source atom's finite-reading phrase describes the intended "
                        + "application. Finiteness is not an additional premise of the Lean "
                        + "theorem; the stated strict cardinal inequality alone carries the "
                        + "collision conclusion."))),
                DescribeRole.Theorem))));
}
