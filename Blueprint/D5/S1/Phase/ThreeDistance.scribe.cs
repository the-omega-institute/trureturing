using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Phase;

internal sealed class ThreeDistanceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The cyclic adjacent gaps of a finite golden-ratio rotation orbit have at most three distinct lengths.",
        H("Three Distances in the Golden Rotation"),
        Blocks(
            Paragraph(
                Text("For a natural number "), Math(F.Id("N")), Text(
                    ", the finite orbit in "), Ref("D5/S1/Phase/ThreeDistance"), Text(
                    " consists of the fractional parts of n times the golden ratio, for "
                    + "0 <= n < N. The function goldenGapValues takes the distinct lengths "
                    + "of gaps between successive orbit points in increasing order, including the cyclic "
                    + "gap from the last point back to the first.")),
            Describe.Lean(
                DescribeId.Create("golden-three-gap-bound"),
                DeclarationHandle.Create("D5/S1/Phase/ThreeDistance.three_gap"),
                H("At most three distinct cyclic gap lengths"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("N"), Sp, InMacro, Sp,
                    Mathbb, Grp(F.Id("N")), Comma, Esc,
                    Call("card", Call("goldenGapValues", F.Id("N"))),
                    Sp, Le, Sp, D(3)))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every natural N, the cardinality of goldenGapValues(N) "
                        + "is at most three. This counts distinct lengths, rather than "
                        + "the number of gaps. There is no positive-N hypothesis: the "
                        + "total gap construction assigns the singleton gap of length "
                        + "one to the empty orbit as well as to a one-point orbit.")),
                    Paragraph(Text(
                        "The proof specializes the general real-rotation bound "),
                        Ref("D5/S1/Phase/ThreeGap/Main.three_gap_card_le_three"),
                        Text(" to the golden ratio. That theorem is the repository's "
                            + "MIT-licensed port of Dirk Kunert's formalization of the "
                            + "classical three-gap theorem. The present result is its "
                            + "repository-derived specialization; it asserts neither "
                            + "that all three lengths occur for every N nor a formula "
                            + "for their multiplicities."))),
                DescribeRole.Theorem))));
}
