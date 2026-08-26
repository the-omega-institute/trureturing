using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Coding;

internal sealed class FullCRTBlindCountAndDistanceDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Arith/Coding/FullCRTBlindCountAndDistance."
            + "full_crt_blind_count_distance_and_detection_limit";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The full product range has maximal blind-coordinate count one below its "
            + "length and exact distance one.",
        H("Full CRT Blind Count and Distance"),
        Blocks(Describe.Lean(
            DescribeId.Create("full-crt-blind-count-and-distance"),
            DeclarationHandle.Create(Declaration),
            H("Full CRT range has no coordinate-error margin"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The blind-coordinate count is the canonical maximum over coordinate "
                        + "subsets whose modulus product lies below the message range. At "
                        + "the full product, every prefix omitting the last coordinate is "
                        + "admissible, while the complete coordinate set is not.")),
                Paragraph(Text(
                    "The resulting residue words are still injective on the complete range, "
                        + "so encoding remains unique. The attained minimum supplies two "
                        + "valid words separated in exactly one coordinate, showing that a "
                        + "single changed coordinate can be accepted as another valid word."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula moduli = F.Id("m");
        Formula length = F.Id("n");
        Formula i = F.Id("i");
        Formula j = F.Id("j");
        Formula x = F.Id("x");
        Formula y = F.Id("y");
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));
        Formula modulusI = Call("m", i);
        Formula modulusJ = Call("m", j);
        Formula fullRange = Call("prefixProduct", moduli, length);
        Formula wordX = Call("residueWord", moduli, length, x);
        Formula wordY = Call("residueWord", moduli, length, y);
        Formula blindCount = Call(
            "maximumBlindCoordinateCount", moduli, length, fullRange);
        Formula minimumDistance = Call(
            "residueMinimumDistance", moduli, length, fullRange);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, moduli, Colon, Sp, naturals, Sp, To, Sp, naturals,
            Comma, Sp, length, Sp, InMacro, Sp, naturals, Comma,
            RowBreak, Grp(),
            Open,
            D(0), Sp, Lt, Sp, length,
            Sp, Land, RowBreak, Grp(),
            Open, Forall, Sp, i, Comma, Sp, j, Comma, Sp,
            i, Sp, Lt, Sp, j, Sp, Land, Sp, j, Sp, Lt, Sp, length,
            Sp, Rightarrow, Sp, modulusI, Sp, Lt, Sp, modulusJ, Close,
            Sp, Land, RowBreak, Grp(),
            Open, Forall, Sp, i, Comma, Sp,
            i, Sp, Lt, Sp, length, Sp, Rightarrow, Sp,
            D(2), Sp, Leq, Sp, modulusI, Close,
            Sp, Land, RowBreak, Grp(),
            Open, Forall, Sp, i, Comma, Sp, j, Comma, Sp,
            i, Sp, Lt, Sp, length, Sp, Land, Sp,
            j, Sp, Lt, Sp, length, Sp, Land, Sp,
            i, Sp, Neq, Sp, j, Sp, Rightarrow, Sp,
            Gcd, Open, modulusI, Comma, Sp, modulusJ, Close,
            Sp, Eq, Sp, D(1), Close,
            Close, Sp, Rightarrow, RowBreak, Grp(),
            blindCount, Sp, Eq, Sp, length, Sp, Minus, Sp, D(1),
            Sp, Land, RowBreak, Grp(),
            minimumDistance, Sp, Eq, Sp, D(1),
            Sp, Land, RowBreak, Grp(),
            Open, Forall, Sp, x, Comma, Sp, y, Sp, InMacro, Sp, naturals, Comma, Sp,
            x, Sp, Lt, Sp, fullRange, Sp, Land, Sp,
            y, Sp, Lt, Sp, fullRange, Sp, Land, Sp,
            wordX, Sp, Eq, Sp, wordY,
            Sp, Rightarrow, Sp, x, Sp, Eq, Sp, y, Close,
            Sp, Land, RowBreak, Grp(),
            Open, Exists, Sp, x, Comma, Sp, y, Sp, InMacro, Sp, naturals, Comma, Sp,
            x, Sp, Lt, Sp, y, Sp, Land, Sp,
            y, Sp, Lt, Sp, fullRange, Sp, Land, Sp,
            Call("hammingDist", wordX, wordY), Sp, Eq, Sp, D(1), Close, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
