using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Deficit.Carry;

internal sealed class GoldenCarryDeficitBridgeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Internal golden carries preserve both faces, and the common signed integer deficit vanishes under difference decoding.",
        H("The Golden Carry Deficit Bridge"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("the-golden-carry-deficit-bridge"),
                DeclarationHandle.Create(
                    "D5/S1/Deficit/Carry/GoldenCarryDeficitBridge.golden_carry_deficit_bridge"),
                H("The golden carry deficit bridge"),
                StatementSource.FromAuthor(BridgeFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For each natural carry index and each pair of natural operands, the adjacent "
                            + "and higher doubling rewrites preserve both the expanding golden face phi "
                            + "and its conjugate face psi. The normalization deficit is equal on those "
                            + "two faces, is a rational integer, and equals the signed count accumulated "
                            + "from bottom carries: the lowest rule contributes +1, the second contributes "
                            + "-1, and internal carries contribute zero.")),
                    Paragraph(Text(
                        "The proof directly packages the frozen two-face theorem "
                            + "carry_rewrite_face_invariant with the frozen integer certificate "
                            + "deficit_integer. Since the two deficits are equal, their difference divided "
                            + "by sqrt(5) is zero, making the common integer account invisible to the "
                            + "difference decoder. No carry arithmetic or normalization machinery is "
                            + "reproved in this bridge."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S1/Deficit/GoldenCarryLedger")),
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S1/Deficit/DeficitInteger")),
        ]));

    private static Formula BridgeFormula()
    {
        Formula k = F.Id("k");
        Formula v1 = Seq(F.Id("v"), Underscore, D(1));
        Formula v2 = Seq(F.Id("v"), Underscore, D(2));
        Formula x = F.Id("x");
        Formula deficit = Seq(F.Id("c"), Open, v1, Comma, Sp, v2, Close);
        Formula contraction = Seq(F.Id("c"), Apos, Open, v1, Comma, Sp, v2, Close);
        Formula signedCount = Seq(
            Operatorname, Grp(F.Id("carrySignedCount")), Open,
            Operatorname, Grp(F.Id("toRaw")), Open, F.Id("Z"), Open, v1, Close, Close, Plus,
            Operatorname, Grp(F.Id("toRaw")), Open, F.Id("Z"), Open, v2, Close, Close, Close);

        return Disp(Seq(
            Forall, Sp, k, Comma, Sp, v1, Comma, Sp, v2,
            InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, Quad,
            OpenBracket,
            Forall, Sp, x, InMacro, Sp, OpenBrace, Varphi, Comma, Sp, Psi, CloseBrace,
            Comma, Quad,
            Open,
            x, Caret, Grp(k, Plus, D(1)), Plus,
            x, Caret, Grp(k, Plus, D(2)), Eq,
            x, Caret, Grp(k, Plus, D(3)), Sp, Land, Sp,
            D(2), x, Caret, Grp(k, Plus, D(2)), Eq,
            x, Caret, Grp(k, Plus, D(3)), Plus, x, Caret, k,
            Close,
            CloseBracket, Sp, Land, Sp,
            OpenBracket,
            deficit, Eq, contraction, Sp, Land, Sp,
            Open,
            Exists, Sp, F.Id("z"), InMacro, Sp, Mathbb, Grp(F.Id("Z")), Comma, Sp,
            deficit, Eq, F.Id("z"),
            Close, Sp, Land, Sp,
            deficit, Eq, signedCount,
            CloseBracket, Sp, Land, Sp,
            Frac, Grp(deficit, Minus, contraction), Grp(Sqrt, Grp(D(5))), Eq, D(0)));
    }
}
