using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Complexity.PositivePairs.Coefficients;

internal sealed class PositivePairsCoefficientsPositivePairFiltrationDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S1/Words/Complexity/PositivePairs/Coefficients/PositivePairFiltration";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Words/nilforoushanparvaresh2026kdecks");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The full indexed positive-pair family has the required cutoff filtration.",
        H("PositivePairFiltration"),
        Blocks(
            Paragraph(Text(
                "Magnus expansions and shuffle or infiltration identities are classical context, "
                + "but the complete recursively indexed positive-pair construction below is a "
                + "repository route. Indices are retained even when two evaluated pairs coincide.")),
            D("positive-pair-index", "PositivePairIndex", "Full recursive choice index",
                "PositivePairIndex A r abbreviates Fin r -> A. Distinct indices remain distinct even if their evaluated word pairs coincide.", DescribeRole.Definition),
            D("positive-pair-words", "positivePairWords", "Actual recursive positive pairs",
                "Level zero is ([],[]), level one is ([a],[]), and a successor step sends (u,v) and a to (u++[a]++v, v++[a]++u).", DescribeRole.Definition),
            D("cutoff-magnus", "cutoffMagnus", "Actual Magnus cutoff",
                "For finite A, cutoffMagnus r source is the rational coefficient extension of the actual Magnus polynomial restricted through degree r.", DescribeRole.Definition),
            D("positive-pair-ratio", "positivePairRatio", "Actual positive-pair Magnus ratio",
                "For independent cutoff and level parameters, positivePairRatio is cutoffMagnus(u) multiplied by the finite geometric inverse of cutoffMagnus(v)-1 for the actual pair (u,v).", DescribeRole.Definition),
            D("positive-pair-ratio-filtration", "full_positivePair_ratio_filtration", "Full indexed family agrees below its level",
                "For every finite alphabet, cutoff, level r, and full PositivePairIndex, both the actual cutoff-Magnus difference M(u)-M(v) and the ratio minus one vanish below r. Duplicate pairs and zero leading directions remain in the quantified family."),
            D("cutoff-magnus-cancellation", "cutoffMagnus_cancellation", "Cancellation of actual cutoff Magnus factors",
                "The empty-word coefficient of every actual Magnus image is one. Finite geometric inverses in the truncated split-convolution algebra therefore cancel common left factors and equal right factors in appended positive words at every cutoff."))));

    private static DocumentBlock.Describe D(string id, string declaration, string title,
        string prose, DescribeRole role = DescribeRole.Theorem, bool literature = false) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Module + "." + declaration),
            H(title), StatementSource.FromAuthor(Disp(Statement(declaration))),
            literature ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role);

    private static Formula Statement(string declaration) => declaration switch
    {
        "PositivePairIndex" => Seq(Forall, Sp, F.Id("A"), Comma, F.Id("r"),
            Comma, Equal(Call("PositivePairIndex", F.Id("A"), F.Id("r")),
                Call("functions", Call("Fin", F.Id("r")), F.Id("A")))),
        "positivePairWords" => PositivePairWordsStatement(),
        "cutoffMagnus" => Seq(Forall, Sp, F.Id("r"), Comma,
            F.Id("source"), Comma,
            Equal(Call("cutoffMagnus", F.Id("r"), F.Id("source")),
                Call("cutoffRestriction", F.Id("r"),
                    Call("toRationalWordPolynomial",
                        Call("magnusPolynomial", F.Id("source")))))),
        "positivePairRatio" => Seq(Forall, Sp, F.Id("cutoff"), Comma,
            F.Id("r"), Comma, F.Id("index"), Comma,
            Equal(Call("positivePairRatio", F.Id("cutoff"), F.Id("r"),
                    F.Id("index")),
                Call("cutoffMul", F.Id("cutoff"),
                    Call("cutoffMagnus", F.Id("cutoff"),
                        Call("left", Call("positivePairWords", F.Id("r"),
                            F.Id("index")))),
                    Call("cutoffGeometricInverse", F.Id("cutoff"), Subtract(
                        Call("cutoffMagnus", F.Id("cutoff"), Call("right",
                            Call("positivePairWords", F.Id("r"), F.Id("index")))),
                        Call("cutoffOne", F.Id("cutoff"))))))),
        "full_positivePair_ratio_filtration" => Seq(Forall, Sp,
            F.Id("cutoff"), Comma, F.Id("r"), Comma, F.Id("index"), Comma,
            Call("VanishesBelow", F.Id("cutoff"), F.Id("r"), Subtract(
                Call("cutoffMagnus", F.Id("cutoff"), Call("left",
                    Call("positivePairWords", F.Id("r"), F.Id("index")))),
                Call("cutoffMagnus", F.Id("cutoff"), Call("right",
                    Call("positivePairWords", F.Id("r"), F.Id("index")))))),
            Land, Call("VanishesBelow", F.Id("cutoff"), F.Id("r"), Subtract(
                Call("positivePairRatio", F.Id("cutoff"), F.Id("r"), F.Id("index")),
                Call("cutoffOne", F.Id("cutoff"))))),
        "cutoffMagnus_cancellation" => Seq(Open, Forall, Sp, F.Id("r"), Comma,
            F.Id("prefix"), Comma, F.Id("left"), Comma, F.Id("right"), Comma,
            Equal(Call("cutoffMagnus", F.Id("r"),
                    Call("append", F.Id("prefix"), F.Id("left"))),
                Call("cutoffMagnus", F.Id("r"),
                    Call("append", F.Id("prefix"), F.Id("right")))),
            Rightarrow, Equal(Call("cutoffMagnus", F.Id("r"), F.Id("left")),
                Call("cutoffMagnus", F.Id("r"), F.Id("right"))), Close, Land,
            Open, Forall, Sp, F.Id("r"), Comma, F.Id("left"), Comma,
            F.Id("right"), Comma, F.Id("suffixLeft"), Comma,
            F.Id("suffixRight"), Comma,
            Equal(Call("cutoffMagnus", F.Id("r"), F.Id("suffixLeft")),
                Call("cutoffMagnus", F.Id("r"), F.Id("suffixRight"))), Land,
            Equal(Call("cutoffMagnus", F.Id("r"),
                    Call("append", F.Id("left"), F.Id("suffixLeft"))),
                Call("cutoffMagnus", F.Id("r"),
                    Call("append", F.Id("right"), F.Id("suffixRight")))),
            Rightarrow, Equal(Call("cutoffMagnus", F.Id("r"), F.Id("left")),
                Call("cutoffMagnus", F.Id("r"), F.Id("right"))), Close),
        _ => throw new ArgumentOutOfRangeException(nameof(declaration)),
    };

    private static Formula PositivePairWordsStatement()
    {
        var r = F.Id("r");
        var index = F.Id("index");
        var previous = Call("positivePairWords", Add(r, Num(1)),
            Call("FinInit", index));
        var a = Call("apply", index, Call("FinLast", Add(r, Num(1))));
        return Seq(
            Open, Forall, Sp, F.Id("index0"), Comma,
            Equal(Call("positivePairWords", Num(0), F.Id("index0")),
                Call("pair", F.Id("empty"), F.Id("empty"))), Close, Land,
            Open, Forall, Sp, F.Id("index1"), Comma,
            Equal(Call("positivePairWords", Num(1), F.Id("index1")),
                Call("pair", Call("singleton", Call("apply", F.Id("index1"), Num(0))),
                    F.Id("empty"))), Close, Land,
            Forall, Sp, r, Comma, index, Comma,
            Equal(Call("positivePairWords", Add(r, Num(2)), index),
                Call("pair",
                    Call("append", Call("left", previous), Call("singleton", a),
                        Call("right", previous)),
                    Call("append", Call("right", previous), Call("singleton", a),
                        Call("left", previous)))));
    }
}
