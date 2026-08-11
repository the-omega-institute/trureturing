using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Phase.Interference;

internal sealed class DominantPartialQuotientGapDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        Header(
            "D5/S1/Phase/Interference/DominantPartialQuotientGap",
            "A dominant term leaves a nonnegative reverse-triangle gap below a finite "
            + "complex sum."),
        H("Dominant Partial-Quotient Gap"),
        Blocks(
            DocumentBlock.Describe.Theorem(
                DescribeId.Create("dominant-partial-quotient-gap-lemma"),
                H("A dominant term leaves a lower gap"),
                LeanTheorem(
                    "D5/S1/Phase/Interference/DominantPartialQuotientGap."
                    + "dominant_partial_quotient_gap"),
                Disp(Seq(
                    Forall, Sp, F.Id("S"), Comma, Sp, F.Id("a"), Comma, Sp,
                    F.Id("k"), Comma, Esc,
                    F.Id("k"), Sp, InMacro, Sp, F.Id("S"), Sp, Land, Sp,
                    Sum, Sp, Underscore,
                    Grp(F.Id("i"), Sp, InMacro, Sp, F.Id("S"), Setminus,
                        OpenBrace, F.Id("k"), CloseBrace), Sp,
                    Bar, F.Id("a"), Underscore, Grp(F.Id("i")), Bar,
                    Sp, Le, Sp,
                    Bar, F.Id("a"), Underscore, Grp(F.Id("k")), Bar,
                    Sp, Rightarrow, Sp,
                    D(0), Sp, Le, Sp,
                    Bar, F.Id("a"), Underscore, Grp(F.Id("k")), Bar, Minus,
                    Sum, Sp, Underscore,
                    Grp(F.Id("i"), Sp, InMacro, Sp, F.Id("S"), Setminus,
                        OpenBrace, F.Id("k"), CloseBrace), Sp,
                    Bar, F.Id("a"), Underscore, Grp(F.Id("i")), Bar,
                    Sp, Le, Sp,
                    Bar, Sum, Sp, Underscore,
                    Grp(F.Id("i"), Sp, InMacro, Sp, F.Id("S")), Sp,
                    F.Id("a"), Underscore, Grp(F.Id("i")), Bar)),
                DescribeProvenance.RepoDerived(),
                Blocks(
                    Paragraph(Text(
                        "Let S be a finite support for complex terms a_i and let k belong to S. "
                        + "If the norm of a_k is at least the sum of the norms of every other "
                        + "supported term, then the difference is nonnegative and is a lower "
                        + "bound for the norm of the full sum. Strict dominance therefore makes "
                        + "the displayed gap positive.")),
                    Paragraph(Text(
                        "Pinned Mathlib was searched before proving. `norm_sub_norm_le` supplies "
                        + "the reverse triangle inequality and `norm_sum_le` bounds the norm of "
                        + "the erased remainder by its sum of norms. `Finset.sum_erase_add` only "
                        + "restores the selected term. The declaration is a thin named wrapper "
                        + "over those results.")),
                    Paragraph(Text(
                        "The nearest repository theorem, "
                        + "`SeatTowerConsequences.dominant_term_gap_bound`, is an unconditional "
                        + "integer leading-term bound. It does not provide this selected finite "
                        + "complex family, the dominance premise, or the nonnegative-gap result. "
                        + "No dominant partial-quotient identification is asserted here.")))
            ),
            DocumentBlock.Describe.Theorem(
                DescribeId.Create("strict-dominance-positive-gap-example"),
                H("The positive gap is attained by an explicit family"),
                LeanTheorem(
                    "D5/S1/Phase/Interference/DominantPartialQuotientGap."
                    + "strict_dominance_positive_gap_example"),
                Disp(Seq(
                    OpenBrace, D(2), Comma, Sp, Minus, D(1), CloseBrace, Colon, Sp,
                    D(1), Sp, Lt, Sp, D(2), Sp, Land, Sp,
                    D(0), Sp, Lt, Sp, D(2), Minus, D(1), Sp, Eq, Sp,
                    Bar, D(2), Minus, D(1), Bar, Sp, Eq, Sp, D(1))),
                DescribeProvenance.RepoDerived(),
                Blocks(Paragraph(Text(
                    "On Fin 2 take the complex family (2, -1), support both indices, and select "
                    + "the first. The remainder norm sum is one, strictly below the dominant "
                    + "norm two. The resulting gap is one and the full sum also has norm one, "
                    + "so the lower bound is positive and attained rather than vacuous.")))
            ))));
}
