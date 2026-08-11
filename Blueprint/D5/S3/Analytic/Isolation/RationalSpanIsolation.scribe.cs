using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Isolation;

internal sealed class RationalSpanIsolationDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef KrantzParks =
        LibraryNoteRef.Create("D5/L/Analytic/krantzparks2002primer");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        Header(
            "D5/S3/Analytic/Isolation/RationalSpanIsolation",
            "Fixed rational-span levels of a nonconstant real-analytic family are isolated."),
        H("Isolation of Fixed Rational-Span Levels"),
        Blocks(
            DocumentBlock.Describe.Theorem(
                DescribeId.Create("fixed-rational-span-levels-are-isolated"),
                H("Fixed rational-span levels are isolated"),
                LeanTheorem(
                    "D5/S3/Analytic/Isolation/RationalSpanIsolation.rational_span_level_set_codiscrete"),
                Disp(Seq(
                    Begin, Grp(F.Id("gathered")),
                    Forall, Sp, Iota, Sp,
                    OpenBracket, Operatorname, Grp(F.Id("Fintype")),
                    Open, Iota, Close, CloseBracket, Comma, RowBreak,
                    F.Id("P"), Subseteq, Mathbb, Grp(F.Id("R")), Comma, Sp,
                    F.Id("F"), Colon, Mathbb, Grp(F.Id("R")), To,
                    Mathbb, Grp(F.Id("R")), Comma, RowBreak,
                    F.Id("q"), Colon, Iota, To, Mathbb, Grp(F.Id("Q")), Comma, Sp,
                    F.Id("b"), Colon, Iota, To, Mathbb, Grp(F.Id("R")), Comma, RowBreak,
                    Operatorname, Grp(F.Id("IsConnected")), Open, F.Id("P"), Close,
                    Sp, Land, Sp,
                    Operatorname, Grp(F.Id("AnalyticOnNhd")),
                    Open, F.Id("F"), Comma, F.Id("P"), Close, Comma, RowBreak,
                    F.Id("x"), InMacro, Sp, F.Id("P"), Sp, Land, Sp,
                    F.Id("F"), Open, F.Id("x"), Close, Neq,
                    Sum, Underscore, Grp(F.Id("i"), InMacro, Sp, Iota),
                    F.Id("q"), Underscore, F.Id("i"),
                    F.Id("b"), Underscore, F.Id("i"), Sp, Rightarrow, Sp, RowBreak,
                    F.Id("F"), Caret, Grp(Minus, D(1)),
                    Open, OpenBrace,
                    Sum, Underscore, Grp(F.Id("i"), InMacro, Sp, Iota),
                    F.Id("q"), Underscore, F.Id("i"),
                    F.Id("b"), Underscore, F.Id("i"),
                    CloseBrace, Caret, Grp(F.Id("c")), Close,
                    InMacro, Sp, Operatorname, Grp(F.Id("codiscreteWithin")),
                    Open, F.Id("P"), Close, Dot,
                    End, Grp(F.Id("gathered")))),
                DescribeProvenance.LiteratureAttested(KrantzParks),
                Blocks(
                    Paragraph(Text(
                        "Fix a finite family of real values and one rational coefficient for "
                        + "each value. If a real-analytic function on a connected parameter "
                        + "set differs from their weighted sum at one point, the complement "
                        + "of that level set is codiscrete within the parameter set. On the "
                        + "real line, connected sets are intervals, and this is Mathlib's "
                        + "filter formulation of the level set being isolated.")),
                    Paragraph(Text(
                        "The source assumes that membership in the whole rational span is not "
                        + "identically true on any subinterval. For each fixed coefficient "
                        + "tuple, that hypothesis supplies the one unequal witness required by "
                        + "the formal theorem. The indexed family may contain repeated values; "
                        + "finiteness, rather than a duplicate-free enumeration, is the only "
                        + "property used by the displayed rational sum.")),
                    Paragraph(Text(
                        "Mathlib was searched before proving. The pinned library already "
                        + "provides `AnalyticOnNhd.preimage_zero_mem_codiscreteWithin`. The Lean "
                        + "proof is therefore a thin honest wrapper: it subtracts the fixed "
                        + "rational linear combination, applies that theorem, and rewrites the "
                        + "zero set as the original level set. Krantz and Parks supply the "
                        + "literature anchor for the classical one-variable real-analytic "
                        + "identity and isolated-zero principle; no new analytic proof is "
                        + "claimed here.")))
            ))));
}
