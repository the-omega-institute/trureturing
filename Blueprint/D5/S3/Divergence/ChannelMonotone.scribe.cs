using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Divergence;

internal sealed class ChannelMonotoneDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        Header(
            "D5/S3/Divergence/ChannelMonotone",
            "A strictly positive finite channel cannot increase finite real-valued classical KL divergence."),
        H("Channel Monotonicity of Finite Classical KL Divergence"),
        Blocks(
            DocumentBlock.Describe.Theorem(
                DescribeId.Create("a-strictly-positive-finite-channel-does-not-increase-classical-kl-divergence"),
                H("A strictly positive finite channel does not increase classical KL divergence"),
                LeanTheorem(
                    "D5/S3/Divergence/ChannelMonotone.kl_divergence_channel_le"),
                Disp(Seq(
                    Begin, Grp(F.Id("gathered")),
                    Forall, Sp, F.Id("X"), Comma, Sp, F.Id("Y"), Esc,
                    OpenBracket,
                    Operatorname, Grp(F.Id("Fintype")), Open, F.Id("X"), Close,
                    CloseBracket, Sp,
                    OpenBracket,
                    Operatorname, Grp(F.Id("Nonempty")), Open, F.Id("X"), Close,
                    CloseBracket, Sp,
                    OpenBracket,
                    Operatorname, Grp(F.Id("Fintype")), Open, F.Id("Y"), Close,
                    CloseBracket, Comma, RowBreak,
                    Forall, Sp,
                    F.Id("p"), Comma, Sp, F.Id("q"), Colon, Sp,
                    F.Id("X"), To, Mathbb, Grp(F.Id("R")), Comma, Sp,
                    F.Id("W"), Colon, Sp,
                    F.Id("X"), To, Sp, F.Id("Y"), To, Mathbb, Grp(F.Id("R")),
                    Comma, RowBreak,
                    Open,
                    Open, Forall, Sp, F.Id("x"), Colon, Sp, F.Id("X"), Comma,
                    Sp, D(0), Lt, F.Id("p"), Open, F.Id("x"), Close, Close,
                    Sp, Land, Sp,
                    Sum, Underscore, Grp(F.Id("x")),
                    F.Id("p"), Open, F.Id("x"), Close, Eq, D(1),
                    Close, Sp, Rightarrow, RowBreak,
                    Open,
                    Open, Forall, Sp, F.Id("x"), Colon, Sp, F.Id("X"), Comma,
                    Sp, D(0), Lt, F.Id("q"), Open, F.Id("x"), Close, Close,
                    Sp, Land, Sp,
                    Sum, Underscore, Grp(F.Id("x")),
                    F.Id("q"), Open, F.Id("x"), Close, Eq, D(1),
                    Close, Sp, Rightarrow, RowBreak,
                    Open,
                    Open, Forall, Sp,
                    F.Id("x"), Colon, Sp, F.Id("X"), Comma, Sp,
                    F.Id("y"), Colon, Sp, F.Id("Y"), Comma, Sp,
                    D(0), Lt, F.Id("W"), Open,
                    F.Id("x"), Comma, Sp, F.Id("y"), Close,
                    Close, Sp, Land, Sp,
                    Open, Forall, Sp, F.Id("x"), Colon, Sp, F.Id("X"), Comma, Sp,
                    Sum, Underscore, Grp(F.Id("y")),
                    F.Id("W"), Open, F.Id("x"), Comma, Sp, F.Id("y"), Close,
                    Eq, D(1), Close,
                    Close, Sp, Rightarrow, RowBreak,
                    F.Id("D"), Open,
                    F.Id("W"), F.Id("p"), Vert, Vert, Sp,
                    F.Id("W"), F.Id("q"), Close,
                    Sp, Le, Sp,
                    F.Id("D"), Open,
                    F.Id("p"), Vert, Vert, Sp, F.Id("q"), Close, Dot,
                    End, Grp(F.Id("gathered")))),
                DescribeProvenance.RepoDerived(),
                Blocks(
                    Paragraph(Text(
                        "Let X and Y be finite types, with X nonempty. Let p and q be strictly " +
                        "positive normalized real mass functions on X, and let W be a strictly " +
                        "positive stochastic kernel from X to Y, meaning that every row sums " +
                        "to one. These are exactly the hypotheses required by " +
                        "D5/S3/Divergence/DpiDefect.dpi_defect_nonneg; nothing beyond them is assumed.")),
                    Paragraph(Text(
                        "This module restates D5/S3/Divergence/DpiDefect.dpi_defect_nonneg in " +
                        "inequality form. The proof of the mathematical content lives in " +
                        "DpiDefect. ChannelMonotone only converts its nonnegative defect " +
                        "conclusion into the equivalent output-at-most-input inequality.")),
                    Paragraph(Text(
                        "This module is a redundant re-proof: the same proposition was already " +
                        "frozen as D5/S3/Divergence/DpiDefect.dpi_defect_nonneg before this module " +
                        "was deposited. The theorem remains true and machine-verified; the " +
                        "redundancy lies in this module, not in the mathematics. It is retained, " +
                        "rather than removed, only because the frozen ledger currently has no " +
                        "revoke writer (issue #1030); removal is the resolution that CLAUDE.md 第6条 " +
                        "would require. Therefore, this module is a documented compromise and " +
                        "does not by itself satisfy 唯一真源 / single source of truth. Readers and " +
                        "downstream work should depend on " +
                        "D5/S3/Divergence/DpiDefect.dpi_defect_nonneg, not on this module.")),
                    Paragraph(Text(
                        "This is the data-processing inequality that wave 11's " +
                        "D5/S3/Divergence/MarginalMonotone module explicitly did not claim. At " +
                        "the level of the data-processing operation, wave 11's first-coordinate " +
                        "marginalization is the special case of forgetting a coordinate. Its " +
                        "deterministic forgetting kernel has zero transition probabilities, so " +
                        "the wave-11 theorem is proved separately rather than by instantiating " +
                        "this theorem.")),
                    Paragraph(Text(
                        "This is the finite real-valued klDivergence of ClassicalDPI, the " +
                        "repository's single source for the definition, not a measure-theoretic " +
                        "divergence. Mathlib's InformationTheory.klDiv_compProd_eq_add is not " +
                        "used, and no ENNReal/finite-sum bridge is established here.")),
                    Paragraph(Text(
                        "The remaining limits are full-support requirements: strict positivity " +
                        "of the kernel and of both input distributions is required. Channels " +
                        "with zero transition probabilities and distributions with zero mass " +
                        "are outside this module's scope.")))))));
}
