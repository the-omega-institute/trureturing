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
                        "to one. These are exactly the hypotheses required by the wave-3 " +
                        "identity; nothing beyond them is assumed.")),
                    Paragraph(Text(
                        "This theorem is a composition of repository results, not new divergence " +
                        "machinery. The wave-3 identity " +
                        "D5/S3/Divergence/ClassicalDPI.classical_dpi_identity supplies the exact " +
                        "decomposition of input divergence into output divergence plus an " +
                        "output-weighted sum of posterior divergences. The Grandmother theorem " +
                        "D5/S3/Divergence/GrandmotherTheorem.kl_divergence_nonneg supplies " +
                        "nonnegativity of each posterior divergence, and Finset.sum_nonneg " +
                        "combines those pointwise bounds.")),
                    Paragraph(Text(
                        "The Grandmother theorem's premises are discharged, not assumed: each " +
                        "posterior is strictly positive and sums to one, proved directly from " +
                        "the definitions and positivity of the output mass. Its " +
                        "absolute-continuity premise is trivial because the second posterior is " +
                        "strictly positive.")),
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
