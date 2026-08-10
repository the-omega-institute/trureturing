using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.RenyiDivergence;

internal sealed class DataProcessingDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        Header(
            "D5/S3/RenyiDivergence/DataProcessing",
            "Finite nonnegative row-stochastic processing cannot increase Renyi divergence at orders strictly between zero and one under positive overlap."),
        H("Data Processing for Finite Renyi Divergence"),
        Blocks(
            DocumentBlock.Describe.Theorem(
                DescribeId.Create("half-order-data-processing-is-a-corollary-of-frozen-results"),
                H("Half-order data processing is a corollary of frozen results"),
                LeanTheorem(
                    "D5/S3/RenyiDivergence/DataProcessing.renyi_divergence_one_half_channel_le"),
                Disp(Seq(
                    Begin, Grp(F.Id("gathered")),
                    Forall, Sp, F.Id("X"), Comma, Sp, F.Id("Y"), Esc,
                    OpenBracket,
                    Operatorname, Grp(F.Id("Fintype")), Open, F.Id("X"), Close,
                    CloseBracket, Sp,
                    OpenBracket,
                    Operatorname, Grp(F.Id("Fintype")), Open, F.Id("Y"), Close,
                    CloseBracket, Comma, RowBreak,
                    Forall, Sp, F.Id("p"), Comma, Sp, F.Id("q"), Colon, Sp,
                    F.Id("X"), To, Sp, Mathbb, Grp(F.Id("R")), Comma, Sp,
                    F.Id("W"), Colon, Sp,
                    F.Id("X"), To, Sp, F.Id("Y"), To, Sp, Mathbb, Grp(F.Id("R")), Comma,
                    RowBreak,
                    Open,
                    Open, Forall, Sp, F.Id("x"), Comma, Sp,
                    D(0), Le, Sp, F.Id("p"), Open, F.Id("x"), Close, Close,
                    Sp, Land, Sp, RowBreak,
                    Open, Forall, Sp, F.Id("x"), Comma, Sp,
                    D(0), Le, Sp, F.Id("q"), Open, F.Id("x"), Close, Close,
                    Sp, Land, Sp, RowBreak,
                    Open, Exists, Sp, F.Id("x"), Comma, Sp,
                    D(0), Lt, Sp, F.Id("p"), Open, F.Id("x"), Close,
                    Sp, Land, Sp,
                    D(0), Lt, Sp, F.Id("q"), Open, F.Id("x"), Close, Close,
                    Sp, Land, Sp, RowBreak,
                    Open,
                    Open, Forall, Sp, F.Id("x"), Comma, Sp, F.Id("y"), Comma, Sp,
                    D(0), Le, Sp,
                    F.Id("W"), Open, F.Id("x"), Comma, Sp, F.Id("y"), Close, Close,
                    Sp, Land, Sp,
                    Open, Forall, Sp, F.Id("x"), Comma, Sp,
                    Sum, Sp, Underscore, Grp(F.Id("y")), Sp,
                    F.Id("W"), Open, F.Id("x"), Comma, Sp, F.Id("y"), Close,
                    Eq, D(1), Close,
                    Close, Close,
                    Sp, Rightarrow, Sp, RowBreak,
                    F.Id("D"), Underscore, Grp(Frac, Grp(D(1)), Grp(D(2))), Open,
                    Operatorname, Grp(F.Id("channelOutput")),
                    Open, F.Id("W"), Comma, Sp, F.Id("p"), Close,
                    Vert, Sp, Vert, Sp,
                    Operatorname, Grp(F.Id("channelOutput")),
                    Open, F.Id("W"), Comma, Sp, F.Id("q"), Close, Close,
                    Le, Sp,
                    F.Id("D"), Underscore, Grp(Frac, Grp(D(1)), Grp(D(2))), Open,
                    F.Id("p"), Vert, Sp, Vert, Sp, F.Id("q"), Close, Dot,
                    End, Grp(F.Id("gathered")))),
                DescribeProvenance.RepoDerived(),
                Blocks(
                    Paragraph(Text(
                        "This named theorem is a corollary of frozen results, not a new proof " +
                        "of the half-order mathematics. Its Lean doc comment opens with that " +
                        "provenance and expressly disclaims novelty at half order. The frozen theorem " +
                        "bhattacharyya_channel_le states that a nonnegative row-stochastic " +
                        "channel increases Bhattacharyya affinity, while the frozen identity " +
                        "renyi_divergence_one_half identifies D_(1/2) with -2 log BC. " +
                        "Monotonicity of the logarithm followed by multiplication by the " +
                        "negative factor -2 gives the displayed inequality in one step.")),
                    Paragraph(Text(
                        "Positive input overlap keeps the affinity strictly positive, so the " +
                        "logarithmic comparison is legitimate under the repository convention " +
                        "Real.log 0 = 0. Output nonnegativity follows directly from " +
                        "nonnegative input masses and channel entries. No normalization of p or " +
                        "q is used.")),
                    Paragraph(Text(
                        "The corollary is stated with explicit provenance because a consequence " +
                        "of an earlier frozen theorem is presented as that theorem's corollary, " +
                        "never as a rival derivation of the same structure. Its separate name " +
                        "also preserves the established half-order interface for later users.")),
                    Paragraph(Text(
                        "The corollary also serves as a consistency check on the general theorem " +
                        "below. The Lean module contains a compiled example whose conjunction " +
                        "has the corollary's exact statement on both sides: one conjunct is " +
                        "discharged by the frozen-material corollary, and the other by " +
                        "specializing the general theorem to alpha = 1/2. A general statement " +
                        "that silently disagreed with an already-frozen special case would " +
                        "signal an error in its formulation; the overlap is precisely where " +
                        "such an error is least costly to detect. The caller reproduced this " +
                        "compiled check independently.")))),
            DocumentBlock.Describe.Theorem(
                DescribeId.Create("sub-unit-renyi-divergence-obeys-data-processing"),
                H("Sub-unit Renyi divergence obeys data processing"),
                LeanTheorem(
                    "D5/S3/RenyiDivergence/DataProcessing.renyi_divergence_channel_le_of_lt_one"),
                Disp(Seq(
                    Begin, Grp(F.Id("gathered")),
                    Forall, Sp, F.Id("X"), Comma, Sp, F.Id("Y"), Esc,
                    OpenBracket,
                    Operatorname, Grp(F.Id("Fintype")), Open, F.Id("X"), Close,
                    CloseBracket, Sp,
                    OpenBracket,
                    Operatorname, Grp(F.Id("Fintype")), Open, F.Id("Y"), Close,
                    CloseBracket, Comma, RowBreak,
                    Forall, Sp, Alpha, Sp, InMacro, Sp,
                    Mathbb, Grp(F.Id("R")), Comma, Sp,
                    D(0), Lt, Sp, Alpha, Sp, Lt, Sp, D(1), Comma, RowBreak,
                    Forall, Sp, F.Id("p"), Comma, Sp, F.Id("q"), Colon, Sp,
                    F.Id("X"), To, Sp, Mathbb, Grp(F.Id("R")), Comma, Sp,
                    F.Id("W"), Colon, Sp,
                    F.Id("X"), To, Sp, F.Id("Y"), To, Sp, Mathbb, Grp(F.Id("R")), Comma,
                    RowBreak,
                    Open,
                    Open, Forall, Sp, F.Id("x"), Comma, Sp,
                    D(0), Le, Sp, F.Id("p"), Open, F.Id("x"), Close, Close,
                    Sp, Land, Sp, RowBreak,
                    Open, Forall, Sp, F.Id("x"), Comma, Sp,
                    D(0), Le, Sp, F.Id("q"), Open, F.Id("x"), Close, Close,
                    Sp, Land, Sp, RowBreak,
                    Open, Exists, Sp, F.Id("x"), Comma, Sp,
                    D(0), Lt, Sp, F.Id("p"), Open, F.Id("x"), Close,
                    Sp, Land, Sp,
                    D(0), Lt, Sp, F.Id("q"), Open, F.Id("x"), Close, Close,
                    Sp, Land, Sp, RowBreak,
                    Open,
                    Open, Forall, Sp, F.Id("x"), Comma, Sp, F.Id("y"), Comma, Sp,
                    D(0), Le, Sp,
                    F.Id("W"), Open, F.Id("x"), Comma, Sp, F.Id("y"), Close, Close,
                    Sp, Land, Sp,
                    Open, Forall, Sp, F.Id("x"), Comma, Sp,
                    Sum, Sp, Underscore, Grp(F.Id("y")), Sp,
                    F.Id("W"), Open, F.Id("x"), Comma, Sp, F.Id("y"), Close,
                    Eq, D(1), Close,
                    Close, Close,
                    Sp, Rightarrow, Sp, RowBreak,
                    F.Id("D"), Underscore, Grp(Alpha, Sp), Open,
                    Operatorname, Grp(F.Id("channelOutput")),
                    Open, F.Id("W"), Comma, Sp, F.Id("p"), Close,
                    Vert, Sp, Vert, Sp,
                    Operatorname, Grp(F.Id("channelOutput")),
                    Open, F.Id("W"), Comma, Sp, F.Id("q"), Close, Close,
                    Le, Sp,
                    F.Id("D"), Underscore, Grp(Alpha, Sp), Open,
                    F.Id("p"), Vert, Sp, Vert, Sp, F.Id("q"), Close, Dot,
                    End, Grp(F.Id("gathered")))),
                DescribeProvenance.RepoDerived(),
                Blocks(
                    Paragraph(Text(
                        "Processing an observation cannot increase finite Renyi divergence at " +
                        "any real order strictly between zero and one. The repository already " +
                        "contained data processing for classical divergence and total " +
                        "variation, together with affinity growth for the Bhattacharyya " +
                        "coefficient and contraction of squared Hellinger distance. This " +
                        "theorem places the sub-unit Renyi family in the same finite-channel " +
                        "framework.")),
                    Paragraph(Text(
                        "The theorem covers every real alpha with 0 < alpha < 1, every pair of " +
                        "finite pointwise nonnegative mass functions p and q having at least one " +
                        "coordinate at which both are positive, and every pointwise " +
                        "nonnegative row-stochastic channel W. Neither input is required to be " +
                        "normalized. This distinction is substantive: the sibling squared " +
                        "Hellinger contraction does require both inputs to have unit mass.")),
                    Paragraph(Text(
                        "For each output coordinate, finite Holder bounds the sum of the mixed " +
                        "alpha and 1-alpha powers by the corresponding powers of the two output " +
                        "masses. Summation over outputs, interchange of the finite sums, and the " +
                        "unit row sums of W show that the Renyi power sum cannot decrease under " +
                        "the channel. Positive overlap makes the input power sum strictly " +
                        "positive. The logarithm therefore preserves the comparison, whereas " +
                        "the prefactor 1/(alpha-1) is nonpositive and reverses it, yielding the " +
                        "displayed data-processing inequality.")),
                    Paragraph(Text(
                        "At alpha = 1 the repository's definition is literally zero because its " +
                        "totalized prefactor vanishes. Data processing at that order is thus a " +
                        "trivial equality for this definition, not the order-one or " +
                        "Kullback--Leibler interpretation. No such interpretation is claimed.")),
                    Paragraph(Text(
                        "Above order one, the displayed theorem is false under its minimal " +
                        "support hypotheses, and the Lean module compiles a counterexample. At " +
                        "order two, take the uniform law p on Bool and a point mass q, which " +
                        "still have positive overlap, and send both through the constant channel " +
                        "to Unit. The output divergence is 0, while the input divergence is " +
                        "-2 log 2, so the asserted inequality 0 <= -2 log 2 fails.")),
                    Paragraph(Text(
                        "This failure is produced by the formalization's totalizing conventions, " +
                        "not by Renyi divergence itself. At the unsupported coordinate, the " +
                        "order-two contribution is mathematically infinite, but Lean's x/0 = 0 " +
                        "erases it. The surrounding definition likewise stipulates " +
                        "Real.log 0 = 0; together these conventions replace support-boundary " +
                        "infinities by finite values. The compiled example records an artifact of this " +
                        "formal definition and must not be read as evidence that mathematical " +
                        "Renyi data processing fails above order one.")),
                    Paragraph(Text(
                        "Nonpositive orders are not claimed. The Holder conjugates used by the " +
                        "proof require alpha and 1-alpha to be positive, and hence require " +
                        "strictly positive sub-unit order.")),
                    Paragraph(Text(
                        "No order-one limit, data-processing theorem above order one, equality " +
                        "characterization, or measure-theoretic analogue is claimed. All " +
                        "logarithms are natural, so the units are nats.")))))));
}
