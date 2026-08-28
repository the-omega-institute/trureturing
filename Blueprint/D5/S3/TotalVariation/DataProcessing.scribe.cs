using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.TotalVariation;

internal sealed class DataProcessingDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A nonnegative row-stochastic finite channel contracts total variation for arbitrary real input functions.",
        H("Data Processing for Finite Total Variation"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("stochastic-channels-contract-total-variation"),
                DeclarationHandle.Create("D5/S3/TotalVariation/DataProcessing.total_variation_channel_le"),
                H("Stochastic channels contract total variation"),
                StatementSource.FromAuthor(Disp(Seq(
                                    Begin, Grp(F.Id("gathered")),
                                    Forall, Sp, F.Id("X"), Comma, Sp, F.Id("Y"),
                                    Colon, Sp, Operatorname, Grp(F.Id("Type")), Comma, Esc,
                                    OpenBracket,
                                    Operatorname, Grp(F.Id("Fintype")), Open, F.Id("X"), Close,
                                    CloseBracket, Sp,
                                    OpenBracket,
                                    Operatorname, Grp(F.Id("Fintype")), Open, F.Id("Y"), Close,
                                    CloseBracket, Comma, RowBreak,
                                    Forall, Sp, F.Id("p"), Comma, Sp, F.Id("q"), Colon, Sp,
                                    F.Id("X"), To, Sp, Mathbb, Grp(F.Id("R")), Comma, Sp,
                                    F.Id("W"), Colon, Sp,
                                    F.Id("X"), To, Sp, F.Id("Y"), To, Sp, Mathbb, Grp(F.Id("R")), Comma, RowBreak,
                                    Open,
                                    Open, Forall, Sp, F.Id("x"), Comma, Sp, F.Id("y"), Comma, Sp,
                                    D(0), Le, Sp, F.Id("W"), Open, F.Id("x"), Comma, Sp, F.Id("y"), Close,
                                    Close, Sp, Land, Sp,
                                    Open, Forall, Sp, F.Id("x"), Comma, Sp,
                                    Sum, Underscore, Grp(F.Id("y")),
                                    F.Id("W"), Open, F.Id("x"), Comma, Sp, F.Id("y"), Close,
                                    Eq, D(1), Close, Close,
                                    Sp, Rightarrow, RowBreak,
                                    Operatorname, Grp(F.Id("TV")), Open,
                                    Operatorname, Grp(F.Id("channelOutput")),
                                    Open, F.Id("W"), Comma, Sp, F.Id("p"), Close, Comma, Sp,
                                    Operatorname, Grp(F.Id("channelOutput")),
                                    Open, F.Id("W"), Comma, Sp, F.Id("q"), Close, Close,
                                    Le, Sp,
                                    Operatorname, Grp(F.Id("TV")), Open, F.Id("p"), Comma, Sp, F.Id("q"), Close, Dot,
                                    End, Grp(F.Id("gathered"))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                                    Paragraph(Text(
                                        "No processing of an observation can make two laws easier to " +
                                        "distinguish. This contraction property is what makes total variation " +
                                        "a legitimate measure of statistical distinguishability, and it is " +
                                        "the total-variation counterpart of the divergence data-processing " +
                                        "result already frozen in this repository.")),
                                    Paragraph(Text(
                                        "The hypothesis set is strikingly small, and this economy is the " +
                                        "document's most informative point. Only the channel W is constrained: " +
                                        "its entries are nonnegative and every row sums to one. " +
                                        "The input mass functions p and q are arbitrary real functions. They " +
                                        "need not be nonnegative, neither function need be normalized, their " +
                                        "total masses need not be equal, and no absolute-continuity or " +
                                        "zero-support convention is imposed.")),
                                    Paragraph(Text(
                                        "This is a structural contrast with the frozen divergence theorem. " +
                                        "That result requires nonnegativity of both input mass functions, " +
                                        "normalization of both and hence equality of total mass, and the " +
                                        "zero-support implication expressing absolute continuity. Divergence " +
                                        "contains logarithms and division, so positivity and a convention at " +
                                        "zero support are indispensable. Total variation contains only " +
                                        "absolute values and finite sums, which impose none of these input " +
                                        "conditions. Channel nonnegativity is used only to replace |W(x,y)| " +
                                        "by W(x,y), while row normalization is used only to collapse the " +
                                        "factored channel mass to one.")),
                                    Paragraph(Text(
                                        "The proof route was chosen for strength, not elegance. For each output " +
                                        "coordinate y, the difference is rewritten as the sum over x of " +
                                        "(p(x)-q(x))W(x,y). The triangle inequality for finite sums bounds its " +
                                        "absolute value pointwise. Nonnegativity removes the absolute value " +
                                        "from W; the two finite sums are then interchanged; and row " +
                                        "normalization completes the estimate.")),
                                    Paragraph(Text(
                                        "A route through the variational characterization appears more " +
                                        "conceptual but is weaker here in two respects. It would import an " +
                                        "equal-mass assumption, and an output event pulls back through a " +
                                        "general channel only to a randomized input test. That approach would " +
                                        "therefore require a separate argument absent from the direct proof. " +
                                        "A route that forces extra hypotheses merely to appear conceptual is " +
                                        "the wrong choice.")),
                                    Paragraph(Text(
                                        "The inequality is genuinely strict. Take X = Bool, Y = Unit, and the " +
                                        "constant channel W(x,()) = 1; it is nonnegative and every row sums to " +
                                        "one. Let p(true) = 1 and p(false) = 0, while q(false) = 1 and " +
                                        "q(true) = 0. These are disjoint unit point masses, so their input total " +
                                        "variation is 1, whereas both channel outputs are the same unit mass and " +
                                        "therefore have total variation 0. This witness was compiled " +
                                        "independently. Thus the bound is not secretly an equality: a channel " +
                                        "that discards its input collapses all " +
                                        "distinguishability.")),
                                    Paragraph(Text(
                                        "This theorem supplies the contraction component of the " +
                                        "TotalVariation bucket's three-part narrative, alongside Pinsker's " +
                                        "bound and the metric structure with its variational characterization. " +
                                        "Where divergence is mentioned, logarithms are natural and the units " +
                                        "are nats.")),
                                    Paragraph(Text(
                                        "No reverse bound of Bretagnolle-Huber type is claimed. There is no " +
                                        "characterization of equality or of the channels that preserve total " +
                                        "variation, and no continuous or measure-theoretic analogue is given."))),
                DescribeRole.Theorem
            ))));
}
