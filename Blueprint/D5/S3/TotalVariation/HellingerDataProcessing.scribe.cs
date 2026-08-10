using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.TotalVariation;

internal sealed class HellingerDataProcessingDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        Header(
            "D5/S3/TotalVariation/HellingerDataProcessing",
            "A nonnegative row-stochastic finite channel increases Bhattacharyya affinity and contracts squared Hellinger distance."),
        H("Hellinger Data Processing Through Affinity"),
        Blocks(
            DocumentBlock.Describe.Theorem(
                DescribeId.Create("stochastic-channels-contract-squared-hellinger-distance"),
                H("Stochastic channels contract squared Hellinger distance"),
                LeanTheorem(
                    "D5/S3/TotalVariation/HellingerDataProcessing.hellinger_sq_channel_le"),
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
                    F.Id("X"), To, Sp, F.Id("Y"), To, Sp, Mathbb, Grp(F.Id("R")), Comma, RowBreak,
                    Open,
                    Open,
                    Open, Forall, Sp, F.Id("x"), Comma, Sp,
                    D(0), Le, Sp, F.Id("p"), Open, F.Id("x"), Close, Close,
                    Sp, Land, Sp,
                    Sum, Sp, Underscore, Grp(F.Id("x")), Sp,
                    F.Id("p"), Open, F.Id("x"), Close, Eq, D(1),
                    Close, Sp, Land, RowBreak,
                    Open,
                    Open, Forall, Sp, F.Id("x"), Comma, Sp,
                    D(0), Le, Sp, F.Id("q"), Open, F.Id("x"), Close, Close,
                    Sp, Land, Sp,
                    Sum, Sp, Underscore, Grp(F.Id("x")), Sp,
                    F.Id("q"), Open, F.Id("x"), Close, Eq, D(1),
                    Close, Sp, Land, RowBreak,
                    Open,
                    Open, Forall, Sp, F.Id("x"), Comma, Sp, F.Id("y"), Comma, Sp,
                    D(0), Le, Sp, F.Id("W"), Open, F.Id("x"), Comma, Sp, F.Id("y"), Close,
                    Close, Sp, Land, Sp,
                    Open, Forall, Sp, F.Id("x"), Comma, Sp,
                    Sum, Sp, Underscore, Grp(F.Id("y")), Sp,
                    F.Id("W"), Open, F.Id("x"), Comma, Sp, F.Id("y"), Close,
                    Eq, D(1), Close,
                    Close, Close,
                    Sp, Rightarrow, Sp, RowBreak,
                    F.Id("H"), Caret, Grp(D(2)), Open,
                    Operatorname, Grp(F.Id("channelOutput")),
                    Open, F.Id("W"), Comma, Sp, F.Id("p"), Close, Comma, Sp,
                    Operatorname, Grp(F.Id("channelOutput")),
                    Open, F.Id("W"), Comma, Sp, F.Id("q"), Close, Close,
                    Le, Sp,
                    F.Id("H"), Caret, Grp(D(2)), Open,
                    F.Id("p"), Comma, Sp, F.Id("q"), Close, Dot,
                    End, Grp(F.Id("gathered")))),
                DescribeProvenance.RepoDerived(),
                Blocks(
                    Paragraph(Text(
                        "This module completes a data-processing trilogy at this stratum. The " +
                        "repository already contained data processing for Kullback--Leibler " +
                        "divergence, measured in nats, and contraction of total variation; " +
                        "squared Hellinger distance was the missing third member. In three " +
                        "different coordinate systems, all assert the same statistical " +
                        "principle: processing an observation cannot make two laws easier to " +
                        "distinguish.")),
                    Paragraph(Text(
                        "The passage through the Bhattacharyya coefficient reverses the " +
                        "inequality direction and must not be skimmed. The coefficient is an " +
                        "affinity: it measures overlap rather than separation. Accordingly, the " +
                        "auxiliary theorem proves BC(p,q) <= BC(Wp,Wq), the opposite direction " +
                        "from the total-variation inequality in the sibling module, while the " +
                        "displayed squared Hellinger distance decreases. This is not a typo: " +
                        "destroying information can only make two laws look more alike, which " +
                        "raises overlap and lowers every distance.")),
                    Paragraph(Text(
                        "The hypotheses separate into an informative hierarchy. Total-variation " +
                        "data processing assumes nothing about p and q: they may be arbitrary " +
                        "real functions, because absolute values and finite sums supply their " +
                        "own sign control. The affinity bound requires p and q to be pointwise " +
                        "nonnegative but does not require normalization, because its coordinates " +
                        "are square roots of products. Only the squared Hellinger bound requires " +
                        "full normalization, and only because it passes through the frozen " +
                        "identity H^2 = 2(1-BC), whose statement is restricted to probability " +
                        "vectors. Normalization enters exactly where that bridge identity " +
                        "demands it and nowhere earlier.")),
                    Paragraph(Text(
                        "The affinity proof is a pointwise Cauchy--Schwarz argument. For each " +
                        "output coordinate y, mathlib's Real.sum_sqrt_mul_sqrt_le gives " +
                        "sum_x sqrt(p(x)q(x))W(x,y) <= " +
                        "sqrt((sum_x p(x)W(x,y))(sum_x q(x)W(x,y))). The right-hand side is " +
                        "the overlap of the two mixed output masses at y. Summing over y, " +
                        "interchanging the finite sums, and collapsing every channel row sum " +
                        "to one yields affinity growth. No new definition is introduced.")),
                    Paragraph(Text(
                        "The Hellinger contraction is then a change of coordinates. The proof " +
                        "establishes nonnegativity and unit mass for both channel outputs, applies " +
                        "the frozen identity H^2 = 2(1-BC) to the input and output pairs, and " +
                        "transfers the affinity inequality by linear arithmetic.")),
                    Paragraph(Text(
                        "The local treatment of the output probability laws is deliberate. A " +
                        "repository search found no public declaration below D5/S3 stating that " +
                        "a stochastic channel maps probability vectors to probability vectors. " +
                        "Rather than promote a second public declaration in anticipation of use, " +
                        "the proof establishes output nonnegativity and unit mass locally. The " +
                        "repository lifts an abstraction at the second instance or under " +
                        "demonstrated pressure; if a second consumer appears, this is the fact " +
                        "to lift.")),
                    Paragraph(Text(
                        "No characterization of the channels that preserve affinity exactly is " +
                        "claimed. There is no reverse inequality, measure-theoretic analogue, or " +
                        "Renyi- or f-divergence generalization.")))))));
}
