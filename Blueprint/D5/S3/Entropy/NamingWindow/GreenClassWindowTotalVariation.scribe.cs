using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Entropy.NamingWindow;

internal sealed class GreenClassWindowTotalVariationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Total variation of a finite naming-window law lies below the sum of its coordinate " +
        "variations and above every single coordinate variation.",
        H("Green-Class Window Total Variation"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("window-total-variation-is-bounded-by-the-coordinate-sum"),
                DeclarationHandle.Create(
                    "D5/S3/Entropy/NamingWindow/GreenClassWindowTotalVariation.totalVariation_windowLaw_le_sum"),
                H("Window total variation is bounded by the coordinate sum"),
                StatementSource.FromAuthor(Disp(Seq(
                    Operatorname, Grp(F.Id("TV")), Open,
                    Operatorname, Grp(F.Id("windowLaw")), Open, F.Id("p"), Close,
                    Comma, Sp,
                    Operatorname, Grp(F.Id("windowLaw")), Open, F.Id("q"), Close, Close,
                    Sp, Le, Sp,
                    Sum, Underscore, Grp(F.Id("i")), Sp,
                    Operatorname, Grp(F.Id("TV")), Open,
                    F.Id("p"), Underscore, Grp(F.Id("i")), Comma, Sp,
                    F.Id("q"), Underscore, Grp(F.Id("i")), Close, Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For nonnegative normalized coordinate laws, change the product one " +
                        "coordinate at a time. The triangle inequality bounds the endpoint " +
                        "distance by the sum of the distances along this finite hybrid path.")),
                    Paragraph(Text(
                        "At an insertion step, all unchanged factors are collected outside the " +
                        "absolute coordinate difference. Finite sum-product factorization makes " +
                        "their total mass one, leaving exactly twice the coordinate total " +
                        "variation before the defining one-half factor is applied.")),
                    Paragraph(Text(
                        "Induction over the coordinate finset therefore gives the displayed " +
                        "upper bound, including the empty-window case. No equality claim or " +
                        "strictness witness is included."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("each-coordinate-total-variation-is-bounded-by-the-window"),
                DeclarationHandle.Create(
                    "D5/S3/Entropy/NamingWindow/GreenClassWindowTotalVariation.totalVariation_le_totalVariation_windowLaw"),
                H("Each coordinate total variation is bounded by the window"),
                StatementSource.FromAuthor(Disp(Seq(
                    Operatorname, Grp(F.Id("TV")), Open,
                    F.Id("p"), Underscore, Grp(F.Id("i")), Comma, Sp,
                    F.Id("q"), Underscore, Grp(F.Id("i")), Close,
                    Sp, Le, Sp,
                    Operatorname, Grp(F.Id("TV")), Open,
                    Operatorname, Grp(F.Id("windowLaw")), Open, F.Id("p"), Close,
                    Comma, Sp,
                    Operatorname, Grp(F.Id("windowLaw")), Open, F.Id("q"), Close, Close, Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Project a window assignment to coordinate i through the deterministic " +
                        "indicator channel. The channel is nonnegative and row-stochastic because " +
                        "exactly one output letter agrees with the selected coordinate.")),
                    Paragraph(Text(
                        "Normalization of every coordinate outside i collapses the channel output " +
                        "to p_i, and similarly to q_i. Total-variation data processing then gives " +
                        "the lower half of the window sandwich."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("green-class-window-total-variation-has-the-coordinate-sum-bound"),
                DeclarationHandle.Create(
                    "D5/S3/Entropy/NamingWindow/GreenClassWindowTotalVariation.totalVariation_greenClass_window_le_sum"),
                H("Green-class window total variation has the coordinate-sum bound"),
                StatementSource.FromAuthor(Disp(Seq(
                    Operatorname, Grp(F.Id("TV")), Open,
                    Operatorname, Grp(F.Id("windowLaw")), Open,
                    Operatorname, Grp(F.Id("coordLaw")), Open, F.Id("mu"), Close, Close,
                    Comma, Sp,
                    Operatorname, Grp(F.Id("windowLaw")), Open,
                    Operatorname, Grp(F.Id("coordLaw")), Open, F.Id("nu"), Close, Close, Close,
                    Sp, Le, Sp,
                    Sum, Underscore, Grp(F.Id("i")), Sp,
                    Operatorname, Grp(F.Id("TV")), Open,
                    Operatorname, Grp(F.Id("coordLaw")), Open,
                    F.Id("mu"), Comma, Sp, F.Id("i"), Close,
                    Comma, Sp,
                    Operatorname, Grp(F.Id("coordLaw")), Open,
                    F.Id("nu"), Comma, Sp, F.Id("i"), Close, Close, Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "A probability measure on the finite alphabet gives a nonnegative " +
                        "normalized real coordinate law by singleton evaluation and conversion " +
                        "from extended nonnegative reals.")),
                    Paragraph(Text(
                        "Applying the general window upper bound to the coordinates selected by " +
                        "the finite set S and reindexing the subtype sum yields the Green-class " +
                        "specialization."))),
                DescribeRole.Theorem))));
}
