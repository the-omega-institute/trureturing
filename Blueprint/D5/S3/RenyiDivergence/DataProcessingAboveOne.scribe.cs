using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.RenyiDivergence;

internal sealed class DataProcessingAboveOneDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Above one, finite Renyi divergence obeys data processing under discrete absolute continuity, while a compiled order-two witness shows why that support hypothesis is necessary for the totalized definition.",
        H("Above-One Data Processing for Finite Renyi Divergence"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("above-one-renyi-divergence-obeys-data-processing-under-absolute-continuity"),
                DeclarationHandle.Create("D5/S3/RenyiDivergence/DataProcessingAboveOne.renyi_divergence_channel_le_of_one_lt_of_ac"),
                H("Above-one Renyi divergence obeys data processing under absolute continuity"),
                StatementSource.FromAuthor(Disp(Seq(
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
                    D(1), Lt, Sp, Alpha, Comma, RowBreak,
                    Forall, Sp, F.Id("p"), Comma, Sp, F.Id("q"), Colon, Sp,
                    F.Id("X"), To, Sp, Mathbb, Grp(F.Id("R")), Comma, Sp,
                    F.Id("W"), Colon, Sp,
                    F.Id("X"), To, Sp, F.Id("Y"), To, Sp, Mathbb, Grp(F.Id("R")),
                    Comma, RowBreak,
                    Open,
                    Open, Forall, Sp, F.Id("x"), Comma, Sp,
                    D(0), Le, Sp, F.Id("p"), Open, F.Id("x"), Close, Close,
                    Sp, Land, Sp, RowBreak,
                    Open, Forall, Sp, F.Id("x"), Comma, Sp,
                    D(0), Le, Sp, F.Id("q"), Open, F.Id("x"), Close, Close,
                    Sp, Land, Sp, RowBreak,
                    Open, Forall, Sp, F.Id("x"), Comma, Sp,
                    F.Id("q"), Open, F.Id("x"), Close, Eq, D(0),
                    Sp, Rightarrow, Sp, F.Id("p"), Open, F.Id("x"), Close, Eq, D(0), Close,
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
                    Close, Sp, Rightarrow, Sp, RowBreak,
                    F.Id("D"), Underscore, Grp(Alpha, Sp), Open,
                    Operatorname, Grp(F.Id("channelOutput")),
                    Open, F.Id("W"), Comma, Sp, F.Id("p"), Close,
                    Vert, Sp, Vert, Sp,
                    Operatorname, Grp(F.Id("channelOutput")),
                    Open, F.Id("W"), Comma, Sp, F.Id("q"), Close, Close,
                    Le, Sp,
                    F.Id("D"), Underscore, Grp(Alpha, Sp), Open,
                    F.Id("p"), Vert, Sp, Vert, Sp, F.Id("q"), Close, Dot,
                    End, Grp(F.Id("gathered"))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "This theorem closes the precise open sentence in the frozen below-one " +
                        "data-processing module: orders above one were excluded because, with merely " +
                        "nonnegative masses, missing support and zero powers could reverse the desired " +
                        "inequality. Discrete absolute continuity, namely q x = 0 implies p x = 0, is " +
                        "the stronger support hypothesis supplied here. The frozen sentence is: " +
                        "\"Orders above one are not covered: with merely nonnegative masses, missing " +
                        "support and zero powers can reverse the desired inequality. Stronger support " +
                        "hypotheses may recover that range, but no such theorem is claimed here.\"")),
                    Paragraph(Text(
                        "The sign bookkeeping reverses relative to the sub-unit theorem. When 0 < alpha < 1, " +
                        "the prefactor 1/(alpha - 1) is negative, so the power sum must increase and the " +
                        "prefactor reverses the logarithmic comparison. For alpha > 1 the prefactor is " +
                        "positive, so the power sum must decrease. Holder therefore uses the conjugate pair " +
                        "alpha and alpha/(alpha - 1), both strictly greater than one.")),
                    Paragraph(Text(
                        "No normalization and no pointwise strict positivity is assumed. Nonnegative p and q " +
                        "may share zero coordinates; absolute continuity only prevents p from being nonzero " +
                        "where q vanishes. The channel is likewise only pointwise nonnegative and " +
                        "row-stochastic.")),
                    Paragraph(Text(
                        "The authored display is legal because the current statement projector has no pinned " +
                        "projectable fixture for this declaration, so construction records a ProjectionGap " +
                        "rather than pretending that the presentation is Lean-derived."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("order-two-data-processing-fails-for-a-totalized-support-boundary"),
                DeclarationHandle.Create("D5/S3/RenyiDivergence/DataProcessingAboveOne.renyi_divergence_data_processing_failure_order_two"),
                H("Order two has a compiled Bool-to-Unit data-processing failure"),
                StatementSource.FromAuthor(Disp(Seq(
                    Begin, Grp(F.Id("gathered")),
                    F.Id("X"), Eq, F.Id("Bool"), Comma, Sp,
                    F.Id("Y"), Eq, F.Id("Unit"), Comma, Sp,
                    Alpha, Eq, D(2), Comma, RowBreak,
                    F.Id("p"), Eq, Open, Frac, Grp(D(1)), Grp(D(2)), Comma, Sp,
                    Frac, Grp(D(1)), Grp(D(2)), Close, Comma, Sp,
                    F.Id("q"), Eq, Open, D(1), Comma, Sp, D(0), Close, Comma, Sp,
                    F.Id("W"), Eq, D(1), Comma, RowBreak,
                    Open,
                    Open, F.Id("p"), Geq, Sp, D(0), Close, Sp, Land, Sp,
                    F.Id("p"), Eq, Sp, D(1), Comma, Sp,
                    Open, F.Id("q"), Geq, Sp, D(0), Close, Sp, Land, Sp,
                    F.Id("q"), Eq, Sp, D(1), Comma, Sp,
                    Open, F.Id("W"), Geq, Sp, D(0), Close, Sp, Land, Sp,
                    F.Id("W"), Eq, Sp, D(1), Close, Sp, Rightarrow, RowBreak,
                    F.Id("D"), Underscore, Grp(D(2)), Open,
                    Operatorname, Grp(F.Id("channelOutput")), Open, F.Id("W"), Comma, Sp, F.Id("p"), Close,
                    Vert, Sp, Vert, Sp,
                    Operatorname, Grp(F.Id("channelOutput")), Open, F.Id("W"), Comma, Sp, F.Id("q"), Close, Close,
                    Gt, Sp,
                    F.Id("D"), Underscore, Grp(D(2)), Open,
                    F.Id("p"), Vert, Sp, Vert, Sp, F.Id("q"), Close, Dot,
                    End, Grp(F.Id("gathered"))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "This is an explicit compiled counterexample at alpha = 2. The source takes X = Bool, " +
                        "Y = Unit, p = (1/2, 1/2), q = (1, 0), and the constant channel W x y = 1. Both " +
                        "masses are pointwise nonnegative and normalized, and W is pointwise nonnegative " +
                        "with every row sum equal to one. Nevertheless the post-channel divergence is 0, " +
                        "whereas the pre-channel divergence is -2 log 2, so the strict inequality is reversed.")),
                    Paragraph(Text(
                        "The witness makes the absolute-continuity hypothesis machine-proved necessary for this " +
                        "totalized formal definition rather than merely convenient. q has a zero coordinate " +
                        "where p is nonzero. At order two the corresponding contribution has a negative q exponent; " +
                        "the repository's totalization sends a zero base with that negative exponent to zero " +
                        "instead of infinity. The pre-channel divergence is therefore understated and becomes " +
                        "negative, while mixing through the constant channel raises it to zero.")),
                    Paragraph(Text(
                        "The counterexample does not establish that q must be pointwise strictly positive. The " +
                        "main theorem explicitly permits p and q to share zero coordinates, provided every zero " +
                        "of q is also a zero of p. Its claim is exactly the weaker discrete absolute-continuity " +
                        "condition.")),
                    Paragraph(Text(
                        "The authored display is legal for the same reason as the preceding theorem: no pinned " +
                        "projectable statement fixture exists for this declaration, and construction records the " +
                        "resulting ProjectionGap."))),
                DescribeRole.Theorem))));
}
