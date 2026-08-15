using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.TotalVariation.Equality;

internal sealed class DataProcessingEqualityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Total-variation channel contraction is exact precisely when each output column avoids mixing the two strict sign supports of the input discrepancy.",
        H("Equality in Total-Variation Data Processing"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("total-variation-channel-equality-is-no-sign-mixing"),
                DeclarationHandle.Create(
                    "D5/S3/TotalVariation/Equality/DataProcessingEquality.total_variation_channel_eq_iff_no_sign_mixing"),
                H("Channel equality is absence of sign mixing"),
                StatementSource.FromAuthor(Disp(Seq(
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
                    Open, Forall, Sp, F.Id("x"), Comma, Sp, F.Id("y"), Comma, Sp,
                    D(0), Le, Sp, F.Id("W"), Open, F.Id("x"), Comma, Sp, F.Id("y"), Close,
                    Close, Sp, Land, Sp,
                    Open, Forall, Sp, F.Id("x"), Comma, Sp,
                    Sum, Underscore, Grp(F.Id("y")), Sp,
                    F.Id("W"), Open, F.Id("x"), Comma, Sp, F.Id("y"), Close,
                    Eq, Sp, D(1), Close, Close,
                    Sp, Rightarrow, Sp, RowBreak,
                    Operatorname, Grp(F.Id("TV")), Open,
                    Operatorname, Grp(F.Id("channelOutput")), Open,
                    F.Id("W"), Comma, Sp, F.Id("p"), Close, Comma, Sp,
                    Operatorname, Grp(F.Id("channelOutput")), Open,
                    F.Id("W"), Comma, Sp, F.Id("q"), Close, Close,
                    Eq, Sp,
                    Operatorname, Grp(F.Id("TV")), Open,
                    F.Id("p"), Comma, Sp, F.Id("q"), Close,
                    Sp, Leftrightarrow, Sp, RowBreak,
                    Forall, Sp, F.Id("y"), Comma, Sp,
                    Open,
                    Open, Forall, Sp, F.Id("x"), Comma, Sp,
                    F.Id("p"), Open, F.Id("x"), Close, Lt, Sp,
                    F.Id("q"), Open, F.Id("x"), Close, Sp, Rightarrow, Sp,
                    F.Id("W"), Open, F.Id("x"), Comma, Sp, F.Id("y"), Close,
                    Eq, Sp, D(0), Close,
                    Sp, Lor, Sp, RowBreak,
                    Open, Forall, Sp, F.Id("x"), Comma, Sp,
                    F.Id("q"), Open, F.Id("x"), Close, Lt, Sp,
                    F.Id("p"), Open, F.Id("x"), Close, Sp, Rightarrow, Sp,
                    F.Id("W"), Open, F.Id("x"), Comma, Sp, F.Id("y"), Close,
                    Eq, Sp, D(0), Close,
                    Close, Dot,
                    End, Grp(F.Id("gathered"))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let p and q be arbitrary real functions on a finite input carrier, and " +
                        "let W be a nonnegative row-stochastic channel. The channel preserves " +
                        "their total variation exactly when every output y kills all inputs from " +
                        "one of the two strict sign supports of p - q.")),
                    Paragraph(Text(
                        "The strict inequalities are essential at the boundary. Inputs with " +
                        "p(x) = q(x) impose no condition, and a zero channel weight contributes " +
                        "to neither sign. Thus a column may meet both strict supports as sets, " +
                        "but it cannot give positive weight to both; an identically zero output " +
                        "column satisfies both alternatives.")),
                    Paragraph(Text(
                        "The contraction proof is a sum of one triangle inequality for each " +
                        "output column. Row normalization preserves the total absolute input " +
                        "mass across all columns, so global equality holds exactly when every " +
                        "columnwise triangle inequality is an equality. A private finite signed-" +
                        "mass lemma identifies that equality with sign coherence, and channel " +
                        "nonnegativity converts coherence into the displayed support condition.")),
                    Paragraph(Text(
                        "No normalization, nonnegativity, or equal-mass assumption is placed on " +
                        "p and q. The result classifies equality for the fixed triple (p, q, W); " +
                        "it does not classify channels that preserve total variation for every " +
                        "input pair, and it states no measure-theoretic analogue."))),
                DescribeRole.Theorem))));
}
