using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.DivergenceSupport;

internal sealed class ZeroSupportDefectEqualityDocument : IScribeDocumentDefinition
{
    private const string LeanPrefix = "D5/S3/DivergenceSupport/ZeroSupportDefectEquality.";

    private static Formula Law(bool first) => F.Id(first ? "p" : "q");

    private static Formula ChannelOutput(bool first) => F.Seq(
        F.Open, F.Id("W"), Law(first), F.Close);

    private static Formula ChannelOutputAtY(bool first) => F.Seq(
        ChannelOutput(first), F.Open, F.Id("y"), F.Close);

    private static Formula Posterior(bool first) => F.Seq(
        F.Widehat, F.Grp(Law(first)), F.Underscore, F.Grp(F.Id("y")));

    private static Formula Divergence(Formula left, Formula right) => F.Seq(
        F.Id("D"), F.Open, left, F.Vert, F.Vert, F.Sp, right, F.Close);

    private static Formula Defect() => F.Seq(
        Divergence(Law(true), Law(false)), F.Sp, F.Minus, F.Sp,
        Divergence(ChannelOutput(true), ChannelOutput(false)));

    private static Formula Statement(Formula equalityCase) => F.Disp(F.Seq(
        F.Begin, F.Grp(F.Id("gathered")),
        F.Forall, F.Sp, F.Id("X"), F.Comma, F.Sp, F.Id("Y"), F.Esc,
        F.OpenBracket,
        F.Operatorname, F.Grp(F.Id("Fintype")), F.Open, F.Id("X"), F.Close,
        F.CloseBracket, F.Sp,
        F.OpenBracket,
        F.Operatorname, F.Grp(F.Id("Fintype")), F.Open, F.Id("Y"), F.Close,
        F.CloseBracket, F.Comma, F.RowBreak,
        F.Forall, F.Sp,
        F.Id("p"), F.Comma, F.Sp, F.Id("q"), F.Colon, F.Sp,
        F.Id("X"), F.To, F.Sp, F.Mathbb, F.Grp(F.Id("R")), F.Comma, F.Sp,
        F.Id("W"), F.Colon, F.Sp,
        F.Id("X"), F.To, F.Sp, F.Id("Y"), F.To, F.Sp,
        F.Mathbb, F.Grp(F.Id("R")), F.Comma, F.RowBreak,
        F.Open,
        F.Open, F.Forall, F.Sp, F.Id("x"), F.Colon, F.Sp, F.Id("X"), F.Comma, F.Sp,
        F.D(0), F.Le, F.Sp, Law(true), F.Open, F.Id("x"), F.Close, F.Close,
        F.Sp, F.Land, F.Sp,
        F.Sum, F.Underscore, F.Grp(F.Id("x")),
        Law(true), F.Open, F.Id("x"), F.Close, F.Eq, F.D(1),
        F.Close, F.Sp, F.Rightarrow, F.RowBreak,
        F.Open,
        F.Open, F.Forall, F.Sp, F.Id("x"), F.Colon, F.Sp, F.Id("X"), F.Comma, F.Sp,
        F.D(0), F.Le, F.Sp, Law(false), F.Open, F.Id("x"), F.Close, F.Close,
        F.Sp, F.Land, F.Sp,
        F.Sum, F.Underscore, F.Grp(F.Id("x")),
        Law(false), F.Open, F.Id("x"), F.Close, F.Eq, F.D(1),
        F.Close, F.Sp, F.Rightarrow, F.RowBreak,
        F.Open, F.Forall, F.Sp, F.Id("x"), F.Colon, F.Sp, F.Id("X"), F.Comma, F.Sp,
        Law(false), F.Open, F.Id("x"), F.Close, F.Eq, F.D(0),
        F.Sp, F.Rightarrow, F.Sp,
        Law(true), F.Open, F.Id("x"), F.Close, F.Eq, F.D(0), F.Close,
        F.Sp, F.Rightarrow, F.RowBreak,
        F.Open,
        F.Open, F.Forall, F.Sp,
        F.Id("x"), F.Colon, F.Sp, F.Id("X"), F.Comma, F.Sp,
        F.Id("y"), F.Colon, F.Sp, F.Id("Y"), F.Comma, F.Sp,
        F.D(0), F.Le, F.Sp,
        F.Id("W"), F.Open, F.Id("x"), F.Comma, F.Sp, F.Id("y"), F.Close,
        F.Close, F.Sp, F.Land, F.Sp,
        F.Open, F.Forall, F.Sp, F.Id("x"), F.Colon, F.Sp, F.Id("X"), F.Comma, F.Sp,
        F.Sum, F.Underscore, F.Grp(F.Id("y")),
        F.Id("W"), F.Open, F.Id("x"), F.Comma, F.Sp, F.Id("y"), F.Close,
        F.Eq, F.D(1), F.Close,
        F.Close, F.Sp, F.Rightarrow, F.RowBreak,
        Defect(), F.Sp, F.Eq, F.Sp, F.D(0),
        F.Sp, F.Leftrightarrow, F.RowBreak,
        equalityCase, F.Dot,
        F.End, F.Grp(F.Id("gathered"))));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Equality cases for the finite classical data-processing defect on general support.",
        H("When the General-Support Data-Processing Defect Vanishes"),
        Blocks(
            Paragraph(Text(
                "The frozen ZeroSupportDefect module proved that the data-processing defect is "
                + "nonnegative, but it did not characterize equality. The two results below "
                + "supply exactly that missing case under the same hypotheses, so nonnegativity "
                + "and vanishing now form a matched pair on general support.")),
            Paragraph(Text(
                "Both results rest on the frozen general-support chain identity. It expresses the "
                + "input divergence as the output divergence plus a finite output-weighted sum of "
                + "posterior divergences. Every summand is nonnegative, and a finite sum of "
                + "nonnegative real numbers vanishes exactly when every summand vanishes. The "
                + "frozen KL equality characterization then identifies a zero posterior "
                + "divergence with equality of the two posteriors wherever the output weight is "
                + "positive.")),
            Paragraph(Text(
                "Thus a channel loses no divergence exactly when it leaves the two posteriors "
                + "indistinguishable at every output letter to which the input law p gives "
                + "positive output mass.")),
            Paragraph(Text(
                "This criterion is neither a recovery map nor a statement of Petz sufficiency. "
                + "The module also does not assert that the criterion can be checked from the "
                + "input laws and the channel without computing the posteriors.")),
            Paragraph(Text(
                "Both displays are authored legally because the current statement projector has "
                + "no pinned projectable fixture for either declaration. Document construction "
                + "therefore records a ProjectionGap for each theorem.")),
            Describe.Lean(
                DescribeId.Create("zero-defect-is-pointwise-vanishing-of-weighted-posterior-divergence"),
                DeclarationHandle.Create(
                    LeanPrefix + "dpi_defect_eq_zero_iff_weighted_posterior_kl_zero"),
                H("Zero defect is pointwise vanishing of weighted posterior divergence"),
                StatementSource.FromAuthor(Statement(F.Seq(
                    F.Forall, F.Sp, F.Id("y"), F.Colon, F.Sp, F.Id("Y"), F.Comma, F.Sp,
                    ChannelOutputAtY(true), F.Sp,
                    Divergence(Posterior(true), Posterior(false)),
                    F.Sp, F.Eq, F.Sp, F.D(0)))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The first equivalence retains the weighted posterior terms themselves. "
                    + "After the chain identity rewrites the defect as their finite sum, "
                    + "nonnegativity makes equality of the sum equivalent to pointwise equality "
                    + "of every term with zero. This statement includes zero-output letters, "
                    + "whose weighted terms vanish by the frozen zero-output convention."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("zero-defect-is-zero-output-mass-or-equality-of-posteriors"),
                DeclarationHandle.Create(
                    LeanPrefix + "dpi_defect_eq_zero_iff_zero_output_or_posteriors_eq"),
                H("Zero defect is zero output mass or equality of posteriors"),
                StatementSource.FromAuthor(Statement(F.Seq(
                    F.Forall, F.Sp, F.Id("y"), F.Colon, F.Sp, F.Id("Y"), F.Comma, F.Sp,
                    ChannelOutputAtY(true), F.Sp, F.Eq, F.Sp, F.D(0),
                    F.Sp, F.Lor, F.Sp,
                    Posterior(true), F.Sp, F.Eq, F.Sp, Posterior(false)))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The second equivalence resolves each weighted zero term. At a zero-output "
                    + "letter the term vanishes automatically. Otherwise output absolute "
                    + "continuity makes both relevant output masses positive, so the positive "
                    + "weight can be cancelled and the frozen KL equality theorem makes the two "
                    + "posterior mass functions equal. The converse applies the same alternatives "
                    + "letter by letter."))),
                DescribeRole.Theorem)
        )));
}
