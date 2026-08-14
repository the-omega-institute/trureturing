using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Complexity;

internal sealed class MechanicalSubshiftInterceptDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "At an irrational slope, every intercept gives the same lower mechanical factor "
            + "language and subshift, while equality of subshifts is equivalent to equality "
            + "of slopes.",
        H("Intercept Independence of Irrational Mechanical Subshifts"),
        Blocks(
            Paragraph(Text(
                "Fix an irrational real slope alpha in the half-open interval from zero to one. "
                + "Finite breakpoint cells identify factors across arbitrary real intercepts, "
                + "so both the finite language and its prefix-language subshift depend only on "
                + "the slope.")),
            Describe.Lean(
                DescribeId.Create("mechanical-subshift-intercept-independence"),
                DeclarationHandle.Create(
                    "D5/S1/Words/Complexity/MechanicalSubshiftIntercept."
                        + "wordSubshift_intercept_independent"),
                H("The mechanical subshift is independent of the intercept"),
                StatementSource.FromAuthor(Disp(Seq(
                    D(0), Sp, Leq, Sp, Alpha, Sp, Lt, Sp, D(1), Sp, Land, Sp,
                    Operatorname, Grp(F.Id("Irrational")), Open, Alpha, Close,
                    Sp, Rightarrow, Sp,
                    F.Id("X"), Underscore, Grp(Alpha, Comma, Sp, SigmaLower),
                    Sp, Eq, Sp,
                    F.Id("X"), Underscore, Grp(Alpha, Comma, Sp, Rho)))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The word at the second intercept belongs to the subshift generated at the "
                    + "first intercept. Irrational mechanical minimality then identifies the "
                    + "two generated subshifts."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("mechanical-factor-set-intercept-independence"),
                DeclarationHandle.Create(
                    "D5/S1/Words/Complexity/MechanicalSubshiftIntercept."
                        + "lowerMechanicalFactorSet_intercept_independent"),
                H("The finite factor language is independent of the intercept"),
                StatementSource.FromAuthor(Disp(Seq(
                    Operatorname, Grp(F.Id("Irrational")), Open, Alpha, Close,
                    Sp, Rightarrow, Sp,
                    F.Id("F"), Underscore, Grp(Alpha, Comma, Sp, Rho),
                    Open, F.Id("n"), Close, Sp, Eq, Sp,
                    F.Id("F"), Underscore, Grp(Alpha, Comma, Sp, SigmaLower),
                    Open, F.Id("n"), Close))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For each factor occurrence, a right-stable phase interval preserves all "
                    + "breakpoint comparisons through its length. Density of irrational "
                    + "rotation supplies a matching phase at the other intercept; symmetry "
                    + "gives equality of the two factor sets."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("mechanical-subshift-slope-classification"),
                DeclarationHandle.Create(
                    "D5/S1/Words/Complexity/MechanicalSubshiftIntercept."
                        + "wordSubshift_eq_iff_slope_eq"),
                H("Mechanical subshifts coincide exactly at equal slopes"),
                StatementSource.FromAuthor(Disp(Seq(
                    D(0), Sp, Leq, Sp, Alpha, Sp, Lt, Sp, D(1), Sp, Land, Sp,
                    D(0), Sp, Leq, Sp, F.Id("beta"), Sp, Lt, Sp, D(1), Sp, Land, Sp,
                    Operatorname, Grp(F.Id("Irrational")), Open, Alpha, Close,
                    Sp, Rightarrow, Sp, Open,
                    F.Id("X"), Underscore, Grp(Alpha, Comma, Sp, Rho),
                    Sp, Eq, Sp,
                    F.Id("X"), Underscore, Grp(F.Id("beta"), Comma, Sp, SigmaLower),
                    Sp, Iff, Sp, Alpha, Sp, Eq, Sp, F.Id("beta"), Close))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Subshift equality forces slope equality by true-letter density rigidity. "
                    + "Conversely, after identifying the slopes, intercept independence gives "
                    + "the required subshift equality."))),
                DescribeRole.Theorem))));
}
