using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Divergence;

internal sealed class StrictDpiDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create("Posterior disequality makes the finite classical data-processing defect strictly positive.", H("Strict Positivity of the Classical Data-Processing Defect"), Blocks(
            Describe.Lean(DescribeId.Create("posterior-disequality-makes-the-classical-dpi-defect-positive"), DeclarationHandle.Create("D5/S3/Divergence/StrictDpi.dpi_defect_pos_of_posteriors_ne"), H("Posterior disequality makes the classical DPI defect positive"), StatementSource.FromAuthor(Disp(Seq(
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
                    F.Id("X"), To, Sp, Mathbb, Grp(F.Id("R")), Comma, Sp,
                    F.Id("W"), Colon, Sp,
                    F.Id("X"), To, Sp, F.Id("Y"), To, Sp, Mathbb, Grp(F.Id("R")),
                    Comma, RowBreak,
                    Open,
                    Open, Forall, Sp, F.Id("x"), Comma, Sp,
                    D(0), Lt, F.Id("p"), Open, F.Id("x"), Close, Close,
                    Sp, Land, Sp,
                    Sum, Underscore, Grp(F.Id("x")),
                    F.Id("p"), Open, F.Id("x"), Close, Eq, Sp, D(1),
                    Close, Sp, Rightarrow, RowBreak,
                    Open,
                    Open, Forall, Sp, F.Id("x"), Comma, Sp,
                    D(0), Lt, F.Id("q"), Open, F.Id("x"), Close, Close,
                    Sp, Land, Sp,
                    Sum, Underscore, Grp(F.Id("x")),
                    F.Id("q"), Open, F.Id("x"), Close, Eq, Sp, D(1),
                    Close, Sp, Rightarrow, RowBreak,
                    Open,
                    Open, Forall, Sp, F.Id("x"), Comma, Sp, F.Id("y"), Comma, Sp,
                    D(0), Lt,
                    F.Id("W"), Open, F.Id("x"), Comma, Sp, F.Id("y"), Close,
                    Close, Sp, Land, Sp,
                    Open, Forall, Sp, F.Id("x"), Comma, Sp,
                    Sum, Underscore, Grp(F.Id("y")),
                    F.Id("W"), Open, F.Id("x"), Comma, Sp, F.Id("y"), Close,
                    Eq, Sp, D(1), Close,
                    Close, Sp, Rightarrow, RowBreak,
                    Open, Exists, Sp, F.Id("y"), Colon, Sp, F.Id("Y"), Comma, Sp,
                    Widehat, Grp(F.Id("p")), Underscore, Grp(F.Id("y")),
                    Neq,
                    Widehat, Grp(F.Id("q")), Underscore, Grp(F.Id("y")), Close,
                    Sp, Rightarrow, RowBreak,
                    D(0), Lt,
                    F.Id("D"), Open, F.Id("p"), Vert, Vert, Sp, F.Id("q"), Close,
                    Minus,
                    F.Id("D"), Open,
                    F.Id("W"), F.Id("p"), Vert, Vert, Sp,
                    F.Id("W"), F.Id("q"), Close, Dot,
                    End, Grp(F.Id("gathered"))))), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text(
                        "Let X and Y be finite alphabets, with X nonempty. Strict DPI assumes " +
                        "strict positivity of p and q and of the stochastic kernel W. This is the " +
                        "channel-side convention, deliberately different from StrictGibbs's " +
                        "nonnegative absolutely continuous convention, so the binders must not be " +
                        "copied between the two modules. All three objects are normalized in the " +
                        "corresponding mass or row direction.")),
                    Paragraph(Text(
                        "The stricter convention is forced by the posterior formula: posterior W " +
                        "p y is a quotient by channelOutput W p y; the posterior is defined, and is " +
                        "positive, only when that denominator is positive. The same applies to q. " +
                        "StrictGibbs never divides, so discrete absolute continuity alone is enough " +
                        "to keep every logarithm meaningful.")),
                    Paragraph(Text(
                        "This theorem composes " +
                        "D5/S3/Divergence/DpiDefect.dpi_defect_nonneg with " +
                        "D5/S3/Divergence/PetzClassical.dpi_defect_zero_iff_posteriors_eq; " +
                        "nothing is re-proved. The nonnegative defect cannot be zero when the " +
                        "stated posterior disequality contradicts PetzClassical's equality " +
                        "characterization.")),
                    Paragraph(Text(
                        "The premise is not p ≠ q: it is ∃ y, posterior W p y ≠ posterior W q " +
                        "y. Distinct inputs are neither the hypothesis of this theorem nor claimed " +
                        "by it to be sufficient; this module says nothing about whether p ≠ q alone " +
                        "forces a strictly positive defect.")),
                    Paragraph(Text(
                        "PetzClassical's output-positivity side condition is discharged from these " +
                        "hypotheses by a Finset.sum_pos' argument; it is not assumed. Strict " +
                        "positivity of p and W makes each summand nonnegative and supplies a " +
                        "positive witness because X is nonempty.")),
                    Paragraph(Text(
                        "The honest limit is the full-support regime: the kernel and both inputs " +
                        "are strictly positive, so zero transition probabilities and zero-mass " +
                        "distributions remain outside this module. This scope is narrower than a " +
                        "boundary-aware channel theorem.")),
                    Paragraph(Text(
                        "This completes the defect cluster opened by PetzClassical: the defect is " +
                        "zero if and only if the posteriors are equal, hence the defect is strictly " +
                        "positive exactly when they differ. The displayed theorem packages the " +
                        "disequality-to-positivity direction."))), DescribeRole.Theorem))));
}
