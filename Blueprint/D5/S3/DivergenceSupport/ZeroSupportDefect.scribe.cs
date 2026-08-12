using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.DivergenceSupport;

internal sealed class ZeroSupportDefectDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Nonnegativity of the finite classical data-processing defect on general support.",
        H("The Data-Processing Defect on General Support"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("forgetting-quantity-dpi-nonneg-beyond-finite-classical-strict-positive"),
                DeclarationHandle.Create("D5/S3/DivergenceSupport/ZeroSupportDefect.dpi_defect_nonneg_zero_support"),
                H("The forgetting quantity stays nonnegative on general support"),
                StatementSource.FromAuthor(Disp(Seq(
                                    Begin, Grp(F.Id("gathered")),
                                    Forall, Sp, F.Id("X"), Comma, Sp, F.Id("Y"), Esc,
                                    OpenBracket,
                                    Operatorname, Grp(F.Id("Fintype")), Open, F.Id("X"), Close,
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
                                    Open, Forall, Sp, F.Id("x"), Colon, Sp, F.Id("X"), Comma, Sp,
                                    D(0), Le, Sp, F.Id("p"), Open, F.Id("x"), Close, Close,
                                    Sp, Land, Sp,
                                    Sum, Underscore, Grp(F.Id("x")),
                                    F.Id("p"), Open, F.Id("x"), Close, Eq, D(1),
                                    Close, Sp, Rightarrow, RowBreak,
                                    Open,
                                    Open, Forall, Sp, F.Id("x"), Colon, Sp, F.Id("X"), Comma, Sp,
                                    D(0), Le, Sp, F.Id("q"), Open, F.Id("x"), Close, Close,
                                    Sp, Land, Sp,
                                    Sum, Underscore, Grp(F.Id("x")),
                                    F.Id("q"), Open, F.Id("x"), Close, Eq, D(1),
                                    Close, Sp, Rightarrow, RowBreak,
                                    Open, Forall, Sp, F.Id("x"), Colon, Sp, F.Id("X"), Comma, Sp,
                                    F.Id("q"), Open, F.Id("x"), Close, Eq, D(0),
                                    Sp, Rightarrow, Sp,
                                    F.Id("p"), Open, F.Id("x"), Close, Eq, D(0), Close,
                                    Sp, Rightarrow, RowBreak,
                                    Open,
                                    Open, Forall, Sp,
                                    F.Id("x"), Colon, Sp, F.Id("X"), Comma, Sp,
                                    F.Id("y"), Colon, Sp, F.Id("Y"), Comma, Sp,
                                    D(0), Le, Sp,
                                    F.Id("W"), Open, F.Id("x"), Comma, Sp, F.Id("y"), Close,
                                    Close, Sp, Land, Sp,
                                    Open, Forall, Sp, F.Id("x"), Colon, Sp, F.Id("X"), Comma, Sp,
                                    Sum, Underscore, Grp(F.Id("y")),
                                    F.Id("W"), Open, F.Id("x"), Comma, Sp, F.Id("y"), Close,
                                    Eq, D(1), Close,
                                    Close, Sp, Rightarrow, RowBreak,
                                    F.Id("D"), Open, F.Id("p"), Vert, Vert, Sp, F.Id("q"), Close,
                                    Minus,
                                    F.Id("D"), Open,
                                    F.Id("W"), F.Id("p"), Vert, Vert, Sp, F.Id("W"), F.Id("q"), Close,
                                    Ge, Sp, D(0), Dot,
                                    End, Grp(F.Id("gathered"))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                                    Paragraph(Text(
                                        "Let X and Y be finite types, let p and q be nonnegative normalized " +
                                        "masses with discrete absolute continuity, and let the channel W be " +
                                        "nonnegative with unit row sums. The displayed D and channel output are " +
                                        "the definitions imported from the frozen ClassicalDPI module, total at " +
                                        "zero under the stated conventions. The difference on the left is the " +
                                        "forgetting quantity: the divergence lost by passing both masses " +
                                        "through the channel.")),
                                    Paragraph(Text(
                                        "The proof composes two frozen results. The general-support chain " +
                                        "identity classical_dpi_identity_zero_support rewrites the difference " +
                                        "as the output-weighted sum of posterior divergences, and the finite " +
                                        "Gibbs inequality kl_divergence_nonneg makes each summand nonnegative " +
                                        "once absolute continuity is transported to the posteriors. No strict " +
                                        "positivity is assumed anywhere; zero-mass branches contribute zero by " +
                                        "convention and the inequality survives at the boundary."))),
                DescribeRole.Theorem
            ))));
}
