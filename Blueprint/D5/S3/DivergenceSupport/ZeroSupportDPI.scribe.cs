using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.DivergenceSupport;

internal sealed class ZeroSupportDpiDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The finite classical data-processing identity under discrete absolute continuity and general support.",
        H("Classical Data Processing on General Support"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("classical-dpi-identity-zero-support-extension"),
                DeclarationHandle.Create("D5/S3/DivergenceSupport/ZeroSupportDPI.classical_dpi_identity_zero_support"),
                H("The classical DPI chain identity extends to zero support"),
                StatementSource.FromAuthor(Disp(Seq(
                                    Begin, Grp(F.Id("gathered")),
                                    F.Id("D"), Open, F.Id("a"), Vert, Vert, Sp, F.Id("b"), Close,
                                    Colon, Eq,
                                    Sum, Underscore, Grp(F.Id("i")),
                                    F.Id("a"), Open, F.Id("i"), Close, Sp,
                                    Log, Open,
                                    Frac,
                                    Grp(F.Id("a"), Open, F.Id("i"), Close),
                                    Grp(F.Id("b"), Open, F.Id("i"), Close),
                                    Close, Comma, RowBreak,
                                    Open, F.Id("W"), F.Id("r"), Close, Open, F.Id("y"), Close,
                                    Colon, Eq,
                                    Sum, Underscore, Grp(F.Id("x")),
                                    F.Id("r"), Open, F.Id("x"), Close,
                                    F.Id("W"), Open, F.Id("x"), Comma, Sp, F.Id("y"), Close,
                                    Comma, RowBreak,
                                    Widehat, Grp(F.Id("r")), Underscore, Grp(F.Id("y")),
                                    Open, F.Id("x"), Close, Colon, Eq,
                                    Frac,
                                    Grp(
                                        F.Id("r"), Open, F.Id("x"), Close,
                                        F.Id("W"), Open, F.Id("x"), Comma, Sp, F.Id("y"), Close),
                                    Grp(Open, F.Id("W"), F.Id("r"), Close, Open, F.Id("y"), Close),
                                    Semi, RowBreak,
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
                                    Eq,
                                    F.Id("D"), Open,
                                    F.Id("W"), F.Id("p"), Vert, Vert, Sp, F.Id("W"), F.Id("q"), Close,
                                    Plus,
                                    Sum, Underscore, Grp(F.Id("y")),
                                    Open, F.Id("W"), F.Id("p"), Close, Open, F.Id("y"), Close,
                                    F.Id("D"), Open,
                                    Widehat, Grp(F.Id("p")), Underscore, Grp(F.Id("y")),
                                    Vert, Vert, Sp,
                                    Widehat, Grp(F.Id("q")), Underscore, Grp(F.Id("y")),
                                    Close, Dot,
                                    End, Grp(F.Id("gathered"))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                                    Paragraph(Text(
                                        "Let X and Y be finite types. The functions p and q are nonnegative " +
                                        "normalized masses with discrete absolute continuity: q(x) = 0 implies " +
                                        "p(x) = 0. The channel W is nonnegative and each row sums to one. The " +
                                        "displayed D, channel output, and posterior are exactly the definitions " +
                                        "imported from the frozen ClassicalDPI module.")),
                                    Paragraph(Text(
                                        "Those definitions are total at zero. Real.log 0 is zero, real division " +
                                        "by zero is zero, and a zero output mass multiplies its posterior " +
                                        "divergence contribution by zero. The declaration " +
                                        "zero_output_weighted_posterior_kl records that convention in a separate theorem. " +
                                        "Nonnegativity and finite-sum zero detection also show that p-output " +
                                        "mass vanishes whenever q-output mass vanishes, so absolute continuity " +
                                        "is preserved by the channel.")),
                                    Paragraph(Text(
                                        "The proof writes out the common joint masses p(x)W(x,y) and q(x)W(x,y). " +
                                        "Terms with p(x) = 0, W(x,y) = 0, or zero p-output mass are discharged " +
                                        "before logarithms are split. On the remaining positive support, " +
                                        "absolute continuity makes every denominator positive and Real.log_mul " +
                                        "gives the input and output chain decompositions. Equating the two " +
                                        "finite sums proves the identity. This is a direct general-support " +
                                        "proof, not a specialization of the strict-positivity theorem " +
                                        "classical_dpi_identity."))),
                DescribeRole.Theorem
            ))));
}
