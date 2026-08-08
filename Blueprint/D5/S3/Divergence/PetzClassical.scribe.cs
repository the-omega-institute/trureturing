using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Divergence;

internal sealed class PetzClassicalDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        Header(
            "D5/S3/Divergence/PetzClassical",
            "Zero classical data-processing defect is equivalent to supportwise equality of posteriors."),
        H("The Classical Petz Equality Condition"),
        Blocks(
            DocumentBlock.Describe.Theorem(
                DescribeId.Create("zero-dpi-defect-is-supportwise-posterior-equality"),
                H("Zero DPI defect is supportwise posterior equality"),
                LeanTheorem(
                    "D5/S3/Divergence/PetzClassical.dpi_defect_zero_iff_posteriors_eq"),
                Disp(Seq(
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
                    Open, Forall, Sp, F.Id("x"), Colon, Sp, F.Id("X"), Comma,
                    Sp, D(0), Lt, F.Id("p"), Open, F.Id("x"), Close, Close,
                    Sp, Land, Sp,
                    Sum, Underscore, Grp(F.Id("x")),
                    F.Id("p"), Open, F.Id("x"), Close, Eq, D(1),
                    Close, Sp, Rightarrow, RowBreak,
                    Open,
                    Open, Forall, Sp, F.Id("x"), Colon, Sp, F.Id("X"), Comma,
                    Sp, D(0), Lt, F.Id("q"), Open, F.Id("x"), Close, Close,
                    Sp, Land, Sp,
                    Sum, Underscore, Grp(F.Id("x")),
                    F.Id("q"), Open, F.Id("x"), Close, Eq, D(1),
                    Close, Sp, Rightarrow, RowBreak,
                    Open,
                    Open, Forall, Sp,
                    F.Id("x"), Colon, Sp, F.Id("X"), Comma, Sp,
                    F.Id("y"), Colon, Sp, F.Id("Y"), Comma, Sp,
                    D(0), Lt, F.Id("W"), Open, F.Id("x"), Comma, Sp, F.Id("y"), Close,
                    Close, Sp, Land, Sp,
                    Open, Forall, Sp, F.Id("x"), Colon, Sp, F.Id("X"), Comma, Sp,
                    Sum, Underscore, Grp(F.Id("y")),
                    F.Id("W"), Open, F.Id("x"), Comma, Sp, F.Id("y"), Close,
                    Eq, D(1), Close,
                    Close, Sp, Rightarrow, RowBreak,
                    F.Id("D"), Open,
                    F.Id("p"), Vert, Vert, Sp, F.Id("q"), Close,
                    Minus,
                    F.Id("D"), Open,
                    F.Id("W"), F.Id("p"), Vert, Vert, Sp,
                    F.Id("W"), F.Id("q"), Close,
                    Eq, D(0), Sp, Leftrightarrow, RowBreak,
                    Forall, Sp, F.Id("y"), Colon, Sp, F.Id("Y"), Comma, Sp,
                    D(0), Lt,
                    Open, F.Id("W"), F.Id("p"), Close, Open, F.Id("y"), Close,
                    Sp, Rightarrow, Sp,
                    Widehat, Grp(F.Id("p")), Underscore, Grp(F.Id("y")),
                    Eq,
                    Widehat, Grp(F.Id("q")), Underscore, Grp(F.Id("y")), Dot,
                    End, Grp(F.Id("gathered")))),
                DescribeProvenance.RepoDerived(),
                Blocks(
                    Paragraph(Text(
                        "Let X and Y be finite types, with X nonempty. Let p and q be strictly " +
                        "positive normalized real mass functions on X, and let W be a strictly " +
                        "positive row-stochastic channel from X to Y. The symbols D, Wp, and " +
                        "p-hat_y are exactly the divergence, channel output, and posterior defined " +
                        "in ClassicalDPI. The conclusion is stated on the support of Wp, even " +
                        "though the present full-support hypotheses make every output mass positive.")),
                    Paragraph(Text(
                        "The classical data-processing identity rewrites the defect as the finite " +
                        "sum over y of (Wp)(y) times D(p-hat_y||q-hat_y). The Grandmother Theorem " +
                        "makes every posterior divergence nonnegative, so every weighted summand " +
                        "is nonnegative. If the defect is zero, the finite nonnegative-sum criterion " +
                        "makes each weighted summand zero. On the support of Wp, the positive weight " +
                        "can be cancelled, and Gibbs equality gives p-hat_y = q-hat_y. Conversely, " +
                        "supportwise posterior equality makes every summand vanish and hence makes " +
                        "the defect zero.")),
                    Paragraph(Text(
                        "This declaration proves only the core equality characterization. Bayesian " +
                        "reverse recovery and the permutation-channel specialization are not part of " +
                        "this declaration; they require separate statements and proofs.")))))));
}
