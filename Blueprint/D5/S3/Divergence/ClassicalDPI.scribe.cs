using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Divergence;

internal sealed class ClassicalDpiDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        Header(
            "D5/S3/Divergence/ClassicalDPI",
            "The finite classical data-processing identity from two decompositions of joint relative entropy."),
        H("Classical Data Processing as a Chain Identity"),
        Blocks(
            DocumentBlock.Describe.Theorem(
                DescribeId.Create("joint-relative-entropy-has-two-chain-decompositions"),
                H("Joint relative entropy has two chain decompositions"),
                LeanTheorem("D5/S3/Divergence/ClassicalDPI.classical_dpi_identity"),
                Disp(Seq(
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
                    Operatorname, Grp(F.Id("Nonempty")), Open, F.Id("X"), Close,
                    CloseBracket, Sp,
                    OpenBracket,
                    Operatorname, Grp(F.Id("Fintype")), Open, F.Id("Y"), Close,
                    CloseBracket, Comma, RowBreak,
                    Forall, Sp,
                    F.Id("p"), Comma, Sp, F.Id("q"), Colon, Sp,
                    F.Id("X"), To, Mathbb, Grp(F.Id("R")), Comma, Sp,
                    F.Id("W"), Colon, Sp,
                    F.Id("X"), To, Sp, F.Id("Y"), To, Mathbb, Grp(F.Id("R")),
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
                    F.Id("D"), Open, F.Id("p"), Vert, Vert, Sp, F.Id("q"), Close,
                    Eq,
                    F.Id("D"), Open,
                    F.Id("W"), F.Id("p"), Vert, Vert, Sp, F.Id("W"), F.Id("q"), Close,
                    Plus,
                    Sum, Underscore, Grp(F.Id("y")),
                    Open, F.Id("W"), F.Id("p"), Close, Open, F.Id("y"), Close,
                    F.Id("D"), Open,
                    Widehat, Grp(F.Id("p")), Underscore, Grp(F.Id("y")),
                    Vert, Vert,
                    Widehat, Grp(F.Id("q")), Underscore, Grp(F.Id("y")),
                    Close, Dot,
                    End, Grp(F.Id("gathered")))),
                DescribeProvenance.RepoDerived(),
                Blocks(
                    Paragraph(Text(
                        "Let X and Y be finite types, with X nonempty. Let p and q be strictly " +
                        "positive normalized real mass functions on X, and let W be a strictly " +
                        "positive row-stochastic channel from X to Y. The displayed definitions " +
                        "agree pointwise with the Lean definitions klDivergence, channelOutput, " +
                        "and posterior. Under these hypotheses every output mass and every " +
                        "posterior denominator is positive, so all logarithms are evaluated on " +
                        "positive ratios.")),
                    Paragraph(Text(
                        "For the joint mass functions P(x,y) = p(x)W(x,y) and " +
                        "Q(x,y) = q(x)W(x,y), decomposition by the input coordinate cancels the " +
                        "common channel factor and gives D(P||Q) = D(p||q). Decomposition by the " +
                        "output coordinate uses P(x,y) = (Wp)(y) p-hat_y(x) and the analogous " +
                        "factorization of Q, giving D(P||Q) = D(Wp||Wq) plus the Wp-weighted sum " +
                        "of posterior divergences. Equating the two checked finite sums proves " +
                        "the identity. The declaration formalizes the full-support case only; it " +
                        "does not claim the zero-support extension obtained by absolute " +
                        "continuity and the convention 0 log 0 = 0.")))))));
}
