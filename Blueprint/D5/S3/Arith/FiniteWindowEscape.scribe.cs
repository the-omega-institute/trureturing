using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith;

internal sealed class FiniteWindowEscapeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        Header(
            "D5/S3/Arith/FiniteWindowEscape",
            "Finite prime windows escape; finite readings retain a nonzero kernel difference."),
        H("Finite-Window Escape and Hidden Fibers"),
        Blocks(
            DocumentBlock.Describe.Theorem(
                DescribeId.Create(
                    "finite-prime-windows-escape-and-finite-readings-have-hidden-fibers"),
                H("Finite prime windows escape and finite readings retain hidden differences"),
                LeanTheorem(
                    "D5/S3/Arith/FiniteWindowEscape."
                    + "finite_window_escape_and_hidden_fiber"),
                Disp(Seq(
                    Forall, Sp, F.Id("S"), Subset, Underscore,
                    Grp(Mathrm, Grp(F.Id("fin"))), Mathbb, Grp(F.Id("N")), Comma, Esc,
                    Left, Open, Forall, Sp, F.Id("p"), InMacro, F.Id("S"), Comma, Esc,
                    Operatorname, Grp(F.Id("Prime")), Open, F.Id("p"), Close, Right, Close,
                    Sp, Rightarrow, Sp,
                    F.Id("P"), Underscore, Grp(F.Id("S")), Eq,
                    Prod, Underscore, Grp(F.Id("r"), InMacro, F.Id("S")), F.Id("r"), Comma, Esc,
                    F.Id("E"), Underscore, Grp(F.Id("S")), Eq,
                    F.Id("P"), Underscore, Grp(F.Id("S")), Plus, D(1), Comma, Esc,
                    Left, Open,
                    Left, Open, Forall, Sp, F.Id("p"), InMacro, F.Id("S"), Comma, Esc,
                    F.Id("E"), Underscore, Grp(F.Id("S")), Equiv, D(1),
                    OpenBracket, Operatorname, Grp(F.Id("mod")), F.Id("p"), CloseBracket,
                    Right, Close, Sp, Land, Sp,
                    Neg, Open, F.Id("E"), Underscore, Grp(F.Id("S")),
                    InMacro, F.Id("S"), Close, Sp, Land, Sp,
                    Left, Open, Exists, Sp, F.Id("q"), InMacro, Mathbb, Grp(F.Id("N")), Comma, Esc,
                    Operatorname, Grp(F.Id("Prime")), Open, F.Id("q"), Close, Sp, Land, Sp,
                    F.Id("q"), Mid, F.Id("E"), Underscore, Grp(F.Id("S")), Sp, Land, Sp,
                    Neg, Open, F.Id("q"), InMacro, F.Id("S"), Close, Right, Close, Sp, Land, Sp,
                    Left, Open, Forall, Sp, F.Id("q"), InMacro, Mathbb, Grp(F.Id("N")), Comma, Esc,
                    Operatorname, Grp(F.Id("Prime")), Open, F.Id("q"), Close, Sp, Land, Sp,
                    F.Id("q"), Mid, F.Id("E"), Underscore, Grp(F.Id("S")), Sp, Rightarrow, Sp,
                    Neg, Open, F.Id("q"), InMacro, F.Id("S"), Close, Right, Close, Sp, Land, Sp,
                    Forall, Sp, F.Id("G"), F.Text, Grp(Sp, F.Id("infinite"), Sp,
                    F.Id("additive"), Sp, F.Id("group")), Comma, Esc,
                    Forall, Sp, F.Id("A"), F.Text, Grp(Sp, F.Id("finite"), Sp,
                    F.Id("additive"), Sp, F.Id("group")), Comma, Esc,
                    Forall, Sp, F.Id("R"), Colon, F.Id("G"), To, F.Id("A"),
                    F.Text, Grp(Sp, F.Id("additive")), Comma, Esc,
                    Exists, Sp, F.Id("x"), Comma, F.Id("y"), InMacro, F.Id("G"), Comma, Esc,
                    F.Id("x"), Neq, F.Id("y"), Sp, Land, Sp,
                    F.Id("R"), Open, F.Id("x"), Close, Eq,
                    F.Id("R"), Open, F.Id("y"), Close, Sp, Land, Sp,
                    F.Id("x"), Minus, F.Id("y"), Neq, D(0), Sp, Land, Sp,
                    F.Id("R"), Open, F.Id("x"), Minus, F.Id("y"), Close, Eq, D(0),
                    Right, Close)),
                DescribeProvenance.RepoDerived(),
                Blocks(
                    Paragraph(Text(
                        "Fix a finite set S of natural primes, write P_S for its product, and set "
                        + "E_S = P_S + 1. The declaration proves that E_S is congruent to one "
                        + "modulo every member of S, that E_S itself is outside S, that E_S has a "
                        + "prime divisor outside S, and that every prime divisor of E_S is outside "
                        + "S. Thus every finite prime window leaves an external prime direction: "
                        + "the prime-axis tail persists and the window is not closed under the "
                        + "product-plus-one escape construction.")),
                    Paragraph(Text(
                        "For the finite-reading clause, G is any infinite additive group, A is "
                        + "any finite additive group, and R is any additive homomorphism from G to "
                        + "A. The witnesses x and y are distinct but have equal readings; their "
                        + "difference is explicitly nonzero and R maps it to zero. The formal "
                        + "statement therefore realizes the kernel branch of the hidden-difference "
                        + "alternative directly. It introduces no narrative ledger object and "
                        + "makes no claim about ledger custody.")),
                    Paragraph(Text(
                        "The proof combines the classical product-plus-one argument with the finite "
                        + "pigeonhole principle. Divisibility of P_S by every window prime gives the "
                        + "modular escape and excludes every prime divisor of E_S from S; existence "
                        + "of a prime divisor supplies the persistent tail. Finiteness of A and "
                        + "infinitude of G force a repeated reading, while additivity places the "
                        + "resulting nonzero difference in the kernel. The exact conjunction and its "
                        + "packaging as one declaration are repository-derived, and the result has "
                        + "no numerical certificate.")))
            ))));
}
