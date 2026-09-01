using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Witt;

internal sealed class PrimitiveEulerLedgerDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S1/Recurrence/Witt/PrimitiveEulerLedger.unique_primitive_euler_ledger";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A constant-one integer power series has a unique locally finite primitive Euler ledger.",
        H("Unique Primitive Euler Ledger"),
        Blocks(Describe.Lean(
            DescribeId.Create("unique-primitive-euler-ledger"),
            DeclarationHandle.Create(Declaration),
            H("Every constant-one integer power series has one Euler ledger"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "For a formal power series f over the integers with constant coefficient "
                        + "one, there is a unique integer-valued ledger c on the positive "
                        + "degrees. At every finite cutoff N, its first N Euler factors reproduce "
                        + "every coefficient through degree N.")),
                Paragraph(Text(
                    "The factor at degree n + 1 is defined coefficientwise by generalized "
                        + "binomial coefficients, so it is the formal series "
                        + "(1 - X^(n + 1))^(-c_n). Its coefficients below degree n + 1 vanish, "
                        + "while the coefficient at degree n + 1 is c_n. This makes the next "
                        + "ledger entry the exact residual coefficient.")),
                Paragraph(Text(
                    "The source notation Gamma_phi, L, and its infinite product were not "
                        + "defined in the atom. The formal statement therefore specializes to "
                        + "ordinary integer formal power series, indexes factors by positive "
                        + "natural degrees, and expresses local finiteness as equality on every "
                        + "finite coefficient truncation. This supplies the missing semantics "
                        + "without weakening the existence-and-uniqueness claim.")),
                Paragraph(Text(
                    "The proof uses Mathlib's power-series coefficient convolution, finite "
                        + "antidiagonal sums, finite products, and generalized integer binomial "
                        + "coefficients. Strong induction at the first differing degree proves "
                        + "uniqueness."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula f = F.Id("f");
        Formula c = F.Id("c");
        Formula n = F.Id("n");
        Formula cutoff = F.Id("N");
        Formula degree = F.Id("k");
        Formula x = F.Id("X");
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));
        Formula integers = Seq(Mathbb, Grp(F.Id("Z")));
        Formula powerSeries = Seq(
            Operatorname, Grp(F.Id("PowerSeries")), Open, integers, Close);
        Formula product = Seq(
            Prod, Underscore, Grp(D(0), Leq, n, Lt, cutoff), Sp,
            Open, D(1), Minus, x, Caret, Grp(n, Plus, D(1)), Close,
            Caret, Grp(Open, Minus, c, Underscore, n, Close));

        return Disp(Seq(
            Forall, Sp, f, InMacro, powerSeries, Comma, Esc,
            Coeff(D(0), f), Eq, D(1), Sp, Rightarrow, Sp,
            Exists, Bang, Sp, c, Colon, Sp, naturals, Sp, To, Sp, integers,
            Comma, RowBreak,
            Forall, Sp, cutoff, Comma, Sp, degree, InMacro, naturals, Comma, Esc,
            degree, Leq, cutoff, Sp, Rightarrow, Sp,
            Coeff(degree, product), Eq, Coeff(degree, f), Dot));
    }

    private static Formula Coeff(Formula degree, Formula series) =>
        Seq(Operatorname, Grp(F.Id("coeff")), Open, degree, Comma, Sp, series, Close);
}
