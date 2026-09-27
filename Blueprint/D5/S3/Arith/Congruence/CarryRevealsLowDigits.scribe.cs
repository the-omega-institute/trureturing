using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Congruence;

internal sealed class CarryRevealsLowDigitsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Congruence/CarryRevealsLowDigits.";

    private static readonly Formula X = F.Id("x"), Y = F.Id("y"), N = F.Id("n"), Nn = F.Id("N"), K = F.Id("k");
    private static readonly Formula Pw = Seq(F.Id("p"), Caret, Grp(K));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Reading the digit of order k of a p-adic integer along the translations x, x + 1, ..., x + p^k - 1 "
            + "recovers its residue modulo p^{k+1}: the first carry into that digit reveals the lower digits, and "
            + "no shorter run of readings suffices.",
        H("A Carry Reveals the Missing Low Digits"),
        Blocks(
            Node("digit", "The digit sensor",
                Disp(Seq(Sub("d", K), Open, X, Close, Sp, Eq, Sp, Lfloor, Frac,
                    Grp(Seq(Open, Sub("q", Seq(K, Plus, D(1))), Open, X, Close, Close)), Grp(Pw), Rfloor)),
                "Here q_{k+1} is the reduction of a p-adic integer modulo p^{k+1}, read as a natural number below "
                    + "p^{k+1}; the sensor d_k returns its digit of order k.",
                "highDigit", DescribeRole.Definition),
            Node("protocol", "The fixed continuous protocol",
                Disp(Seq(Sub("W", Seq(K, Comma, Nn)), Open, X, Close, Sp, Eq, Sp,
                    Open, Sub("d", K), Open, X, Plus, N, Close, Close, Underscore, Grp(N, Sp, Leq, Sp, Nn))),
                "The protocol reads the sensor after 0, 1, ..., N unit translations.",
                "digitProtocol", DescribeRole.Definition),
            Node("carry", "Carry revelation and the sharp horizon", TheoremFormula(),
                "Write q_{k+1}(x) = b p^k + r with b < p and r < p^k. Then q_{k+1}(x + n) is the residue of "
                    + "b p^k + r + n modulo p^{k+1}, and its digit of order k is the digit of the quotient of "
                    + "b p^k + r + n by p^k, that is (b + floor((r + n)/p^k)) mod p. For n <= p^k - 1 the sum r + n "
                    + "is below 2 p^k, so at most one carry reaches the digit: none when r = 0, and exactly at "
                    + "n = p^k - r when r > 0, where the digit changes because p >= 2, including the wrap from "
                    + "p - 1 to 0. Two points with the same readings therefore share b and the first change time, "
                    + "hence r, so they have the same residue; the converse holds because every reading factors "
                    + "through q_{k+1}. For k >= 1 and n <= p^k - 2 the points 0 and 1 both read digit 0, while "
                    + "their residues differ.",
                "carry_reveals_low_digits", DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula r = F.Id("r"), b = F.Id("b");
        Formula split = Seq(Sub("q", Seq(K, Plus, D(1))), Open, X, Close, Sp, Eq, Sp, b, Sp, Pw, Plus, r, Comma, Sp,
            b, Sp, Lt, Sp, F.Id("p"), Comma, Sp, r, Sp, Lt, Sp, Pw);
        Formula carry = Seq(Sub("d", K), Open, X, Plus, N, Close, Sp, Eq, Sp, Open, b, Plus, Lfloor, Frac,
            Grp(Seq(r, Plus, N)), Grp(Pw), Rfloor, Close, Sp, Operatorname, Grp(F.Id("mod")), Sp, F.Id("p"),
            Sp, F.Text, Grp(Sp, F.Id("for"), Sp), N, Sp, Leq, Sp, Pw, Minus, D(1));
        Formula firstChange = Seq(F.Text, Grp(F.Id("first"), Sp, F.Id("change"), Sp, F.Id("at"), Sp), N, Sp, Eq,
            Sp, Pw, Minus, r, Sp, F.Text, Grp(Sp, F.Id("if"), Sp), r, Sp, Gt, Sp, D(0), Comma, Sp,
            F.Text, Grp(F.Id("no"), Sp, F.Id("change"), Sp, F.Id("if"), Sp), r, Sp, Eq, Sp, D(0));
        Formula kernel = Seq(Sub("W", Seq(K, Comma, Pw, Minus, D(1))), Open, X, Close, Sp, Eq, Sp,
            Sub("W", Seq(K, Comma, Pw, Minus, D(1))), Open, Y, Close, Sp, Iff, Sp,
            Sub("q", Seq(K, Plus, D(1))), Open, X, Close, Sp, Eq, Sp, Sub("q", Seq(K, Plus, D(1))), Open, Y, Close);
        Formula sharp = Seq(K, Sp, Geq, Sp, D(1), Comma, Sp, Nn, Sp, Lt, Sp, Pw, Minus, D(1), Sp, Rightarrow, Sp,
            Sub("W", Seq(K, Comma, Nn)), Open, D(0), Close, Sp, Eq, Sp, Sub("W", Seq(K, Comma, Nn)), Open, D(1),
            Close, Sp, Land, Sp, Sub("q", Seq(K, Plus, D(1))), Open, D(0), Close, Sp, Neq, Sp,
            Sub("q", Seq(K, Plus, D(1))), Open, D(1), Close);
        return Disp(Seq(
            split, Sp, Rightarrow, RowBreak, Grp(),
            carry, Comma, RowBreak, Grp(),
            firstChange, Comma, RowBreak, Grp(),
            kernel, Comma, RowBreak, Grp(),
            sharp, Dot));
    }

    private static Formula Sub(string name, Formula index) => Seq(F.Id(name), Underscore, Grp(index));

    private static DocumentBlock Node(
        string id, string title, Formula formula, string prose, string declaration, DescribeRole role) =>
        Describe.Lean(
            DescribeId.Create("carry-digits-" + id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(formula), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
