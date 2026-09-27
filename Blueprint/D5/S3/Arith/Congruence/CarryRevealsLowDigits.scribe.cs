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
                "Here q_{k+1}(x) is read as a natural number below p^{k+1}, so q_{k+1}(x) = b p^k + r with b < p "
                    + "and r < p^k. Then q_{k+1}(x + n) is the residue of "
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
        Formula r = F.Id("r"), b = F.Id("b"), p = F.Id("p");
        Formula q = Sub("q", Seq(K, Plus, D(1)));
        Formula qx = Seq(q, Open, X, Close);
        Formula d = Sub("d", K);
        Formula dxn = Seq(d, Open, X, Plus, N, Close);
        Formula dx = Seq(d, Open, X, Close);
        Formula setting = Seq(p, Sp, F.Text, Grp(Sp, F.Id("prime"), Sp), Comma, Sp, K, Sp, InMacro, Sp,
            Mathbb, Grp(F.Id("N")), Comma, Sp, X, Comma, Sp, Y, Sp, InMacro, Sp, Mathbb, Grp(F.Id("Z")), Underscore,
            Grp(p), Comma, Sp, b, Sp, Eq, Sp, Lfloor, Frac, Grp(qx), Grp(Pw), Rfloor, Comma, Sp,
            r, Sp, Eq, Sp, qx, Sp, Operatorname, Grp(F.Id("mod")), Sp, Pw, Sp, Rightarrow);
        Formula carry = Seq(Forall, Sp, N, Sp, Leq, Sp, Pw, Minus, D(1), Comma, Sp, dxn, Sp, Eq, Sp,
            Open, b, Plus, Lfloor, Frac, Grp(Seq(r, Plus, N)), Grp(Pw), Rfloor, Close, Sp,
            Operatorname, Grp(F.Id("mod")), Sp, p);
        Formula noChange = Seq(Open, r, Sp, Eq, Sp, D(0), Sp, Rightarrow, Sp, Forall, Sp, N, Comma, Sp,
            D(1), Sp, Leq, Sp, N, Sp, Leq, Sp, Pw, Minus, D(1), Sp, Rightarrow, Sp, dxn, Sp, Eq, Sp, dx, Close);
        Formula firstChange = Seq(Open, r, Sp, Gt, Sp, D(0), Sp, Rightarrow, Sp,
            d, Open, X, Plus, Open, Pw, Minus, r, Close, Close, Sp, Neq, Sp, dx, Sp, Land, Sp,
            Forall, Sp, N, Comma, Sp, D(1), Sp, Leq, Sp, N, Sp, Lt, Sp, Pw, Minus, r, Sp, Rightarrow, Sp,
            dxn, Sp, Eq, Sp, dx, Close);
        Formula kernel = Seq(Open, Sub("W", Seq(K, Comma, Pw, Minus, D(1))), Open, X, Close, Sp, Eq, Sp,
            Sub("W", Seq(K, Comma, Pw, Minus, D(1))), Open, Y, Close, Sp, Iff, Sp,
            qx, Sp, Eq, Sp, q, Open, Y, Close, Close);
        Formula sharp = Seq(Forall, Sp, Nn, Comma, Sp, K, Sp, Geq, Sp, D(1), Sp, Rightarrow, Sp, Nn, Sp, Lt, Sp,
            Pw, Minus, D(1), Sp, Rightarrow, Sp,
            Sub("W", Seq(K, Comma, Nn)), Open, D(0), Close, Sp, Eq, Sp, Sub("W", Seq(K, Comma, Nn)), Open, D(1),
            Close, Sp, Land, Sp, q, Open, D(0), Close, Sp, Neq, Sp, q, Open, D(1), Close);
        return Disp(Seq(
            setting, RowBreak, Grp(),
            carry, Sp, Land, RowBreak, Grp(),
            noChange, Sp, Land, RowBreak, Grp(),
            firstChange, Sp, Land, RowBreak, Grp(),
            kernel, Sp, Land, RowBreak, Grp(),
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
