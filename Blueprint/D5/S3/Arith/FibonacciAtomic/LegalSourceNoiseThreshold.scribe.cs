using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic;

internal sealed class LegalSourceNoiseThresholdDocument : IScribeDocumentDefinition
{
    private static Formula V(string name) => F.Id(name);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(name))), [.. args]);
    private static Formula Pow(Formula x, Formula n) => Seq(x, Caret, Grp(n));
    private static Formula Add(Formula x, Formula y) => Seq(x, Sp, Plus, Sp, y);
    private static Formula Mul(Formula x, Formula y) => Seq(x, Sp, Times, Sp, y);
    private static Formula Fr(Formula x, Formula y) => new Formula.Fraction(x, y);
    private static Formula EqOf(Formula x, Formula y) => Seq(x, Sp, Eq, Sp, y);
    private static Formula Nat => Seq(Mathbb, Grp(V("N")));
    private static Formula Real => Seq(Mathbb, Grp(V("R")));
    private static Formula Rational => Seq(Mathbb, Grp(V("Q")));
    private static Formula S(Formula n) => Call("s", n);
    private static Formula C(Formula n) => Call("c", n);
    private static readonly string[] Contracts = ["Rstate", "RclockState", "Rend", "RclockEnd"];

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Legal five-window sources admit exact current-row recovery precisely below a sharp update-noise budget.",
        H("Sharp Update Noise Threshold for Legal Windows"),
        Blocks(
            Paragraph(Text("Fix a rational decay lambda with 0<lambda<1, embedded in the real numbers. "
                + "Words use the low-to-high windows 000,100,010,101,001. A word is legal when no "
                + "high bit of one window and low bit of the next are both one. The empty word "
                + "is legal. Terminal zero windows remain in the source. The symbolic run starts "
                + "with both flags false; End is queried after the entire word.")),
            Paragraph(Text("The canonical rows are zA=(0,1,1), zB=(1,1,1), zC=(1,0,1), and "
                + "zD=(0,0,0). The original matrices are the outer products e3*zA, e2*zB, e3*zB, "
                + "e2*zC, e3*zC for 000,100,010,101,001 respectively. Their row actions agree "
                + "with the symbolic transitions on every word, including failed seams. Legal "
                + "words reach A, B or C; End is false at A and true at B and C.")),
            Paragraph(Text("An actual trajectory starts at zA without initial noise. Each letter applies "
                + "lambda times its original row action and then adds an arbitrary real three-vector "
                + "whose sup norm is at most nu, where nu>=0. Noise is bounded separately at every "
                + "step. The accumulated geometric sum and critical budget are as follows.")),
            new DocumentBlock.DisplayFormula(Definitions()),
            Describe.Lean(DescribeId.Create("legal-source-sharp-noise-threshold"),
                DeclarationHandle.Create("D5/S3/Arith/FibonacciAtomic/LegalSourceNoiseThreshold.result"),
                H("One Current Row Decoder, All Allowed Trajectories"),
                StatementSource.FromAuthor(ResultFormula()), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Rstate and Rend mean existence of a total decoder from the current "
                        + "real row to the canonical state row or Boolean End label. RclockState and "
                        + "RclockEnd additionally give the decoder the current position. For each "
                        + "fixed lambda, nu and M, one decoder must work for every legal input and "
                        + "every permitted noise sequence. It receives no current letter, history, "
                        + "previous state or separate memory. The Boolean b selects all lengths "
                        + "n<=M when false, and only length n=M when true.")),
                    Paragraph(Text("For a nonempty legal trajectory of length n, every target zero "
                        + "coordinate has magnitude at most nu: the last matrix has cleared its "
                        + "earlier value. Every target one coordinate is at least lambda^n-nu*s(n). "
                        + "The induction reads a coordinate equal to one in the legal preceding "
                        + "canonical state. Below c(M), a single threshold strictly between nu and "
                        + "lambda^M-nu*s(M) separates all zero and one coordinates. This threshold "
                        + "lies between zero and one, so it also decodes the empty word.")),
                    Paragraph(Text("At c=c(M) with M>=1, use the legal words 100^M and 000^M. The "
                        + "first trajectory adds -c*zB at every step. The second adds -c*zA for "
                        + "its first M-1 steps, then (c,-c,-c). Their actual final rows are both "
                        + "c*zB, although their canonical targets are B and A and their End labels "
                        + "are true and false. Every disturbance obeys the budget c, so the same "
                        + "collision is permitted at any larger budget. The position also agrees, "
                        + "which excludes every decoder under either observation contract.")),
                    Paragraph(Text("At depth zero there is no update and a constant decoder works "
                        + "for every budget. At depth one the strict boundary is lambda/2. For "
                        + "M>=2 the legal-source budget exceeds lambda^M/(2*s(M)). The budgets "
                        + "tend to zero, so a fixed positive stepwise budget cannot support "
                        + "current-row recovery at every depth."))), DescribeRole.Theorem))));

    private static Formula Definitions()
    {
        var n = V("n"); var j = V("j");
        Formula sum = Seq(new Formula.Subscript(Sum, Seq(D(0), Sp, Le, Sp, j, Sp, Lt, Sp, n)),
            Pow(LambdaLower, j));
        return Disp(new Formula.Aligned([
            EqOf(S(n), sum),
            EqOf(C(n), Fr(Pow(LambdaLower, n), Add(S(n), D(1))))
        ]));
    }

    private static Formula ResultFormula()
    {
        var nu = V("nu"); var m = V("M"); var b = V("b"); var k = V("k");
        Formula R(string name, Formula depth) => Call(name, LambdaLower, nu, depth, b);
        Formula Condition(Formula depth) => Seq(Open, depth, Sp, Eq, Sp, D(0), Sp, Lor, Sp,
            nu, Sp, Lt, Sp, C(depth), Close);
        var lines = new List<Formula> {
            Seq(Forall, Sp, LambdaLower, Sp, InMacro, Sp, Rational, Comma, Sp,
                D(0), Sp, Lt, Sp, LambdaLower, Sp, Lt, Sp, D(1), Comma),
            Seq(Forall, Sp, nu, Sp, InMacro, Sp, Real, Comma, Sp, nu, Sp, Ge, Sp, D(0), Comma, Sp,
                Forall, Sp, m, Sp, InMacro, Sp, Nat, Comma, Sp, Forall, Sp, b, Sp, InMacro, Sp,
                Call("Bool"), Comma)
        };
        foreach (var name in Contracts)
            lines.Add(Seq(R(name, m), Sp, Leftrightarrow, Sp, Condition(m)));
        foreach (var name in Contracts)
            lines.Add(Seq(R(name, D(0)), Comma, Sp,
                Open, R(name, D(1)), Sp, Leftrightarrow, Sp,
                nu, Sp, Lt, Sp, Fr(LambdaLower, D(2)), Close));
        lines.Add(Seq(m, Sp, Ge, Sp, D(2), Sp, Rightarrow, Sp,
            Fr(Pow(LambdaLower, m), Mul(D(2), S(m))), Sp, Lt, Sp, C(m)));
        lines.Add(EqOf(Seq(new Formula.Subscript(Lim, Seq(k, Sp, Rightarrow, Sp, Infty)),
            Sp, C(k)), D(0)));
        return Disp(new Formula.Aligned([.. lines]));
    }
}
