using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic;

internal sealed class RemoteVectorCompensationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciAtomic/RemoteVectorCompensation.";
    private static Formula V(string s) => F.Id(s);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(name))), [.. args]);
    private static Formula Par(Formula f) => Seq(Open, f, Close);
    private static Formula And(params Formula[] formulas)
    {
        var parts = new List<Formula>();
        foreach (var formula in formulas)
        {
            if (parts.Count > 0) parts.Add(Seq(Sp, Land, Sp));
            parts.Add(Par(formula));
        }
        return Seq(parts.ToArray());
    }

    private static DocumentBlock Definition(string name, string title, string prose) =>
        Describe.Lean(DescribeId.Create("remote-vector-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every legal finite prefix and complete modular Fibonacci composition have a common finite realization with a nonzero remote tail.",
        H("Remote Vector Compensation"),
        Blocks(
            Paragraph(Text("L and B are arbitrary natural numbers, including zero. The word p is any "
                + "legal low-to-high binary word of length L: no two adjacent letters are one. "
                + "The modulus m is any positive natural number, including one, and r is any pair in "
                + "ZMod(m) squared. LegalDigits is the space of infinite binary addresses without adjacent "
                + "ones; finiteTail means that all sufficiently high bits are zero. P(L,b) is the "
                + "existing low-prefix projection. The external unit position has digit zero and is "
                + "not part of the address.")),
            Definition("sourceComposition", "Actual source composition",
                "x(b) is the finite-support sum of atomicBlock(j)=M^j alpha over occupied "
                + "positions j of b, where M(a,c)=(c,a+c) and alpha=(1,0). The coordinates are "
                + "nonnegative integers, included in the integer lattice. For an eventually zero "
                + "address this sum is finite. Its totalized value on an address that is not "
                + "eventually zero is not interpreted as a source composition; the realization "
                + "theorem requires finiteTail(b). rho(m,x) reduces both coordinates modulo m."),
            Describe.Lean(DescribeId.Create("remote-vector-compensation-result"),
                DeclarationHandle.Create(Prefix + "result"), H("Joint realization beyond any bound"),
                StatementSource.FromAuthor(Seq(
                    Forall, Sp, V("L"), Comma, Sp, V("p"), Sp, InMacro, Sp, Call("X", V("L")),
                    Comma, Sp, V("m"), Sp, Gt, Sp, Num(0), Comma, Sp, V("r"), Sp, InMacro, Sp,
                    Seq(Call("ZMod", V("m")), Caret, Grp(Num(2))), Comma, Sp, V("B"), Comma, Sp,
                    Exists, Sp, V("b"), Sp, InMacro, Sp, V("LegalDigits"), Comma, Sp,
                    And(Call("finiteTail", V("b")),
                        Seq(Call("P", V("L"), V("b")), Sp, Eq, Sp, V("p")),
                        Seq(Call("rho", V("m"), Call("x", V("b"))), Sp, Eq, Sp, V("r")),
                        Seq(Forall, Sp, V("j"), Comma, Sp,
                            Par(And(Seq(V("L"), Sp, Leq, Sp, V("j")),
                                Seq(Call("bit", V("b"), V("j")), Sp, Eq, Sp, Num(1)))),
                            Sp, Implies, Sp, V("B"), Sp, Lt, Sp, V("j")),
                        Seq(Exists, Sp, V("j"), Comma, Sp,
                            And(Seq(V("L"), Sp, Leq, Sp, V("j")),
                                Seq(V("B"), Sp, Lt, Sp, V("j")),
                                Seq(Call("bit", V("b"), V("j")), Sp, Eq, Sp, Num(1))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Choose a return period T at least three for the Fibonacci "
                    + "step modulo m and a sufficiently distant multiple N of T. Subtract the "
                    + "prefix composition from the target vector. If its two least nonnegative "
                    + "coordinates are a and c, place a+m ones at N+iT and then c ones at "
                    + "N+(a+m+j)T+1. The two groups contribute (a,0) and (0,c) modulo m; "
                    + "the additional m positions have zero modular contribution. Consecutive "
                    + "occupied positions within a group are T apart, and the transition between "
                    + "groups is T+1 apart. The gap after the prefix is at least two. Thus one "
                    + "eventually zero legal address realizes the entire vector, retains the "
                    + "prefix, and has at least one occupied position beyond B."))), DescribeRole.Theorem))));
}
