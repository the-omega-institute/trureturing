using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic;

internal sealed class ImmediateWindowStateCapacityDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Arith/FibonacciAtomic/ImmediateWindowStateCapacity.window_observe_kernel";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The consecutive three-bit window readouts have an exact determinant-two kernel.",
        H("Immediate Fibonacci Window Readout Kernel"),
        Blocks(Describe.Lean(
            DescribeId.Create("immediate-window-readout-kernel"),
            DeclarationHandle.Create(Declaration),
            H("The kernel is exactly the two-torsion in the first coordinate"),
            StatementSource.FromAuthor(KernelFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "For a modulus m, the two readouts are q x and q S x, with "
                    + "q=(2,3) and S=[[1,2],[2,3]].")),
                Paragraph(Text(
                    "Subtracting four times the first readout from the second leaves "
                    + "the second composition coordinate. The first readout then leaves "
                    + "twice the first coordinate, so the kernel is precisely the stated "
                    + "two-torsion family."))),
            DescribeRole.Theorem))));

    private static Formula V(string name) => F.Id(name);

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(V(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula Pair(Formula a, Formula b) =>
        Seq(Open, a, Comma, Sp, b, Close);

    private static Formula Par(Formula body) => Seq(Open, body, Close);

    private static Formula KernelFormula() => Disp(Seq(
        Forall, Sp, V("m"), Sp, InMacro, Sp, Call("N"), Comma, Sp,
        Forall, Sp, V("x"), Sp, InMacro, Sp,
        Call("ZMod", V("m")), Times, Call("ZMod", V("m")), Comma, Sp,
        RowBreak,
        Par(Seq(Call("windowObserve", V("x")), Sp, Eq, Sp, D(0))),
        Sp, Leftrightarrow, Sp,
        Exists, Sp, V("a"), Sp, InMacro, Sp, Call("ZMod", V("m")), Comma, Sp,
        Par(Seq(V("x"), Sp, Eq, Sp, Pair(V("a"), D(0)))),
        Sp, Land, Sp,
        Par(Seq(D(2), V("a"), Sp, Eq, Sp, D(0))), Dot));
}
