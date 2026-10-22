using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic.Observer.FutureResponses;

internal sealed class NativeJointFutureMemoryLowerBoundDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact native future-response classes impose an eleven-state finite-memory lower bound.",
        H("Native Joint Future Memory Lower Bound"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("native-joint-future-memory-lower-bound"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/FibonacciAtomic/Observer/FutureResponses/"
                        + "NativeJointFutureMemoryLowerBound.native_joint_future_memory_lower_bound"),
                H("A finite memory preserving all native future replies has at least eleven states"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let W be a finite memory carrier. A surjective memory map assigns every "
                            + "native source to a memory state, and memoryReadout must reproduce the "
                            + "two future replies for every supplied count from that state.")),
                    Paragraph(Text(
                        "If two sources share one memory state, their reproduced future reply "
                            + "trajectories agree. The native eleven-class classification therefore "
                            + "assigns the same joint class to every source in that memory fibre.")),
                    Paragraph(Text(
                        "Choosing one source from each memory fibre gives a surjection from W onto "
                            + "the eleven attained joint classes. Finite cardinality then forces "
                            + "eleven to be at most the number of memory states. The result counts "
                            + "future-behaviour states only; an executable controller may require "
                            + "additional phase or action-selection states."))),
                DescribeRole.Theorem))));

    private static Formula V(string name) => F.Id(name);

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Sp, Grp(V(name)), Open };
        for (var i = 0; i < arguments.Length; i++)
        {
            if (i > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[i]);
        }

        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, V(name), Colon, Sp, type, Comma, Sp, Grp(body));

    private static Formula FunctionType(params Formula[] types)
    {
        var items = new List<Formula>();
        for (var i = 0; i < types.Length; i++)
        {
            if (i > 0) items.AddRange([Sp, To, Sp]);
            items.Add(types[i]);
        }

        return Seq([.. items]);
    }

    private static Formula Equal(Formula left, Formula right) =>
        Seq(left, Sp, Eq, Sp, right);

    private static Formula Card(Formula type) => Call("card", type);

    private static Formula TheoremFormula()
    {
        Formula source = V("Source");
        Formula reply = V("Reply");
        Formula nat = Seq(Mathbb, Sp, Grp(V("N")));
        Formula memory = V("memory");
        Formula memoryReadout = V("memoryReadout");
        Formula u = V("u");
        Formula k = V("k");
        Formula W = V("W");
        Formula future = All("u", source, All("k", nat,
            Equal(
                Call("futureReplies", u, k),
                Call("memoryReadout", Call("memory", u), k))));
        Formula assumptions = Seq(
            Call("Surjective", memory), Sp, Land, Sp, future);

        return Disp(Seq(
            Forall, Sp, W, Colon, Sp, V("Type"), Comma, Sp,
            OpenBracket, Call("Fintype", W), CloseBracket, Sp,
            All("memory", FunctionType(source, W),
                All("memoryReadout", FunctionType(W, nat, Call("Prod", reply, reply)),
                    Seq(Grp(assumptions), Sp, Rightarrow, Sp,
                        D(1, 1), Sp, Leq, Sp, Card(W)))),
            Dot));
    }
}
