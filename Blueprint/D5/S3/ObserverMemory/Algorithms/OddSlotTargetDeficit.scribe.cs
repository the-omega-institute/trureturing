using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.Algorithms;

internal sealed class OddSlotTargetDeficitDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Directed slot incidence over an odd alphabet forces a deficit at every nonroot target.",
        H("Odd target rows and exact slot accounting"),
        Blocks(
            Paragraph(Text(
                "Let Q be a finite set of reading controls, p the alphabet size, and G a directed "
                + "graph on Q times Fin p. Its used slots contain every root digit. Each nonempty "
                + "successor set has one target control and at most two slots. Successors have "
                + "used sources and targets, no edge enters the root, and every used nonroot "
                + "slot has a predecessor. Cycles and multiple predecessors are allowed.")),
            Paragraph(Text(
                "At target q, missing counts unused digits, excess sums incoming cardinalities "
                + "minus one with natural subtraction, and singles counts one-successor source "
                + "slots whose unique target is q. These quantities refer to this one graph. "
                + "The number terminalCount counts used slots with no successor.")),
            Describe.Lean(DescribeId.Create("odd-slot-target-deficit"),
                DeclarationHandle.Create("D5/S3/ObserverMemory/Algorithms/OddSlotTargetDeficit.result"),
                H("Incidence identity, binary lower bound, and odd improvement"),
                StatementSource.FromAuthor(Disp(Statement())), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Double counting the actual edges gives the exact additive identity. "
                    + "When p is odd, a target row of zero deficit would be covered exactly once "
                    + "by pairwise disjoint two-slot successor sets. Its cardinality would be even. "
                    + "Thus each nonroot target contributes at least one. Summing uses unique "
                    + "target ownership, and the final product inequality is equivalent to "
                    + "card Q at least 1 plus 2p(P-1)/(p-1). This statement takes the directed "
                    + "incidence and terminal count as hypotheses; it does not construct them "
                    + "from a stationary controller."))), DescribeRole.Theorem))));

    private static Formula Statement()
    {
        var r = Call("card", V("Q"));
        var z = Sum("missing");
        var h = Sum("excess");
        var n = Sum("singles");
        var local = All("q", V("Q"), Imp(Ne(V("q"), Call("root", V("G"))),
            LE(D(1), Add(At("missing"), At("excess"), At("singles")))));
        var global = LE(Sub(r, D(1)), Add(z, h, n));
        var body = And(
            EqF(Add(Mul(V("p"), r), V("p")),
                Add(Mul(D(2), Mul(V("p"), V("P"))), h, n, z)),
            LE(Sub(Mul(D(2), V("P")), D(1)), r),
            Imp(Call("Odd", V("p")), And(local, global,
                LE(Mul(Mul(D(2), V("p")), Sub(V("P"), D(1))),
                    Mul(Sub(V("p"), D(1)), Sub(r, D(1)))))));
        return All("p", N, All("Q", V("Type"), Instances(
            All("G", Call("SlotGraph", V("p"), V("Q")),
            All("hp", LE(D(2), V("p")), All("P", N,
            All("hP", LE(D(1), V("P")), All("hterminal",
                EqF(Call("terminalCount", V("G")), Mul(V("p"), V("P"))), body))))))));
    }
    private static Formula V(string s) => F.Id(s);
    private static Formula N => Seq(Mathbb, Sp, Grp(V("N")));
    private static Formula SeqOp(Formula a, Formula op, Formula b) => Seq(Grp(a), op, Grp(b));
    private static Formula EqF(Formula a, Formula b) => SeqOp(a, Eq, b);
    private static Formula LE(Formula a, Formula b) => SeqOp(a, Le, b);
    private static Formula Ne(Formula a, Formula b) => Seq(Grp(a), Neq, Sp, Grp(b));
    private static Formula Mul(Formula a, Formula b) => Seq(Grp(a), Times, Sp, Grp(b));
    private static Formula Sub(Formula a, Formula b) => SeqOp(a, Minus, b);
    private static Formula Imp(Formula a, Formula b) => SeqOp(a, Implies, b);
    private static Formula All(string s, Formula type, Formula body) =>
        Seq(Forall, Sp, V(s), Colon, type, Comma, Grp(body));
    private static Formula Instances(Formula body) => Seq(
        OpenBracket, Call("Fintype", V("Q")), CloseBracket,
        OpenBracket, Call("DecidableEq", V("Q")), CloseBracket, Grp(body));
    private static Formula At(string s) => Call(s, V("G"), V("q"));
    private static Formula Sum(string s) => Seq(F.Sum, Underscore,
        Grp(Seq(V("q"), InMacro, Sp, V("Q"))), At(s));
    private static Formula Call(string s, params Formula[] args) =>
        Seq(Operatorname, Sp, Grp(V(s)), Open, Join(Comma, args), Close);
    private static Formula Join(Formula separator, Formula[] args) =>
        Seq([.. args.SelectMany((x, i) => i == 0 ? new[] { x } : new[] { separator, x })]);
    private static Formula Add(params Formula[] args) => Join(Plus, args);
    private static Formula And(params Formula[] args) => Join(Land, [.. args.Select(Grp)]);
}
