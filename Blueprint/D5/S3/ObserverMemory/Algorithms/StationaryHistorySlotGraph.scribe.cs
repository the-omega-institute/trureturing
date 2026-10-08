using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.Algorithms;

internal sealed class StationaryHistorySlotGraphDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original single-collision slot conditions extract actual marked parent and child histories.",
        H("StationaryHistorySlotGraph"),
        Blocks(
            Result("single_collision_rows", "single-collision-rows", "The actual unique single collision",
                Scope(Imp(And(EqF(At("J"), D(1)), EqF(At("s"), D(1))),
                    Some("q", V("Q"), Some("w", SlotType, Some("v", SlotType, And(
                        EqF(At("binaryMultiplicity", V("q")), D(2)),
                        EqF(Call("fst", V("w")), V("q")),
                        All("t", V("Q"), Imp(NotEq(V("t"), V("q")),
                            LE(At("binaryMultiplicity", V("t")), D(1)))),
                        BinaryIncoming(V("w")),
                        All("z", SlotType, Imp(LE(D(2), Card(At("incoming", V("z")))), EqF(V("z"), V("w")))),
                        EqF(At("resolvingRows"), Singleton(V("v"))))))))),
                "When J=s=1, exactly one actual target has two binary parents. Their two distinct "
                + "source rows each supply two child digits in a three-digit target, so they intersect. "
                + "The whole incoming surplus is spent at that shared slot w. Every other slot has at "
                + "most one incoming edge. The actual resolving-row count is one, selecting v."),
            Result("prescribed_of_single_collision", "unmarked-single-collision", "Actual histories from unmarked slot conditions",
                Scope(Imp(And(EqF(At("J"), D(1)), EqF(At("s"), D(1)), EqF(At("Xi"), D(1)),
                    UnmarkedShape), Some("R", Call("Prescribed", At("physicalForest")), And(
                        EqF(At("row", Call("H", V("R"))), At("row", Call("K", V("R")))),
                        EqF(At("row", Call("Ha", V("R"))), At("row", Call("Ka", V("R")))),
                        NotEq(At("row", Call("H", V("R"))), At("row", Call("Ha", V("R")))),
                        EqF(Card(At("support", Call("K", V("R")))), D(1)),
                        EqF(Card(At("support", Call("Ha", V("R")))), D(1)),
                        EqF(Card(At("support", Call("Ka", V("R")))), D(1)))))),
                "Prescribed contains actual binary parents A,B, a binary history H and unary history K "
                + "on w, and their unary children H1,K1 on v. In the displayed formula Ha and Ka denote "
                + "H1 and K1. UnmarkedShape is the following fully quantified source condition: the "
                + "unique collision slot is producing, differs from the pure resolving slot, every "
                + "nonbinary history on the collision slot is a singleton, and every history on the "
                + "resolving slot is a singleton. J=Xi=1 gives total history surplus two, so these two "
                + "doubled rows exhaust all repeated histories. The selected binary source rows and "
                + "actual outgoing edges determine the marked parent and child relationships. "
                + "Their literal waits agree on each common source row, their physical supports are "
                + "disjoint, and resolving children have different actual digits. The producing history "
                + "may itself be one of A,B; neither acyclicity nor a different producing target is required."))));

    internal static Formula V(string name) => F.Id(name);
    internal static Formula Nat => Seq(Mathbb, Sp, Grp(V("N")));
    internal static Formula Hist => At("History");
    internal static Formula SlotType => Call("Prod", V("Q"), Call("Fin", D(3)));
    internal static Formula Singleton(Formula x) => Seq(OpenBrace, x, CloseBrace);
    internal static Formula NotEq(Formula a, Formula b) => Seq(a, Neq, Sp, b);
    internal static Formula Some(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, V(name), Colon, type, Comma, Grp(body));
    internal static Formula BinaryIncoming(Formula w) => LE(D(2), Card(SetOf("a", At("incoming", w),
        Member(Call("fst", V("a")), At("productionRows")))));
    internal static Formula UnmarkedShape => All("w", SlotType, All("v", SlotType,
        Imp(BinaryIncoming(V("w")), Imp(Member(V("v"), At("resolvingRows")), And(
            Member(V("w"), At("productionRows")), NotEq(V("w"), V("v")),
            All("n", Hist, Imp(EqF(At("row", V("n")), V("w")),
                Imp(NotEq(Card(At("children", V("n"))), D(2)), EqF(Card(At("support", V("n"))), D(1))))),
            All("n", Hist, Imp(EqF(At("row", V("n")), V("v")), EqF(Card(At("support", V("n"))), D(1)))))))));
    internal static Formula NBinary => Seq(D(3), Times, Grp(Seq(V("P"), Minus, D(1))));
    internal static Formula Emptyset => Call("empty");
    internal static Formula At(string name, params Formula[] args) =>
        Call(name, [V("C"), V("hP"), V("I"), .. args]);
    internal static Formula Card(Formula set) => Call("card", set);
    internal static Formula EqF(Formula a, Formula b) => Seq(a, Eq, b);
    internal static Formula LE(Formula a, Formula b) => Seq(a, Le, Sp, b);
    internal static Formula Member(Formula a, Formula b) => Seq(a, InMacro, Sp, b);
    internal static Formula Imp(Formula a, Formula b) => Seq(Grp(a), Implies, Grp(b));
    internal static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, V(name), Colon, type, Comma, Grp(body));
    internal static Formula SetOf(string name, Formula set, Formula condition) =>
        Seq(OpenBrace, V(name), InMacro, Sp, set, Mid, Grp(condition), CloseBrace);
    internal static Formula SumOver(string name, Formula set, Formula summand) =>
        Seq(Sum, Underscore, Grp(Member(V(name), set)), Grp(summand));
    internal static Formula And(params Formula[] terms) =>
        Seq([.. terms.SelectMany((t, i) => i == 0 ? new[] { Grp(t) } : new[] { Land, Grp(t) })]);
    internal static Formula Instances(Formula body, params Formula[] types) =>
        Seq([.. types.Select(t => Seq(OpenBracket, t, CloseBracket)), body]);
    internal static Formula Scope(Formula body) => All("P", Nat, All("Q", Seq(V("Type"), Underscore, Grp(V("u"))),
        Instances(All("C", Call("Controller", V("P"), V("Q")),
        All("hP", Seq(D(1), Lt, V("P")), All("ell", Nat, All("h", Nat,
        All("I", Call("Initialized", V("C"), V("hP"), V("ell"), V("h")), body))))),
        Call("DecidableEq", V("Q")), Call("NeZero", Seq(D(3), Times, Sp, V("P"))))));
    internal static Formula Call(string name, params Formula[] args)
    {
        var items = new List<Formula> { Operatorname, Sp, Grp(V(name)), Open };
        for (var i = 0; i < args.Length; i++)
        {
            if (i > 0) items.Add(Comma);
            items.Add(args[i]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }
    internal static DocumentBlock ResultAt(string owner, string declaration, string id, string title,
        Formula statement, string explanation) => Describe.Lean(DescribeId.Create(id),
        DeclarationHandle.Create("D5/S3/ObserverMemory/Algorithms/" + owner + "." + declaration),
        H(title), StatementSource.FromAuthor(Disp(statement)), AssessedProvenance.FromRepo(),
        Blocks(Paragraph(Text(explanation))), DescribeRole.Theorem);
    private static DocumentBlock Result(string declaration, string id, string title,
        Formula statement, string explanation) => StationaryHistorySlotGraphDocument.ResultAt("StationaryHistorySlotGraph", declaration, id, title, statement, explanation);
}
