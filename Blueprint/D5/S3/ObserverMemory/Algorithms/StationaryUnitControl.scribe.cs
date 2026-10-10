using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.Algorithms;

internal sealed class StationaryUnitControlDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Stationary unit instructions preserve physical phases and force disjoint nominal memory for initialized runs.",
        H("Stationary unit control and literal memory"),
        Blocks(
            Paragraph(Text(
                "A controller consists of one common initial state and a total table on Q. "
                + "Its instructions are wait(next), read(row), and halt(original label). "
                + "The table receives no phase, input label, time, read index, or history. "
                + "Configurations pair a physical element of ZMod(3P) with a control state. "
                + "A wait adds exactly one to the phase. A read preserves the phase and "
                + "uses its actual digit floor(val/P) in Fin 3. Halt has no successor.")),
            Paragraph(Text(
                "Initialized supplies a finite correct run for every original label x, "
                + "starting at phase x and the same initial control. WordShape requires "
                + "ell initial waits, a first read, a positive wait between consecutive "
                + "reads, at most h reads, and a final read immediately followed by halt. "
                + "Stop times and read indices are mathematical indices of actual execution. "
                + "The total trajectory extension is absorbing at halt and adds no action. "
                + "Literal waits, wraps, ell at least 3P, singleton continuations, unused "
                + "nominal states, and terminating cycles of read controls remain allowed.")),
            Result("finite_run_unique", "finite-run-unique", "Deterministic finite outcomes",
                Scope(All("c", Call("Configuration", V("P"), V("Q")),
                    AllN(["n", "m"], AllLabels(["x", "y"],
                    Imp(And(Call("FiniteRun", V("C"), V("hP"), V("c"), V("n"), V("x")),
                        Call("FiniteRun", V("C"), V("hP"), V("c"), V("m"), V("y"))),
                        And(EqF(V("n"), V("m")), EqF(V("x"), V("y")))))))),
                "Two finite executions from the same physical configuration have the same "
                + "stop time and stored output. An earlier claimed halt contradicts the "
                + "other execution's nonhalting prefix; equal stop times have equal labels."),
            Result("initialized_configuration_unique", "initialized-configuration-unique",
                "Original inputs and event times are separated",
                InitializedScope(AllLabels(["x", "y"], AllN(["t", "v"],
                    Imp(And(LE(V("t"), Length("x")), LE(V("v"), Length("y")),
                        EqF(Run("x", V("t")), Run("y", V("v")))),
                        And(EqF(V("x"), V("y")), EqF(V("t"), V("v"))))))),
                "Equal configurations on any two initialized paths force equality of "
                + "their original labels and times. The proof compares the finite suffixes "
                + "of those same paths. Different input labels cannot share an output; "
                + "a repeated configuration on one finite path cannot reach its first halt."),
            Result("waits_physical_execution", "waits-physical-execution",
                "Every literal wait is an actual unit action",
                Scope(AllN(["d"], AllQ(["q", "target"],
                    Imp(Call("Waits", V("C"), V("d"), V("q"), V("target")),
                    All("s", Label, EqF(Call("run", V("C"), V("hP"),
                        Pair(V("s"), V("q")), V("d")),
                        Pair(Seq(V("s"), Plus, V("d")), V("target")))))))),
                "A chain of d waits moves phase s to s+d in ZMod(3P) and reaches its "
                + "specified control target. The natural d counts actual unit actions; "
                + "only the physical phase is modular, so full wraps do not shorten a chain."),
            Result("waits_to_read_unique", "waits-to-read-unique",
                "An intersecting wait has one first future read",
                Scope(AllN(["d", "e"], AllQ(["q", "target", "other"],
                    Imp(And(Call("Waits", V("C"), V("d"), V("q"), V("target")),
                        Call("Waits", V("C"), V("e"), V("q"), V("other")),
                        Read(V("target")), Read(V("other"))),
                        And(EqF(V("d"), V("e")), EqF(V("target"), V("other")))))), false),
                "Two pure wait paths from one control state to read states have equal "
                + "literal lengths and the same read target. At each unit position the "
                + "stationary instruction determines the successor. A read instruction "
                + "cannot also be a wait, excluding unequal first-read distances."),
            Result("waits_chain_injective", "waits-chain-injective",
                "Distinct unit positions in a wait chain",
                Scope(AllN(["d"], AllQ(["q", "target"],
                    Imp(And(Call("Waits", V("C"), V("d"), V("q"), V("target")),
                        Read(V("target"))),
                        Call("Injective", Seq(V("i"), Colon, Call("Fin", V("d")), Mapsto,
                            Call("iterate", Call("waitNext", V("C")),
                                Call("val", V("i")), V("q"))))))), false),
                "The map from Fin d to successive wait controls is injective when the "
                + "chain ends at a read. Equal internal states would give equal remaining "
                + "first-read distances and therefore equal unit positions."),
            Result("initialized_prefix", "initialized-prefix", "The prefix covers every phase",
                InitializedScope(AllLabels(["x"], AllN(["t"],
                    Imp(LE(V("t"), V("ell")), EqF(Run("x", V("t")),
                        Pair(Seq(V("x"), Plus, V("t")), Prefix(V("t")))))))),
                "For t at most ell, every original x has phase x+t and the same prefix "
                + "control. This includes the first read at t=ell, even when the prefix "
                + "wraps around the physical circle several times."),
            Result("prefix_first_read_no_return", "prefix-first-read-no-return",
                "No later return to a prefix or first-read control",
                InitializedScope(AllLabels(["x"], AllN(["i", "t"],
                    Imp(And(LE(V("i"), V("ell")), LT(V("i"), V("t")),
                        LE(V("t"), Length("x"))),
                        Seq(Call("control", Run("x", V("t"))), Neq, Prefix(V("i"))))))),
                "A later occurrence of a prefix control has the same phase as the "
                + "earlier occurrence for y=phase-i. The exact initialized premise for "
                + "that original y supplies the comparison path. Configuration uniqueness "
                + "then contradicts the different times; no original input is discarded."),
            Result("nonroot_has_arrival", "nonroot-has-arrival",
                "Every nonroot read has a positive incoming literal tail",
                InitializedScope(All("q", Call("NonrootRead", V("C"), V("hP"), V("I")),
                    Seq(Exists, Sp, V("d"), Colon, N, Comma,
                        Call("Nonempty", Call("Arrival", V("C"), V("hP"), V("I"),
                            Call("control", V("q")), V("d")))))),
                "Choose an actual occurrence of a nonroot read and the greatest earlier "
                + "read index on its original input path. Every intervening instruction "
                + "is a wait, and the word conditions force a positive gap. Arrival "
                + "retains that original input, the source read time, the literal length, "
                + "the unit chain, and the exact target occurrence."),
            Result("mem_arrival_lengths", "arrival-length-membership",
                "The finite arrival inventory contains exactly the literal arrivals",
                InitializedScope(All("q", V("Q"), All("d", N, Seq(
                    V("d"), InMacro, Sp, Call("arrivalLengths", V("C"), V("hP"), V("I"), V("q")), Iff,
                    Call("Nonempty", Call("Arrival", V("C"), V("hP"), V("I"), V("q"), V("d"))))))),
                "The finite inventory ranges over the stopping times of all original inputs. An arrival's "
                + "positive literal length is below its own input's stop time, so every actual arrival appears. "
                + "This membership characterization connects original forest requests to actualL."),
            Result("full_nominal_resource_embedding", "full-nominal-resource-embedding",
                "Disjoint resource embedding into the full nominal carrier",
                InitializedScope(Call("Nonempty", Call("Embedding",
                    Call("Resource", V("C"), V("hP"), V("I")), V("Q")))),
                "Resource is the tagged sum of ZMod(3P), all actual read controls, Fin ell, "
                + "and the pairs (q,i) with q a nonroot actual read and i in Fin(actualL(q)). "
                + "The finite set of realized incoming lengths defines actualL by its "
                + "maximum, and longestArrival chooses an actual request attaining it. "
                + "Terminal labels separate the original outputs. Instruction kinds "
                + "separate terminal, read, and wait controls. First-future-read uniqueness "
                + "separates different target tails and separates every nonroot tail from "
                + "the common prefix. Within a tail, remaining distances separate positions. "
                + "The codomain is Q itself. Thus unused nominal states remain charged. "
                + "For finite Q, finite cardinality applied to this embedding gives "
                + "3P+r+ell+sum_q actualL(q) at most card Q. The embedding also holds "
                + "without a finiteness assumption on Q."))));

    private static Formula V(string name) => F.Id(name);
    private static Formula N => Seq(Mathbb, Sp, Grp(V("N")));
    private static Formula Label => Call("ZMod", Seq(D(3), Times, Sp, V("P")));
    private static Formula Call(string name, params Formula[] args)
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
    private static Formula Pair(Formula x, Formula y) => Seq(Open, x, Comma, y, Close);
    private static Formula EqF(Formula x, Formula y) => Seq(x, Eq, y);
    private static Formula LE(Formula x, Formula y) => Seq(x, Le, Sp, y);
    private static Formula LT(Formula x, Formula y) => Seq(x, Lt, y);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, V(name), Colon, type, Comma, Grp(body));
    private static Formula AllN(string[] names, Formula body) =>
        names.Reverse().Aggregate(body, (current, name) => All(name, N, current));
    private static Formula AllQ(string[] names, Formula body) =>
        names.Reverse().Aggregate(body, (current, name) => All(name, V("Q"), current));
    private static Formula AllLabels(string[] names, Formula body) =>
        names.Reverse().Aggregate(body, (current, name) => All(name, Label, current));
    private static Formula Imp(Formula premise, Formula body) =>
        Seq(Grp(premise), Implies, Grp(body));
    private static Formula And(params Formula[] clauses)
    {
        var items = new List<Formula>();
        foreach (var clause in clauses)
        {
            if (items.Count > 0) items.Add(Land);
            items.Add(Grp(clause));
        }
        return Seq([.. items]);
    }
    private static Formula Read(Formula q) => Call("IsRead", V("C"), q);
    private static Formula Length(string x) => Call("length", V("I"), V(x));
    private static Formula Prefix(Formula t) => Call("prefixState", V("C"), V("hP"), t);
    private static Formula Run(string x, Formula t) => Call("run", V("C"), V("hP"),
        Pair(V(x), Call("initial", V("C"))), t);
    private static Formula Scope(Formula body, bool physical = true) =>
        All("P", N, All("Q", Seq(V("Type"), Underscore, Grp(V("u"))),
        All("C", Call("Controller", V("P"), V("Q")),
            physical ? All("hP", LT(D(1), V("P")), body) : body)));
    private static Formula InitializedScope(Formula body) => Scope(
        AllN(["ell", "h"], All("I", Call("Initialized", V("C"), V("hP"),
            V("ell"), V("h")), body)));

    private static DocumentBlock Result(string declaration, string id, string heading,
        Formula statement, string explanation) => Describe.Lean(
            DescribeId.Create(id),
            DeclarationHandle.Create("D5/S3/ObserverMemory/Algorithms/StationaryUnitControl."
                + declaration),
            H(heading), StatementSource.FromAuthor(Disp(statement)),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(explanation))),
            DescribeRole.Theorem);
}
