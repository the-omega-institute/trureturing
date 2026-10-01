using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic;

internal sealed class AtomicActionStateCapacityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciAtomic/AtomicActionStateCapacity.";
    private static Formula V(string name) => F.Id(name);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(name))), [.. args]);
    private static Formula Par(Formula body) => Seq(Open, body, Close);
    private static Formula EqOf(Formula a, Formula b) => Seq(a, Sp, Eq, Sp, b);
    private static Formula LeOf(Formula a, Formula b) => Seq(a, Sp, Leq, Sp, b);
    private static Formula Imp(Formula a, Formula b) => Seq(Par(a), Sp, Implies, Sp, Par(b));
    private static Formula All(string name, Formula body) => Seq(Forall, Sp, V(name), Comma, Sp, body);
    private static Formula Some(string name, Formula body) => Seq(Exists, Sp, V(name), Comma, Sp, body);
    private static Formula And(params Formula[] clauses)
    {
        var items = new List<Formula>();
        foreach (var clause in clauses)
        {
            if (items.Count > 0) items.AddRange([Sp, Land, Sp, RowBreak]);
            items.Add(Par(clause));
        }
        return Seq([.. items]);
    }

    private static DocumentBlock Definition(string name, string title, string prose) => Describe.Lean(
        DescribeId.Create("atomic-action-" + name.ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name), H(title), StatementSource.WithoutFormula(),
        AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A seam-preserving atomic action restores the complete modular state capacity.",
        H("Fibonacci Atomic Action State Capacity"),
        Blocks(
            Paragraph(Text("Fix a natural modulus m at least two. The input alphabet consists of the five "
                + "high-to-low Fibonacci windows together with one atomic action mu. The window transitions "
                + "are the complete legal affine reader, including the absorbing error state. The atomic "
                + "action applies one Fibonacci step to the composition and leaves the historical seam unchanged.")),
            Definition("Action", "The extended alphabet", "An input is either a five-window symbol or the atomic action mu."),
            Definition("atomicTransition", "Window and atomic transitions", "Window symbols use the raw affine transition. "
                + "On a live state (s,x), mu sends it to (s,Mx), and mu preserves the error state."),
            Definition("atomicOutput", "Immediate output", "A live state returns its current quantity modulo m; the error state returns the distinguished error label."),
            Definition("atomicMachine", "The initialized extended reader", "The reader starts at seam zero and composition (0,0), and evaluates every finite extended word."),
            Definition("atomicTask", "The extended finite-word task", "The task is the immediate output after every finite word over the five windows and mu."),
            Definition("capacity", "Complete state count", "N(m)=2m^2+1, counting both seam values for every composition and one error state."),
            Describe.Lean(DescribeId.Create("atomic-action-exact-capacity"),
                DeclarationHandle.Create(Prefix + "result"), H("Exact minimal capacity after adding mu"),
                StatementSource.FromAuthor(ResultFormula()), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For every m at least two, the raw state type is finite and has exactly N(m) states. "
                        + "The initialized extended reader is correct on every finite word and every raw state is reachable.")),
                    Paragraph(Text("The present quantity and the quantity after one mu action are the two linear forms "
                        + "(2,3) and (3,5). Their determinant is one, so they recover both composition coordinates "
                        + "over every ZMod(m). The empty continuation and one mu therefore distinguish any two live "
                        + "states with different compositions. A high window distinguishes the two seam values, and "
                        + "the empty word distinguishes the error state from every live state.")),
                    Paragraph(Text("Reachable histories together with these common distinguishing continuations form "
                        + "a finite distinguishing family. The general output-automaton lower-bound theorem then "
                        + "forces every correct finite-state reader to have at least N(m) states, while the raw reader "
                        + "attains this bound."))), DescribeRole.Theorem))));

    private static Formula ResultFormula()
    {
        var m = V("m");
        var stateType = Call("RawState", m);
        var n = Call("N", m);
        var machine = V("M");
        var state = V("q");
        var target = Call("T", m);
        var upper = Some("M", And(Call("Correct", machine, target),
            All("q", Imp(Seq(state, Sp, InMacro, Sp, stateType),
                Some("w", EqOf(Call("eval", machine, V("w")), state))))));
        var lower = All("S", Imp(Call("FiniteState", V("S")),
            All("M", Imp(Call("Correct", machine, target), LeOf(n, Call("card", V("S")))))));
        return Disp(All("m", Imp(And(Seq(m, Sp, InMacro, Sp, Call("Nats")), LeOf(D(2), m)),
            And(Call("FiniteState", stateType), EqOf(Call("card", stateType), n), upper, lower))));
    }
}

