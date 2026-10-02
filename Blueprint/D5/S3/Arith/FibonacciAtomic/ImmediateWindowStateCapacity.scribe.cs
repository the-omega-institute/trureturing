using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic;

internal sealed class ImmediateWindowStateCapacityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciAtomic/ImmediateWindowStateCapacity.";
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
        DescribeId.Create("immediate-window-" + name.ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name), H(title), StatementSource.WithoutFormula(),
        AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The complete high-to-low five-window task has exact minimal reachable modular state capacity.",
        H("Exact Immediate Fibonacci Window State Capacity"),
        Blocks(
            Paragraph(Text("Fix a natural modulus m at least two. Window bits are printed low to high, "
                + "but windows arrive high to low. The unit bit is fixed at zero. Empty words and "
                + "high-end null padding are legal. Every finite prefix immediately produces a residue; "
                + "an illegal prefix produces a distinct absorbing error label. There is no End symbol "
                + "and no requirement that the highest window be nonzero.")),
            Definition("clock", "The three-bit Fibonacci clock", "S(x)=M^3 x, where M(a,b)=(b,a+b). "
                + "Thus S(a,b)=(a+2b,2a+3b), and the quantity is q(a,b)=2a+3b."),
            Definition("displacement", "Window contributions", "The windows null, [2], [3], [25], [5] "
                + "have printed bits 000, 100, 010, 101, 001 and displacements (0,0), (1,0), (0,1), "
                + "(2,1), (1,1), respectively, in ZMod(m)^2."),
            Definition("rawTransition", "Legal affine updates and absorbing errors", "A live state "
                + "is (s,x). The seam s is the low bit of the previously read higher window. Reject when "
                + "s and the next window's high bit are both one; otherwise update x to Sx+d and the "
                + "seam to the new window's low bit. Error remains error under every window."),
            Definition("rawOutput", "Immediate residue or error", "A live state outputs qx modulo m. "
                + "The error state outputs none, distinct from every some(r) for r in ZMod(m)."),
            Definition("rawMachine", "The initialized complete reader", "The start state is seam zero "
                + "and composition (0,0); every input letter uses rawTransition and every reached state "
                + "is observed by rawOutput."),
            Definition("task", "The finite-word output task", "T_m(w) is the output of rawMachine(m) "
                + "after reading the entire finite word w from left to right. Correctness for all words "
                + "includes correctness at every prefix, at the empty word and after any error."),
            Definition("windowObserve", "The two sufficient quantity observations", "O_m(a,b)="
                + "(qx,qSx)=(2a+3b,8a+13b). The kernel is exactly the pairs (a,0) with 2a=0."),
            Definition("Observation", "The actual observation image", "I_m is the range of O_m on "
                + "ZMod(m)^2. It has m^2/gcd(m,2) elements. For even m it is a proper subset of "
                + "ZMod(m)^2, so independent arbitrary readout pairs are not states."),
            Definition("SummaryState", "The complete behavior states", "Q_m consists of one error "
                + "state and the pairs (s,z) with s in {0,1} and z in I_m."),
            Definition("summaryMachine", "A reader on the actual image", "The start state reduces "
                + "the raw start. To update a live image state, choose a composition representing z, "
                + "apply the raw transition, and reduce the result. The output is the first coordinate "
                + "of z, or error. Equality of the two observations is preserved by every legal affine "
                + "update, so the choice of representative does not affect the result."),
            Definition("capacity", "Exact state count", "N(m)=2m^2/gcd(m,2)+1, with natural-number "
                + "division. The gcd divides m^2, so this is an integer; N(2)=5."),
            Describe.Lean(DescribeId.Create("immediate-window-exact-capacity"),
                DeclarationHandle.Create(Prefix + "result"), H("Exact upper and lower bounds"),
                StatementSource.FromAuthor(ResultFormula()), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("In the formula, card denotes cardinality, FiniteState(S) means "
                        + "S is a finite state type, M ranges over deterministic output automata on the "
                        + "five windows with outputs Option(ZMod(m)), Correct(M,T_m) means equality "
                        + "of outputs on every finite word, and eval(M,w) is the state reached from "
                        + "the designated start. In the upper clause M has states Q_m; in the lower clause M has states S. The task is the same in both bounds.")),
                    Paragraph(Text("On seam zero, null, [3] and [5] are affine permutations. Since "
                        + "the residue set is finite, inverse permutations are positive repetitions "
                        + "of the same legal window. Combining these words realizes translations by "
                        + "(0,1) and (1,0), hence every composition on seam zero. Appending [2] reaches "
                        + "every composition on seam one. The word [2][5] reaches error.")),
                    Paragraph(Text("The observation kernel has gcd(m,2) elements by the cyclic-group "
                        + "two-torsion count. Its fibers give m^2/gcd(m,2) image states at each seam. "
                        + "Word induction proves that the image machine implements T_m everywhere. "
                        + "Every one of its states is reachable.")),
                    Paragraph(Text("The empty suffix distinguishes different present outputs and "
                        + "error from live states. A null suffix distinguishes different second "
                        + "observations. A [5] suffix distinguishes the two seams by legality versus "
                        + "error. Reachable representatives and these common suffixes form a "
                        + "distinguishing family, forcing every correct machine to have at least "
                        + "N(m) states. The image machine attains that bound."))), DescribeRole.Theorem))));

    private static Formula ResultFormula()
    {
        var m = V("m");
        var q = Call("Q", m);
        var n = Call("N", m);
        var machine = V("M");
        var word = V("w");
        var state = V("x");
        var target = Call("T", m);
        var upper = Some("M", And(Call("Correct", machine, target),
            All("x", Imp(Seq(state, Sp, InMacro, Sp, q),
                Some("w", EqOf(Call("eval", machine, word), state))))));
        var lower = All("S", Imp(Call("FiniteState", V("S")),
            All("M", Imp(Call("Correct", machine, target), LeOf(n, Call("card", V("S")))))));
        return Disp(All("m", Imp(And(Seq(m, Sp, InMacro, Sp, Call("Nats")), LeOf(D(2), m)),
            And(Call("FiniteState", q), EqOf(Call("card", q), n), upper, lower))));
    }
}
