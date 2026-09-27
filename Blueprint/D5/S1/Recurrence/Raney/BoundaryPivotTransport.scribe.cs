using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Raney;

internal sealed class BoundaryPivotTransportDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Raney/BoundaryPivotTransport.";
    private static readonly LibraryNoteRef Bks =
        LibraryNoteRef.Create("D5/L/Words/bugeaudkriegershallit2009morphic");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Boundary pivots make the signed endpoint corrections of actual descent edges eventually periodic.",
        H("Boundary-Pivot Transport"),
        Blocks(
            Paragraph(Text(
                "The BKS block mechanism supplies bounded edge corrections but does not by itself identify one "
                    + "finite family for every actual block. This owner follows the actual complementary letters "
                    + "at both endpoints through consecutive descent edges. Extremal choices make the next state "
                    + "deterministic, while retaining the left and right pivots as one paired state preserves their "
                    + "joint realization.")),
            Node("imageMeetsComplement", "A letter image contains an outside letter", ImageComplementFormula(),
                "For a Q-uniform morphism g, imageMeetsComplement(g,Delta,a) means that some offset in Fin(Q) "
                    + "has g(a)[offset] outside Delta. The existential offset is literal and is later extremized "
                    + "separately at the two boundaries.", DescribeRole.Definition,
                AssessedProvenance.FromRepo(Bks)),
            Node("actual_boundary_pivot_transport_at_power", "Two actual edges transport both boundary pivots",
                PivotTransportFormula(),
                "Fix q>0 and Q=P^q together with the Q-uniform fixed-word and support-stability facts. Given actual "
                    + "edges grandparent->parent and parent->child, the left boundary is represented by the outside "
                    + "exit at parent.first-1 and the right boundary by the outside exit at parent.last+1. On the "
                    + "left choose the rightmost image entry whose own image meets the complement; on the right "
                    + "choose the leftmost. The theorem returns exit, entry, and next-exit offsets in Fin(Q), their "
                    + "letters and extremality conditions, and the exact signed equations "
                    + "grand.first-Q*parent.first=Q*entry+nextExit+1-Q*(exit+1) and "
                    + "(grand.last+1)-Q*(parent.last+1)=Q*entry+nextExit-Q*exit.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Bks)),
            Node("actualBksPivotState", "The paired outside-letter state", PivotStateFormula(),
                "For endpoints (i,j), the state is the pair of word letters at quotient indices "
                    + "(i-1)/Q and (j+1)/Q. Natural subtraction gives the boundary-safe value at i=0, although "
                    + "descent edges themselves are late. Keeping the pair together is essential: separate left "
                    + "and right optima would not certify a common block.", DescribeRole.Definition,
                AssessedProvenance.FromRepo(Bks)),
            Node("actual_bks_pivot_state_dynamics_at_power", "Paired states determine the next state and correction",
                StateDynamicsFormula(),
                "For one fixed q and a sequence of blocks, state(k) is the paired pivot state of block(k+1), "
                    + "and validAt(k) requires the actual descent edges block(k+2)->block(k+1) and "
                    + "block(k+1)->block(k). Two valid windows with equal current states have equal following "
                    + "states. If their current and following states agree, their upper-edge signed displacements "
                    + "block(k+2).first-Q*block(k+1).first and the corresponding last+1 displacement are equal. "
                    + "The proof uses the extremal offsets returned by actual_boundary_pivot_transport_at_power, "
                    + "not an unrealized product of marginal choices.", DescribeRole.Theorem,
                AssessedProvenance.FromRepo(Bks)),
            Node("exists_eventually_periodic_actual_bks_signed_displacements",
                "Signed endpoint displacements are eventually periodic", PeriodicFormula(),
                "For every infinite sequence of actual descent edges at the selected power Q, there are N and a "
                    + "positive period t such that for all k>=N both corrections repeat after t: the left correction "
                    + "is block(k+1).first-Q*block(k).first, and the right correction uses last+1 in the same way. "
                    + "Finite paired states force a repeated state; deterministic transition propagates it, and "
                    + "equal adjacent state pairs give equal corrections. The conclusion is about signed Int "
                    + "displacements, so boundary borrowing is preserved.", DescribeRole.Theorem,
                AssessedProvenance.FromRepo(Bks)))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance) => Describe.Lean(
        DescribeId.Create("raney-boundary-pivot-" + name.Replace('_', '-').ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
        provenance, Blocks(Paragraph(Text(prose))), role);

    private static Formula V(string name) => F.Id(name);
    private static Formula N() => Seq(Mathbb, Grp(V("N")));
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(name))), [.. args]);
    private static Formula Eqn(Formula a, Formula b) => Seq(a, Sp, Eq, Sp, b);
    private static Formula LtF(Formula a, Formula b) => Seq(a, Sp, Lt, Sp, b);
    private static Formula LeF(Formula a, Formula b) => Seq(a, Sp, Leq, Sp, b);
    private static Formula And(params Formula[] xs) => Join(xs, Land);
    private static Formula Implies(Formula a, Formula b) => Seq(Paren(a), Sp, Rightarrow, Sp, Paren(b));
    private static Formula Paren(Formula x) => Seq(Open, x, Close);
    private static Formula Join(Formula[] xs, Formula op)
    {
        Formula result = xs[0];
        for (var i = 1; i < xs.Length; i++) result = Seq(result, Sp, op, Sp, xs[i]);
        return result;
    }
    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula Ex(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), domain, body);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(a, b);
    private static Formula Pair(Formula a, Formula b) => Seq(Open, a, Comma, Sp, b, Close);
    private static Formula LeftCorrection(Formula k) => Sub(
        Call("first", Call("blocks", Add(k, D(1)))),
        Mul(V("Q"), Call("first", Call("blocks", k))));
    private static Formula RightCorrection(Formula k) => Sub(
        Add(Call("last", Call("blocks", Add(k, D(1)))), D(1)),
        Mul(V("Q"), Add(Call("last", Call("blocks", k)), D(1))));

    private static Formula ImageComplementFormula() => Disp(Seq(
        Call("imageMeetsComplement", V("g"), V("Delta"), V("a")), Sp, Iff, Sp,
        Ex("t", Call("Fin", V("Q")), Seq(Neg, Sp, Paren(
            Seq(Call("uniformLetter", V("g"), V("a"), V("t")), Sp, InMacro, Sp, V("Delta")))))));

    private static Formula PivotTransportFormula() => Disp(Seq(
        And(Call("IsBksDescentStep", V("Q"), V("grand"), V("parent")),
            Call("IsBksDescentStep", V("Q"), V("parent"), V("child"))),
        Sp, Rightarrow, Sp,
        Call("existsExtremalPivotsWithSignedEquations", V("Q"), V("grand"), V("parent"), V("child"))));

    private static Formula PivotStateFormula() => Disp(Eqn(
        Call("actualBksPivotState", V("Q"), V("w"), Pair(V("i"), V("j"))),
        Pair(Call("w", Call("div", Sub(V("i"), D(1)), V("Q"))),
            Call("w", Call("div", Add(V("j"), D(1)), V("Q"))))));

    private static Formula StateDynamicsFormula() => Disp(Seq(
        Call("twoEdgeWindows", V("Q"), V("blocks"), V("i"), V("j")), Sp,
        Rightarrow, Sp, Paren(And(
            Paren(Implies(Eqn(Call("state", V("i")), Call("state", V("j"))),
                Eqn(Call("state", Add(V("i"), D(1))), Call("state", Add(V("j"), D(1)))))),
            Paren(Implies(And(Eqn(Call("state", V("i")), Call("state", V("j"))),
                    Eqn(Call("state", Add(V("i"), D(1))), Call("state", Add(V("j"), D(1))))),
                And(Eqn(
                        Sub(Call("first", Call("blocks", Add(V("i"), D(2)))),
                            Mul(V("Q"), Call("first", Call("blocks", Add(V("i"), D(1)))))),
                        Sub(Call("first", Call("blocks", Add(V("j"), D(2)))),
                            Mul(V("Q"), Call("first", Call("blocks", Add(V("j"), D(1))))))),
                    Eqn(
                        Sub(Add(Call("last", Call("blocks", Add(V("i"), D(2)))), D(1)),
                            Mul(V("Q"), Add(Call("last", Call("blocks", Add(V("i"), D(1)))), D(1)))),
                        Sub(Add(Call("last", Call("blocks", Add(V("j"), D(2)))), D(1)),
                            Mul(V("Q"), Add(Call("last", Call("blocks", Add(V("j"), D(1)))), D(1))))))))))));

    private static Formula PeriodicFormula()
    {
        var edge = All("k", N(), Call("IsBksDescentStep", Pow(V("P"), V("q")),
            Call("blocks", Add(V("k"), D(1))), Call("blocks", V("k"))));
        var repeats = All("k", N(), Implies(LeF(V("N0"), V("k")), And(
            Eqn(LeftCorrection(Add(V("k"), V("t"))), LeftCorrection(V("k"))),
            Eqn(RightCorrection(Add(V("k"), V("t"))), RightCorrection(V("k"))))));
        var eventual = Ex("N0", N(), Ex("t", N(), And(LtF(D(0), V("t")), repeats)));
        var paths = All("Delta", V("FinsetA"),
            All("blocks", Call("Seq", Call("Prod", N(), N())), Implies(edge, eventual)));
        return Disp(Ex("q", N(), And(LtF(D(0), V("q")), paths)));
    }
}
