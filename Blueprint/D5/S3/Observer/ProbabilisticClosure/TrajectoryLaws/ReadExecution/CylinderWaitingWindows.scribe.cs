using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.ReadExecution;

internal sealed class CylinderWaitingWindowsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/ReadExecution/CylinderWaitingWindows.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Full-word waiting windows from primitive cylinder data", H("Full-word waiting windows from primitive cylinder data"),
        Blocks(
            Node("survival-futures", "survivalFutures", SurvivalDefinition(), DescribeRole.Definition,
                "For every natural horizon H and length j, retain the full four-label future words v for which every coordinate k with k.val less than j has v(k) different from the marker 3. Empty horizons and j equal to zero are included."),
            Node("waiting-futures", "waitingFutures", WaitingDefinition(), DescribeRole.Definition,
                "The finite set difference survivalFutures(H,L) minus survivalFutures(H,U) is the event that the first marker lies strictly after L and at or before U. In the theorem L is less than U and U is at most H."),
            Node("no-marker-word", "noMarkerWord", WordDefinition(), DescribeRole.Definition,
                "A complete length-n word over the three nonmarker labels is embedded coordinate by coordinate by Fin.castSucc into Fin 4 and converted to a list. Label B is 2 and the marker is 3."),
            Node("prefixed", "prefixed", PrefixDefinition(), DescribeRole.Definition,
                "Append the complete word w to m copies of B. The copies remain part of the actual full history."),
            Node("finite-full-word-common-cut", "finite_full_word_common_cut", Statement(), DescribeRole.Theorem,
                "The data are full-word cylinder functions p and q. Original masses p are nonnegative and satisfy every finite continuation partition. Each comparison nonmarker word has positive q mass. The nonmarker-word sum equals S(n), and the joint nonmarker-past/no-marker-future cylinder sum equals S(n+j) whenever j is at most H. For every full word z, the raw rescaled masses 4^m*p(B^m z) converge to q(z). These are primitive cylinder assumptions, not conditional-row convergence or a packing premise. The conclusion constructs positive ordered ages, adjacent windows at one horizon, complete selected nonmarker words and distinct positive original histories B^(t-n(i))*w(i) of the same positive length t. Their comparison event masses exceed 1-2*theta and their actual event masses exceed 1-3*theta. The empty K case has H zero and a positive cut; the other quantifiers keep their full natural domains."),
            Paragraph(Text("The construction consumes finite_waiting_windows. Taking differences of the two primitive no-marker-future sums gives the scalar window mass. Finset.exists_lt_of_sum_lt selects one complete nonmarker word for each window; an event-conditioned mixture is never substituted for that word. Finite summation of the raw prefix limits and division by the positive limiting word mass derive the conditional event limits. Filter.eventually_all supplies one cut for the finitely many selected words, with t at least every selected age. Nonnegative continuation partitions normalize each actual row; two disjoint window masses greater than one half rule out coincident histories. This uses event masses directly and asserts no additional uniform-in-horizon convergence rate or TV modulus.")),
            Paragraph(Text("This is an abstract conditional supplier for original-passive-predictive-memory equations 13.5 through 13.10. The displayed primitive assumptions must still be instantiated for the original infinite diffusion and its exact e-start/full-domain law. In particular the three survival limits, stationary cylinder identities and raw B-prefix convergence are unpaid original-source adapters. Neither this result nor its scalar prerequisite establishes the original Theorem 13.2, the arbitrary convex-bank obstruction 13.3 or the marked/acquired certificates 13.4 for that source. No global literature novelty is asserted.")))));

    private static DocumentBlock.Describe Node(string id, string name, Formula formula, DescribeRole role, string text) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(name),
            StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), role);
    private static Formula V(string name) => F.Id(name);
    private static Formula Nat => Seq(Mathbb, Grp(V("N")));
    private static Formula Real => Seq(Mathbb, Grp(V("R")));
    private static Formula Par(Formula x) => Seq(Open, x, Close);
    private static Formula Call(string name, params Formula[] args)
    {
        var items = new List<Formula> { Operatorname, Grp(V(name)), Open };
        for (var i = 0; i < args.Length; i++)
        {
            if (i > 0) items.AddRange([Comma, Sp]);
            items.Add(args[i]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Par(Seq(V(name), Colon, Sp, type)), Comma, Sp, body);
    private static Formula Some(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, Par(Seq(V(name), Colon, Sp, type)), Comma, Sp, body);
    private static Formula Eqn(Formula x, Formula y) => Seq(x, Sp, Eq, Sp, y);
    private static Formula Lt(Formula x, Formula y) => Rel(x, FormulaRelationOperator.LessThan, y);
    private static Formula Le(Formula x, Formula y) => Rel(x, FormulaRelationOperator.LessThanOrEqual, y);
    private static Formula Imp(Formula x, Formula y) => Seq(Par(x), Sp, Rightarrow, Sp, y);
    private static Formula Both(params Formula[] clauses)
    {
        var result = clauses[^1];
        for (var i = clauses.Length - 2; i >= 0; i--)
            result = Seq(Par(clauses[i]), Sp, Land, Sp, Par(result));
        return result;
    }
    private static Formula SumAll(string index, Formula type, Formula body) =>
        Seq(new Formula.Subscript(Sum, Seq(V(index), Colon, Sp, type)), Sp, Par(body));
    private static Formula SumIn(string index, Formula set, Formula body) =>
        Seq(new Formula.Subscript(Sum, Seq(V(index), Sp, InMacro, Sp, set)), Sp, Par(body));
    private static Formula Fin(Formula n) => Call("Fin", n);
    private static Formula Word(Formula n, int alphabet) => new Formula.TypeArrow(Fin(n), Fin(D(alphabet)));
    private static Formula List => Call("List", Fin(D(4)));
    private static Formula NM(Formula w) => Call("noMarkerWord", w);
    private static Formula Future => Call("ofFn", V("v"));
    private static Formula Append(Formula u, Formula v) => Call("append", u, v);
    private static Formula Mass(string f, Formula u, Formula set) =>
        SumIn("v", set, Call(f, Append(u, Future)));
    private static Formula Limit(Formula body, Formula value) =>
        Call("Tendsto", LambdaFormula("m", Nat, body), V("atTop"), Call("nhds", value));
    private static Formula SurvivalDefinition()
    {
        var coordinate = Imp(Lt(Call("val", V("k")), V("j")),
            Seq(Call("v", V("k")), Sp, Neq, Sp, D(3)));
        var predicate = LambdaFormula("v", Word(V("H"), 4), All("k", Fin(V("H")), coordinate));
        var body = Eqn(Call("survivalFutures", V("H"), V("j")), Call("filter", predicate, V("univ")));
        return All("H", Nat, All("j", Nat, body));
    }
    private static Formula WaitingDefinition()
    {
        var body = Eqn(Call("waitingFutures", V("H"), V("L"), V("U")),
            Call("sdiff", Call("survivalFutures", V("H"), V("L")), Call("survivalFutures", V("H"), V("U"))));
        return All("H", Nat, All("L", Nat, All("U", Nat, body)));
    }
    private static Formula WordDefinition()
    {
        var fn = LambdaFormula("i", Fin(V("n")), Call("castSucc", Call("w", V("i"))));
        var body = Eqn(NM(V("w")), Call("ofFn", fn));
        return All("n", Nat, All("w", Word(V("n"), 3), body));
    }
    private static Formula PrefixDefinition()
    {
        var body = Eqn(Call("prefixed", V("m"), V("w")), Append(Call("replicate", V("m"), D(2)), V("w")));
        return All("m", Nat, All("w", List, body));
    }
    private static Formula Age => Call("n", V("i"));
    private static Formula Lower => Call("b", Call("castSucc", V("i")));
    private static Formula Upper => Call("b", Call("succ", V("i")));
    private static Formula Selected => NM(Call("w", V("i")));
    private static Formula History => Call("prefixed", Subtract(V("t"), Age), Selected);
    private static Formula Event => Call("waitingFutures", V("H"), Lower, Upper);
    private static Formula Conclusion()
    {
        var rows = All("i", Fin(V("K")), Both(
            Lt(D(0), Age), Le(Age, V("t")), Lt(Lower, Upper), Le(Upper, V("H")),
            Eqn(Call("length", History), V("t")),
            Lt(Subtract(D(1), Multiply(D(2), V("theta"))),
                new Formula.Fraction(Mass("q", Selected, Event), Call("q", Selected))),
            Lt(D(0), Call("p", History)),
            Lt(Subtract(D(1), Multiply(D(3), V("theta"))),
                new Formula.Fraction(Mass("p", History, Event), Call("p", History)))));
        var result = Both(Eqn(Call("b", D(0)), D(0)), Eqn(Call("b", Call("last", V("K"))), V("H")),
            Seq(Par(Eqn(V("K"), D(0))), Sp, Iff, Sp, Par(Eqn(V("H"), D(0)))),
            Call("StrictMono", V("b")), Call("StrictMono", V("n")), Lt(D(0), V("t")), rows,
            Call("Injective", LambdaFormula("i", Fin(V("K")), History)));
        result = Some("w", All("i", Fin(V("K")), Word(Age, 3)), result);
        result = Some("b", new Formula.TypeArrow(Fin(Add(V("K"), D(1))), Nat), result);
        result = Some("n", new Formula.TypeArrow(Fin(V("K")), Nat), result);
        result = Some("t", Nat, result);
        return Some("H", Nat, result);
    }
    private static Formula Statement()
    {
        var result = All("K", Nat, All("theta", Real,
            Imp(Both(Lt(D(0), V("theta")), Lt(V("theta"), new Formula.Fraction(D(1), D(1, 6)))), Conclusion())));
        result = Imp(All("z", List, Limit(Multiply(new Formula.Power(D(4), V("m")),
            Call("p", Call("prefixed", V("m"), V("z")))), Call("q", V("z")))), result);
        var cylinderSum = SumAll("z", Word(V("r"), 3),
            Mass("q", NM(V("z")), Call("survivalFutures", V("H"), V("j"))));
        var cylinderIdentity = Imp(Le(V("j"), V("H")), Eqn(cylinderSum, Call("S", Add(V("r"), V("j")))));
        result = Imp(All("r", Nat, All("H", Nat, All("j", Nat, cylinderIdentity))), result);
        result = Imp(All("r", Nat, Eqn(SumAll("z", Word(V("r"), 3), Call("q", NM(V("z")))), Call("S", V("r")))), result);
        result = Imp(All("r", Nat, All("z", Word(V("r"), 3), Lt(D(0), Call("q", NM(V("z")))))), result);
        result = Imp(All("z", List, All("H", Nat,
            Eqn(SumAll("v", Word(V("H"), 4), Call("p", Append(V("z"), Future))), Call("p", V("z"))))), result);
        result = Imp(All("z", List, Le(D(0), Call("p", V("z")))), result);
        result = All("p", new Formula.TypeArrow(List, Real), All("q", new Formula.TypeArrow(List, Real), result));
        result = Imp(Call("Tendsto", LambdaFormula("m", Nat,
            new Formula.Fraction(Call("S", Add(V("m"), D(1))), Call("S", V("m")))), V("atTop"), Call("nhds", D(1))), result);
        result = Imp(Call("Tendsto", V("S"), V("atTop"), Call("nhds", D(0))), result);
        result = Imp(All("m", Nat, Lt(D(0), Call("S", V("m")))), result);
        return All("S", new Formula.TypeArrow(Nat, Real), result);
    }
}
