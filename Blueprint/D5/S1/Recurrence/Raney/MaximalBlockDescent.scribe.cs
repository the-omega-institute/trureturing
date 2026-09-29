using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Raney;

internal sealed class MaximalBlockDescentDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Raney/MaximalBlockDescent.";
    private static readonly LibraryNoteRef Bks =
        LibraryNoteRef.Create("D5/L/Words/bugeaudkriegershallit2009morphic");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every actual maximal block descends through literal BKS edges to one of finitely many bounded root forms.",
        H("Actual Maximal-Block Descent"),
        Blocks(
            Paragraph(Text(
                "This owner turns the one-step BKS predecessor/successor mechanism into a finite descent "
                    + "for actual intervals. One support-stabilizing power q is chosen once and returned with "
                    + "all of its fixed-word data. Every edge has a strictly smaller right endpoint, so the "
                    + "chain terminates without an assumed infinite extension.")),
            Node("exists_uniform_power_bks11_bks12_evolution", "One power supports inverse and forward evolution",
                EvolutionFormula(),
                "For a finite alphabet, P>1, a P-uniform morphism, and its pointwise fixed word, choose q>0 "
                    + "and Q=P^q. The powered morphism g is Q-uniform, fixes the same word by Q-cells, and has "
                    + "stable two-step support. Whenever an actual block satisfies the three displayed late, "
                    + "long, and quotient-span bounds, the theorem constructs a unique nearby actual predecessor, "
                    + "proves its right endpoint is smaller, and identifies the original interval as the unique "
                    + "successor crossing the central image.", DescribeRole.Theorem,
                AssessedProvenance.FromRepo(Bks)),
            Node("intervalWord", "The literal word on a finite interval", IntervalWordFormula(),
                "For endpoints (i,j), the list has natural length j+1-i and entry t equal to w(i+t). Natural "
                    + "subtraction totalizes reversed endpoints; every downstream use supplies an ordered actual "
                    + "maximal interval.", DescribeRole.Definition, AssessedProvenance.FromRepo(Bks)),
            Node("IsBksDescentStep", "One actual inverse/image edge", StepFormula(),
                "A descent edge from parent to child requires both endpoints to be actual maximal Delta intervals. "
                    + "The child lies within Q of the quotient endpoints, remains late and longer than Q^2, and "
                    + "has a strictly smaller right endpoint. The central Q-image lies inside the parent. The "
                    + "left and right literal context words between the parent boundary and that central image "
                    + "each have length at most 2Q^2.", DescribeRole.Definition,
                AssessedProvenance.FromRepo(Bks)),
            Node("IsBksRoot", "The exact stopping disjunction", RootFormula(),
                "An interval is a root precisely when at least one hypothesis for the next conservative descent "
                    + "fails: its left quotient is below 2Q, its length is at most 2Q^2, or its quotient span is "
                    + "at most Q^2+2Q. These alternatives preserve short, early, and narrow cases rather than "
                    + "discarding them.", DescribeRole.Definition, AssessedProvenance.FromRepo(Bks)),
            Node("IsBksDescentChain", "Finite chains of actual descent edges", ChainFormula(),
                "The root constructor gives a zero-edge chain at an actual maximal root. The step constructor "
                    + "prepends one IsBksDescentStep to an existing finite tail. Thus every member of a chain is "
                    + "an actual interval, and no coinductive or occurrence-converse assumption enters.",
                DescribeRole.Definition, AssessedProvenance.FromRepo(Bks)),
            Node("earlyBksRoots", "Early roots retain actual endpoints", EarlyRootsFormula(),
                "This set contains exactly the actual maximal intervals whose first endpoint is below 2Q^2. "
                    + "Maximality makes an interval unique at a fixed first endpoint, which is later used to prove "
                    + "the set finite.", DescribeRole.Definition, AssessedProvenance.FromRepo(Bks)),
            Node("lateBksRootWords", "Bounded literal words of late roots", LateRootsFormula(),
                "A list belongs when it is the literal intervalWord of an actual BKS root whose first endpoint is "
                    + "at least 2Q^2. Root failure then bounds the list length by Q(Q^2+2Q), so finite alphabet "
                    + "and bounded length give a finite set without imposing a false endpoint bound.",
                DescribeRole.Definition, AssessedProvenance.FromRepo(Bks)),
            Node("bksContextPairs", "Literal left and right edge contexts", ContextFormula(),
                "For every actual descent edge, the pair records the parent subword before the central image and "
                    + "the parent subword after it. The edge definition bounds both lengths by 2Q^2; pairing them "
                    + "retains the joint correction that later controls one actual realization.",
                DescribeRole.Definition, AssessedProvenance.FromRepo(Bks)),
            Node("exists_bounded_root_descent_chain", "Every actual block reaches finite root data",
                BoundedChainFormula(),
                "The theorem returns one q>0, Q=P^q, the powered uniform/fixed/support facts, finiteness of early "
                    + "roots, late root words, and context pairs, and a chain for every actual maximal interval. "
                    + "The chain is built by well-founded induction on the right endpoint using strict descent. "
                    + "At its terminal root, either the start is below 2Q^2 or the literal length is at most "
                    + "Q(Q^2+2Q). This is the finite-root input consumed by boundary transport and final assembly.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Bks)))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance) => Describe.Lean(
        DescribeId.Create("raney-maximal-block-descent-" + name.Replace('_', '-').ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
        provenance, Blocks(Paragraph(Text(prose))), role);

    private static Formula V(string name) => F.Id(name);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(name))), [.. args]);
    private static Formula Eqn(Formula a, Formula b) => Seq(a, Sp, Eq, Sp, b);
    private static Formula LtF(Formula a, Formula b) => Seq(a, Sp, Lt, Sp, b);
    private static Formula LeF(Formula a, Formula b) => Seq(a, Sp, Leq, Sp, b);
    private static Formula And(params Formula[] xs) => Join(xs, Land);
    private static Formula Or(params Formula[] xs) => Join(xs, Lor);
    private static Formula IffF(Formula a, Formula b) => Seq(a, Sp, Iff, Sp, b);
    private static Formula Paren(Formula x) => Seq(Open, x, Close);
    private static Formula Join(Formula[] xs, Formula op)
    {
        Formula result = xs[0];
        for (var i = 1; i < xs.Length; i++) result = Seq(result, Sp, op, Sp, xs[i]);
        return result;
    }
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(a, b);
    private static Formula Pair(Formula a, Formula b) => Seq(Open, a, Comma, Sp, b, Close);

    private static Formula EvolutionFormula() => Disp(Seq(
        Call("UniformFixed", V("P"), V("mu"), V("w")), Sp, Land, Sp, LtF(D(1), V("P")),
        Sp, Rightarrow, Sp, Call("existsPowerEvolution", V("P"), V("mu"), V("w"))));

    private static Formula IntervalWordFormula() => Disp(Eqn(
        Call("intervalWord", V("w"), Pair(V("i"), V("j"))),
        Call("ofFn", Seq(V("t"), Sp, Mapsto, Sp, Call("w", Add(V("i"), V("t")))),
            Sub(Add(V("j"), D(1)), V("i")))));

    private static Formula StepFormula() => Disp(IffF(
        Call("IsBksDescentStep", V("Q"), V("Delta"), V("w"), V("parent"), V("child")),
        Paren(And(
            Call("ActualMaximal", V("Delta"), V("w"), V("parent")),
            Call("ActualMaximal", V("Delta"), V("w"), V("child")),
            Call("quotientEndpointBounds", V("Q"), V("parent"), V("child")),
            LtF(Call("snd", V("child")), Call("snd", V("parent"))),
            Call("centralImageInside", V("Q"), V("Delta"), V("w"), V("parent"), V("child")),
            LeF(Call("leftContextLength", V("Q"), V("w"), V("parent"), V("child")), Mul(D(2), Pow(V("Q"), D(2)))),
            LeF(Call("rightContextLength", V("Q"), V("w"), V("parent"), V("child")), Mul(D(2), Pow(V("Q"), D(2))))))));

    private static Formula RootFormula() => Disp(IffF(
        Call("IsBksRoot", V("Q"), Pair(V("i"), V("j"))),
        Paren(Or(
            LtF(Call("div", V("i"), V("Q")), Mul(D(2), V("Q"))),
            LeF(Sub(Add(V("j"), D(1)), V("i")), Mul(D(2), Pow(V("Q"), D(2)))),
            LeF(Sub(Add(Call("div", V("j"), V("Q")), D(1)), Call("div", V("i"), V("Q"))),
                Add(Pow(V("Q"), D(2)), Mul(D(2), V("Q"))))))));

    private static Formula ChainFormula() => Disp(new Formula.Aligned([
        Seq(Call("ActualMaximal", V("e")), Sp, Land, Sp, Call("IsBksRoot", V("Q"), V("e")),
            Sp, Rightarrow, Sp, Call("IsBksDescentChain", V("Q"), V("e"), V("e"))),
        Seq(Call("IsBksDescentStep", V("Q"), V("p"), V("c")), Sp, Land, Sp,
            Call("IsBksDescentChain", V("Q"), V("c"), V("r")), Sp, Rightarrow, Sp,
            Call("IsBksDescentChain", V("Q"), V("p"), V("r")))
    ]));

    private static Formula EarlyRootsFormula() => Disp(Eqn(
        Call("earlyBksRoots", V("Q"), V("Delta"), V("w")),
        Call("setOf", V("e"), And(Call("ActualMaximal", V("Delta"), V("w"), V("e")),
            LtF(Call("fst", V("e")), Mul(D(2), Pow(V("Q"), D(2))))))));

    private static Formula LateRootsFormula() => Disp(Eqn(
        Call("lateBksRootWords", V("Q"), V("Delta"), V("w")),
        Call("setOfRootWords", V("e"), Call("intervalWord", V("w"), V("e")),
            Call("ActualMaximal", V("Delta"), V("w"), V("e")),
            Call("IsBksRoot", V("Q"), V("e")),
            LeF(Mul(D(2), Pow(V("Q"), D(2))), Call("fst", V("e"))))));

    private static Formula ContextFormula() => Disp(Eqn(
        Call("bksContextPairs", V("Q"), V("Delta"), V("w")),
        Call("setOfLiteralEdgeContexts", V("Q"), V("Delta"), V("w"))));

    private static Formula BoundedChainFormula() => Disp(Seq(
        Call("UniformFixed", V("P"), V("mu"), V("w")), Sp, Land, Sp, LtF(D(1), V("P")),
        Sp, Rightarrow, Sp,
        Call("existsFiniteRootDescentData", V("P"), V("mu"), V("w"),
            Call("earlyBksRoots", V("Q"), V("Delta"), V("w")),
            Call("lateBksRootWords", V("Q"), V("Delta"), V("w")),
            Call("bksContextPairs", V("Q"), V("Delta"), V("w")))));
}
