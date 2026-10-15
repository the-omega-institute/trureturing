using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic.Observer;
internal sealed class CompletionPositiveDriftRegionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "CompletionPositiveDriftRegion", H("Exact positive-drift completed region split"), Blocks(
            Describe.Lean(DescribeId.Create("positive-drift-region-split"),
                DeclarationHandle.Create("D5/S3/Arith/FibonacciAtomic/Observer/CompletionPositiveDriftRegion.positive_drift_region_split"),
                H("A positive cycle forces its whole forward region to be atomic or leafless"), Statement(),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("The system E is any finite list of positive equalities between normalized expressions in finite grounds, scalar tokens, decorated residuals and ordered pairs. A Boolean scalar mode chooses finite atomic tokens with natural parameters and nonnegative offsets or the leafless tree Omega. Repeated names share one valuation. Exposed equations include both orientations and pair cancellation, so all occurrences from all exposed definitions contribute edges.")),
                    Paragraph(Text("A PositiveCycle is a closed walk with a nonempty occurrence address on at least one edge and a strictly positive sum of integer head-power minus occurrence-power differences. The result therefore includes every simple cycle with these properties. Region is forward reachability from every cycle vertex in the entire exposed graph; it does not include incoming predecessors solely because they point into the region.")),
                    Paragraph(Text("FiniteAlternative assigns a unique natural rank to each region coordinate and replaces that coordinate by the corresponding atomic tree. InfiniteAlternative replaces every region coordinate by Omega. Both replacements leave every outside coordinate equal to its original value. Each alternative includes the reconstruction equality and the complete Solution predicate: every original equation and the arbitrary extra predicate must still hold. No branch is assumed satisfiable, and restrictions on the natural ranks arise only from these retained obligations.")),
                    Paragraph(Text("The finite argument propagates finiteness and nonincreasing native mass along occurrence edges. Strict decrease of positive mass on a strict edge forces cycle mass, and then every forward mass, to vanish. Zero mass characterizes the atomic orbit, whose injective rank gives uniqueness. The infinite argument uses infinite_subtree_origin to recover an actual subtree of the same original head tree. Along a walk, the concatenated address and cumulative powers satisfy one transport identity. Repeating the positive cycle gives arbitrarily deep native preimages; full prefixes force the root to be Omega, and occurrence edges propagate Omega throughout the region.")),
                    Paragraph(Text("The displayed equivalence proves both directions, and the second conjunct proves disjointness. The extra predicate may retain scalar guards, reconstruction constraints, mixed completed comparisons and predicates with captured finite-source chart parameters in their original types. This is a symbolic classification on unrestricted completed trees, not a bounded enumeration or a numerical certificate. It does not assert an expression-normalization algorithm, a cycle-search algorithm, a Presburger compiler, or a solver for arbitrary systems. The result is derived within the repository's native substitution theory; no external novelty is asserted."))
                ), DescribeRole.Theorem)
        )));

    private static StatementSource Statement()
    {
        var valuation = Arrow(Call("Fin", V("m")), Call("CompletionTree"));
        var finite = Call("FiniteAlternative", V("c"), V("mode"), V("param"), V("extra"), V("v"));
        var infinite = Call("InfiniteAlternative", V("c"), V("mode"), V("param"), V("extra"), V("v"));
        var solution = Call("Solution", V("E"), V("mode"), V("param"), V("extra"), V("v"));
        var conclusion = AndOf(IffOf(solution, OrOf(finite, infinite)),
            Seq(Neg, Sp, Par(AndOf(finite, infinite))));
        return StatementSource.FromAuthor(Disp(All("k,m", V("Nat"),
            All("E", Call("System", V("k"), V("m")),
            All("mode", Arrow(Call("Fin", V("k")), V("Bool")),
            All("param", Arrow(Call("Fin", V("k")), V("Nat")),
            All("root", Call("Fin", V("m")),
            All("c", Call("PositiveCycle", V("E"), V("root")),
            All("extra", Arrow(valuation, V("Prop")),
            All("v", valuation, conclusion))))))))));
    }

    private static Formula V(string n) => F.Id(n);
    private static Formula Par(Formula f) => Seq(Open, f, Close);
    private static Formula Call(string n, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(n))), [.. args]);
    private static Formula Arrow(Formula a, Formula b) => Seq(Par(a), Sp, To, Sp, Par(b));
    private static Formula IffOf(Formula a, Formula b) => Seq(Par(a), Sp, Iff, Sp, Par(b));
    private static Formula AndOf(Formula a, Formula b) => Seq(Par(a), Sp, Land, Sp, Par(b));
    private static Formula OrOf(Formula a, Formula b) => Seq(Par(a), Sp, Lor, Sp, Par(b));
    private static Formula All(string ns, Formula t, Formula b) => Seq(Forall, Sp,
        Seq(ns.Split(',').Select((n, i) => i == 0 ? V(n) : Seq(Comma, Sp, V(n))).ToArray()),
        Colon, Sp, t, Comma, Sp, Par(b));
}
