using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Domination;

internal sealed class TotalDominationBlowupDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/Domination/TotalDominationBlowup.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Independent fibres retain actual total-domination subsets and give the known polynomial substitution.",
        H("Independent-fibre substitution on actual subsets"), Blocks(
            Paragraph(Text("V and W are actual finite vertex types, with Fintype instances. G is an arbitrary SimpleGraph on V. For the total-domination identity W is nonempty. Each v is replaced by the independent fibre consisting of all (v,i) with i in W. Vertices in two fibres are adjacent exactly when their original vertices are adjacent. An occupied fibre contributes a nonempty actual subset, not one selected representative.")),
            Node("blowupGraph", "The actual independent-fibre graph", Eq(Call("blowupGraph", V("G"), V("W")), Call("comap", V("G"), Call("fst"))),
                "The result has vertex type V times W and adjacency G.Adj(a.fst,b.fst). There are no internal edges in a fibre. This is SimpleGraph.comap Prod.fst, so symmetry and looplessness are inherited. It is the edgeless-fibre lexicographic blowup, not a clique blowup.", DescribeRole.Definition),
            Node("subsetFamilyEquiv", "Actual subset-to-fibre equivalence", Call("subsetFamilyEquiv"),
                "For finite V and W this is an equivalence between Finset(V times W) and V -> Finset W. A global subset S maps at v to all i in W with (v,i) in S. The inverse maps f to all (v,i) with i in f(v). Extensional membership proves the inverse laws. The private cardinal theorem says the inverse subset cardinality equals sum_v card(f(v)).", DescribeRole.Definition),
            Node("support", "Occupied fibres", Eq(Call("support", V("f")), Call("occupiedFibres", V("f"))),
                "occupiedFibres(f) is the finite subset of all v in V for which f(v) is nonempty. For nonempty W, the private total_family theorem proves that the actual inverse subset totally dominates blowupGraph G W if and only if this support totally dominates G. The forward direction tests any vertex in each fibre; the reverse direction uses a selected neighbour in an occupied adjacent fibre. Selected vertices obey exactly the same condition.", DescribeRole.Definition),
            Node("blowup_polynomial", "The known actual-subset substitution identity", Eq(Call("complexPolynomial", Call("blowupGraph", V("G"), V("W"))),
                Call("comp", Call("complexPolynomial", V("G")), Seq(Par(Seq(D(1), Plus, V("X"))), Caret, Grp(Call("card", V("W"))), Minus, D(1)))),
                "For every finite V,W, nonempty W, and SimpleGraph G on V, T_blowup(x)=T_G((1+x)^card(W)-1) in C[X]. Both polynomials are the literal subset sums defined in TotalDominationSeeds.complexPolynomial. The fibre equivalence, cardinal sum and occupied-support equivalence reduce the left side to a sum over families. For a fixed support A, product-of-sums and the sum of all nonempty fibre subsets give ((1+x)^card(W)-1)^card(A). Summing the supports gives polynomial composition. This is an attributed H-join ingredient from Subramanian and Selvakumar, Filomat 2025, with no new identity or external-resolution credit.", DescribeRole.Theorem),
            Node("seed_blowup_roots", "Power-map pullback of the shrinking seeds", Call("seedBlowupRoots", V("epsilon"), V("k")),
                "For every positive real epsilon and every positive natural k there exist n : N, G : SimpleGraph(Fin n), and r : R with n>=2, 0<1+r<epsilon, complexPolynomial G nonzero, and every vertex of G having a neighbour. For every complex w, (1+w)^k=1+r implies that w is a root of complexPolynomial(blowupGraph G (Fin k)). The blowup polynomial is also nonzero and every blowup vertex has a neighbour; its leading coefficient at its vertex count is one. The same fixed G and r work for all these branches. The proof consumes the new right-hand seed theorem and the known actual-fibre substitution. This is an auxiliary bridge, not WholePlaneDensity: no approximation to an arbitrary target z or unbounded negative seed family is asserted.", DescribeRole.Theorem),
            Node("labelled_seed_blowup_roots", "A single labelled witness for every branch", Call("labelledSeedBlowupRoots", V("epsilon"), V("k")),
                "For every positive real epsilon and positive natural k there exist m : N, H : SimpleGraph (Fin m), and r : R such that m>=2, 0<1+r<epsilon, complexPolynomial H is nonzero, every vertex of H has a neighbour, and for every complex w, (1+w)^k=1+r implies complexPolynomial H has root w. The product vertex type of the independent-fibre graph is reindexed to Fin m through Fintype.equivFin. Actual subsets, their cardinalities, adjacency, every power branch and the same polynomial are preserved. No graph is separately chosen for each branch. This theorem does not assert proximity to an arbitrary complex z.", DescribeRole.Theorem),
            Node("labelled_root_blowup", "A common labelled pullback for every actual root", Call("labelledRootBlowup", V("G"), V("eta"), V("k")),
                "For every n>=2, actual graph G : SimpleGraph (Fin n) without isolates, complex root eta of complexPolynomial G, and positive natural k, there exist m>=2 and an actual isolate-free H : SimpleGraph (Fin m) with nonzero complexPolynomial H. Every complex w satisfying (1+w)^k=1+eta is a root of that same H. The graph is the independent-fibre blowup of G by Fin k, reindexed once to Fin m. Its leading coefficient is one; thus no nonzero assumption on the seed is needed beyond the actual no-isolate graph. This generalizes the live seed pullback to the negative family without a conditional density premise.", DescribeRole.Theorem),
            Node("unbounded_seed_blowup_roots", "The unbounded negative family supplies every branch", Call("unboundedSeedBlowupRoots", V("R"), V("k")),
                "For every real R>2 and every positive natural k there exist m>=2, an actual graph H : SimpleGraph (Fin m), and real r<-R. H has no isolates and its actual complex total-domination polynomial is nonzero. Every complex w with (1+w)^k=1+r is a root of that same H. The proof consumes the unbounded friendship roots and labelled_root_blowup. This does not yet choose r and k jointly to approximate an arbitrary complex target.", DescribeRole.Theorem),
            Paragraph(Text("The full issue 23313 target remains WholePlaneDensity in TotalDominationSeeds. The independent-fibre identity and these power-map branches do not by themselves establish the complete complex density or authorize resolution credit."))), []));

    private static DocumentBlock Node(string selector, string title, Formula formula, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("td-blowup-" + selector.Replace("_", "-").ToLowerInvariant()), DeclarationHandle.Create(Prefix + selector),
            H(title), StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role);
    private static Formula V(string name) => F.Id(name);
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(Seq(Operatorname, Grp(V(name))), [.. args]);
    private static Formula Par(Formula f) => Seq(Open, f, Close);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
}
