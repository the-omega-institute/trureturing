using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Domination;

internal sealed class PenevEvenQKernelRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Combinatorics/Graph/Domination/PenevEvenQKernelRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Certificates/penev2026small");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A bipartite digraph on 29 vertices needs seven centers at radius four, exceeding the six allowed by the proposed bound.",
        H("The even-radius extension of the small q-kernel bound is false"),
        Blocks(
            Describe.Lean(DescribeId.Create("penev-even-radius-claim"),
                DeclarationHandle.Create(Prefix + "claim"), H("The proposed bound for even radii"),
                StatementSource.FromAuthor(Disp(ClaimFormula())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text("The question immediately after Theorem 1.6 of arXiv:2608.00825v1 asks whether the theorem extends to even q. With the printed lower endpoint, this quantifies over every even natural q at least four. The graph ranges over every finite vertex type with a directed adjacency relation. At most one arc occurs in each ordered direction, and opposite arcs can coexist.")),
                    Paragraph(Text("Loopless forbids adjacency from a vertex to itself. Bipartite asks for a Boolean coloring with different colors at the ends of every ambient arc, equivalent to bipartiteness of the underlying simple graph. SourceFree asks for an incoming ambient arc at every vertex. HasOutBranching asks for a subgraph on the entire vertex type whose directed paths from its root are unique, using the Mathlib arborescence structure.")),
                    Paragraph(Text("Independent forbids every ambient arc between members of Q. Covers asks for each vertex to be reached from some member of Q along a directed path in G with distinct vertices and at most q arcs. Length zero is allowed. The multiplicative bound is obtained from the printed fractional bound by multiplying by the positive q + 1."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("penev-even-radius-refutation"),
                DeclarationHandle.Create(Prefix + "result"), H("The radius-four refutation"),
                StatementSource.FromAuthor(Disp(new Formula.Not(F.Id("claim")))),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text("Take the directed cycle 0 → 1 → 2 → 3 → 4 → 5 → 0 and the arc 0 → 6. The three branches are 6 → 7 → 8 → 9 → 10, 6 → 11 → 12 → 13 → 14 → 15 → 16 → 17 → 18 → 19, and 6 → 20 → 21 → 22 → 23 → 24 → 25 → 26 → 27 → 28. Add 15 → 6 and 24 → 6. Every vertex has an in-neighbor. Alternating colors on the cycle and along the branches gives a bipartition, since both return arcs start at odd depth. Deleting 5 → 0 and the two return arcs gives an out-arborescence rooted at 0.")),
                    Paragraph(Text("Two centers on the directed six-cycle are compulsory. It has no incoming arc from outside, and one center reaches at most five cycle vertices within four arcs. If the hub 6 is absent, the demands 10, 14, 19, 23 and 28 have pairwise disjoint predecessor intervals after excluding 6. If the hub is present, the demands 15 and 19 can share only predecessor 15, which independence excludes because of 15 → 6. The demands 24 and 28 similarly cannot share 24. The two pairs require four branch centers in addition to the hub. Both cases force at least five centers outside the cycle.")),
                    Paragraph(Text("The proof checks predecessor membership and disjointness by kernel reduction on the fixed graph. It then counts centers in an arbitrary cover using the disjoint cycle and branch parts. Seven centers imply 5|Q| at least 35, while the source bound on 29 vertices gives 5|Q| at most 34."))),
                DescribeRole.Theorem)),
        []));

    private static Formula ClaimFormula()
    {
        Formula q = F.Id("q"), v = F.Id("V"), g = F.Id("G"), centers = F.Id("Q");
        Formula factor = Add(q, D(1));
        Formula bound = new Formula.Relation(
            new Formula.Binary(factor, FormulaBinaryOperator.Multiply, Call("card", centers)),
            FormulaRelationOperator.LessThanOrEqual, Add(Call("card", v), factor));
        Formula kernel = Bind(FormulaQuantifier.Exists, "Q", Call("Finset", v),
            And(Call("Independent", g, centers), And(Call("Covers", g, q, centers), bound)));
        Formula host = And(Call("Loopless", g), And(Call("Bipartite", g),
            And(Call("SourceFree", g), Call("HasOutBranching", g))));
        Formula family = Seq(Forall, Sp, Open, v, Sp, Colon, Sp, F.Id("Type"), Close, Sp,
            OpenBracket, Call("Fintype", v), CloseBracket, Comma, Sp,
            Bind(FormulaQuantifier.ForAll, "G", Call("Digraph", v), Implies(host, kernel)));
        Formula evenRadius = And(Call("Even", q),
            new Formula.Relation(D(4), FormulaRelationOperator.LessThanOrEqual, q));
        return new Formula.Logic(F.Id("claim"), FormulaLogicOperator.Iff,
            Par(Bind(FormulaQuantifier.ForAll, "q",
                new Formula.NamedConstant(FormulaIdentifier.Create("Nat")),
                Implies(evenRadius, family))));
    }

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
    private static Formula Bind(FormulaQuantifier quantifier, string name, Formula type, Formula body) =>
        new Formula.Bind(quantifier, FormulaIdentifier.Create(name), type, body);
    private static Formula Par(Formula body) => Seq(Open, body, Close);
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);
    private static Formula Implies(Formula hypothesis, Formula conclusion) =>
        new Formula.Logic(Par(hypothesis), FormulaLogicOperator.Implies, Par(conclusion));
}
