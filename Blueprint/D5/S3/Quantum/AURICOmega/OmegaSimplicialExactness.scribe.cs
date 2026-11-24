using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.AURICOmega;

internal sealed class OmegaSimplicialExactnessDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/AURICOmega/OmegaSimplicialExactness";

    public DocumentDefinition Create()
    {
        Formula f = F.Id("f"), edge = F.Id("e"), face = F.Id("F"), chain = F.Id("p");
        Formula b = F.Id("b"), x = F.Id("x"), y = F.Id("y"), z = F.Id("z"), w = F.Id("w");
        Formula zero = D(0);
        Formula closed = All(Equal(Call("d2", face, x, y, z, w), zero), Vertices("x", "y", "z", "w"));
        Formula exact = new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create("e"), Cochains("C1"),
            All(Equal(Call("d1", edge, x, y, z), Call("F", x, y, z)), Vertices("x", "y", "z")));

        return DocumentDefinition.Create(ScribeNode.Create(
            "Finite-chain integration and simplicial coboundaries for Chapter 32, §32.7.3.2, in the zero-axiom architecture of §32.8. "
                + "The vertex domain V is an arbitrary sort and Cj consists of A-valued functions on all ordered tuples of j + 1 vertices, with repetitions allowed. "
                + "The operators d0, d1 and d2 take the alternating sum of omitted-vertex faces. The cone operators H1, H2 and H3 prepend a chosen vertex. "
                + "Sums, differences and zero are those of the coefficient operations G under their additive abelian group laws.",
            H("Finite-chain integration and simplicial cone exactness"),
            Blocks(
                Law("endpoint-chain-integral", "sum_d0", "An exact edge difference integrates to the endpoint difference",
                    InGroup(Equal(Call("sum", chain, Call("d0", f)), Sub(Call("f", y), Call("f", x))),
                        [Bound("f", Cochains("C0")), .. Vertices("x", "y"), Bound("p", Chains(x, y))]),
                    "A chain p from x to y is a finite sequence of oriented edges, possibly empty when the endpoints agree. Each intermediate vertex contributes its potential once with each sign."),
                Law("closed-chain-integral", "sum_d0_loop", "An exact edge difference has zero sum around a loop",
                    InGroup(Equal(Call("sum", chain, Call("d0", f)), zero),
                        [Bound("f", Cochains("C0")), .. Vertices("b"), Bound("p", Chains(b, b))]),
                    "When the chain begins and ends at b, its two endpoint values cancel."),
                Law("vertex-coboundary-nilpotency", "d1_d0", "Two coboundaries of a vertex potential vanish",
                    InGroup(Equal(Call("d1", Call("d0", f), x, y, z), zero),
                        [Bound("f", Cochains("C0")), .. Vertices("x", "y", "z")]),
                    "In the alternating sum of the three edge differences, each vertex potential occurs with opposing signs."),
                Law("edge-coboundary-nilpotency", "d2_d1", "Two coboundaries of an edge cochain vanish",
                    InGroup(Equal(Call("d2", Call("d1", edge), x, y, z, w), zero),
                        [Bound("e", Cochains("C1")), .. Vertices("x", "y", "z", "w")]),
                    "Each edge appears with opposing signs in the four triangle faces of the ordered quadruple."),
                Law("degree-one-cone-identity", "d0_H1_add_H2_d1", "The cone identity on edges",
                    InGroup(Equal(Add(Call("d0", Call("H1", b, edge), x, y),
                            Call("H2", b, Call("d1", edge), x, y)), Call("e", x, y)),
                        [.. Vertices("b"), Bound("e", Cochains("C1")), .. Vertices("x", "y")]),
                    "Prepending b gives two terms on the cone edges. The two terms cancel against the coboundary of the vertex cochain given by H1."),
                Law("degree-two-cone-identity", "d1_H2_add_H3_d2", "The cone identity on triangles",
                    InGroup(Equal(Add(Call("d1", Call("H2", b, face), x, y, z),
                            Call("H3", b, Call("d2", face), x, y, z)), Call("F", x, y, z)),
                        [.. Vertices("b"), Bound("F", Cochains("C2")), .. Vertices("x", "y", "z")]),
                    "The three faces containing the cone vertex cancel when the two summands are added. The face on x, y and z remains."),
                Law("explicit-cone-primitive", "d1_H2_of_d2_eq_zero", "A closed triangle cochain has the chosen cone primitive",
                    InGroup(new Formula.Logic(closed, FormulaLogicOperator.Implies,
                            All(Equal(Call("d1", Call("H2", b, face), x, y, z), Call("F", x, y, z)),
                                Vertices("x", "y", "z"))),
                        [.. Vertices("b"), Bound("F", Cochains("C2"))]),
                    "For a fixed vertex b, the primitive on the edge from x to y is F(b, x, y). Closedness removes the H3 term from the degree-two cone identity."),
                Law("degree-two-exactness", "d2_eq_zero_iff", "A triangle cochain is closed exactly when it is an edge coboundary",
                    InGroup(new Formula.Logic(closed, FormulaLogicOperator.Iff, exact),
                        [.. Vertices("b"), Bound("F", Cochains("C2"))]),
                    "The forward implication uses the primitive H2 at the chosen vertex b. The reverse implication uses vanishing of two successive coboundaries of an edge cochain."))));
    }

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula Cochains(string degree) => Call(degree, F.Id("V"), F.Id("A"));

    private static Formula Chains(Formula first, Formula last) =>
        Call("VertexChain", F.Id("V"), first, last);

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula.BoundVariable[] Vertices(params string[] names) =>
        [.. names.Select(name => Bound(name, F.Id("V")))];

    private static Formula All(Formula body, Formula.BoundVariable[] variables) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables], body);

    private static Formula InGroup(Formula body, Formula.BoundVariable[] variables) =>
        Disp(All(new Formula.Logic(Call("Laws", F.Id("G")), FormulaLogicOperator.Implies, body),
            [Bound("V", F.Id("Sort")), Bound("A", F.Id("Type")),
                Bound("G", Call("AddCommGroup", F.Id("A"))), .. variables]));

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);

    private static Formula Sub(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);

    private static DocumentBlock.Describe Law(string id, string selector, string title, Formula statement, string commentary) =>
        Describe.Lean(
            DescribeId.Create(id),
            DeclarationHandle.Create($"{Module}.{selector}"),
            H(title),
            StatementSource.FromAuthor(statement),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(commentary))),
            DescribeRole.Theorem);
}
