using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Walks;

internal sealed class CirculantComponentsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual connected components are generated additive cosets, with explicit even and odd coordinates.", H("Finite walks and exact components of circulants"), Blocks(
            Paragraph(Text("All circulant graphs here keep their original additive vertices. A finite walk accumulates generator differences. Conversely, vertices reachable from zero form an additive subgroup containing the connection set. Translation supplies the native isomorphism from the generated subgroup to every actual component support.")),
            Node("circulant_reachable_iff", "Reachability is generated membership",
                All("u",I("A"),All("v",I("A"),Iff(C("Reachable",C("circulantGraph",I("S")),I("u"),I("v")),C("mem",C("sub",I("v"),I("u")),C("AddSubgroupClosure",I("S")))))),
                "This holds for every additive commutative group A and every connection set S. The forward direction inducts on an actual finite walk. The reverse direction closes reachable vertices under addition and negation, then translates the resulting walk."),
            Node("component_count", "Exact gcd count",
                All("n",C("Nat"),All("a",C("Nat"),All("b",C("Nat"),Imp(And(C("Nonzero",I("n")),C("Divides",I("b"),I("n"))),Eq(C("NatCard",C("Components",C("circulantGraph",C("pairSet",I("a"),I("b"))))),C("gcd",I("a"),I("b"))))))),
                "The vertices are ZMod n, the two natural jumps are cast into that group, and b divides n. The generated subgroup is the cyclic subgroup of gcd(a,b); the existing subgroup-index supplier gives the number of additive cosets."),
            Node("odd_component_number", "Odd generator order",
                All("p",C("Nat"),All("a",C("Nat"),Imp(C("Odd",C("addOrderOf",C("cast",I("a"),C("ZMod",C("mul",D(2),C("add",I("p"),D(2))))))),Eq(C("gcd",C("mul",D(2),C("add",I("p"),D(2))),I("a")),C("mul",D(2),C("gcd",I("a"),C("add",I("p"),D(2)))))))),
                "When the generator order is odd, the antipode is absent from its cyclic subgroup. Adding the order-two antipode doubles that subgroup. The proof constructs product coordinates and derives the exact factor of two in the component count."),
            Node("even_component_number", "Even generator order",
                All("p",C("Nat"),All("a",C("Nat"),Imp(C("Even",C("addOrderOf",C("cast",I("a"),C("ZMod",C("mul",D(2),C("add",I("p"),D(2))))))),Eq(C("gcd",I("a"),C("add",I("p"),D(2))),C("gcd",C("mul",D(2),C("add",I("p"),D(2))),I("a")))))),
                "An even-order cyclic subgroup already contains the unique antipode. Its cyclic coordinates send the antipodal jump to half its order, producing the native Mobius component graph without assuming a decomposition.")), []));
    private static DocumentBlock Node(string name, string title, Formula statement, string explanation) =>
        Describe.Lean(DescribeId.Create(name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Walks/CirculantComponents." + name), H(title),
            StatementSource.FromAuthor(Disp(statement)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(explanation))),
            name is "mobiusIso" or "pentagon_square_complement_iso" ? DescribeRole.Definition : DescribeRole.Theorem);
    private static Formula I(string s) => F.Id(s);
    private static Formula C(string s, params Formula[] a) => a.Length == 0
        ? new Formula.NamedConstant(FormulaIdentifier.Create(s))
        : new Formula.FunctionCall(FormulaIdentifier.Create(s), [.. a]);
    private static Formula All(string n, Formula t, Formula b) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(n), t, b);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, b);
}
