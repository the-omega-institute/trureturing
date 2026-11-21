using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Matroids;

internal sealed class LaoTransversalUniformMinorDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Combinatorics/Matroids/LaoTransversalUniformMinor";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/FiniteGeometry/lao2026dynamicstransversal");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Full neighborhoods and pair matchings determine which four-element sets support a uniform minor in a bipartite presentation.",
        H("A graph criterion for a four-element uniform minor"),
        Blocks(
            Definition("Matchable", "Matchable left sets",
                "A left set I is matchable if some injection from its vertex subtype to the right type takes every vertex to a neighbor."),
            Definition("transversal", "The transversal matroid",
                "The matroid on the left type is built from the finite matchable sets. Augmentation follows by increasing agreement between two matchings on their common domain until the larger matching supplies an additional left vertex."),
            Theorem("transversal_ground", "The whole left ground", GroundStatement(),
                "Every left vertex is in the ground, including isolated vertices."),
            Theorem("transversal_indep_iff", "Independence as matchability", IndependenceStatement(),
                "For arbitrary left and right types, a finite left set is independent exactly when it is matchable. This covers every subset when the left type is finite, including the empty subset, and permits an empty right type."),
            Definition("neighborhood", "Full right neighborhood",
                "The neighborhood of I contains every right vertex adjacent to any vertex of I."),
            Definition("uniform24", "The rank-two uniform matroid on four points",
                "Its ground is all of Fin 4. Its independent sets are exactly the subsets of cardinality at most two."),
            Describe.Lean(
                DescribeId.Create("has-uniform24-minor-iff"),
                DeclarationHandle.Create(Module + ".has_uniform24_minor_iff"),
                H("Uniform minors on a specified four-element ground"),
                StatementSource.FromAuthor(Disp(MinorStatement())),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text("The relation A runs from the designated left ground L to the presentation indices R. Both types are arbitrary finite types. Fix any four-element left set X. The native matroid minor N must have ground exactly X and a ground equivalence to all of Fin 4 whose relabeling equals the rank-two uniform matroid.")),
                    Paragraph(Text("The graph condition chooses a left set C disjoint from the fixed X. The full right neighborhood B of their union must have size |C| + 2. Each two-element subset P of X has an edge-respecting bijection from C ∪ P onto that same B. The bijection may depend on P.")),
                    Paragraph(Text("Normalize the minor to a contraction and deletion and choose a basis K of the contracted set. The four surviving vertices are X, and adjoining any pair from X to K gives an independent set. Augmentation rules out a larger matchable subset of K ∪ X. Adding one universal dummy right vertex still falls short of a matching of K ∪ X, so Hall's theorem finds a left subset whose full neighborhood falls short by at least two. This subset must contain all of X. If it omitted a surviving vertex, restricting a suitable pair matching would leave at most one left vertex unmatched. Remove X from the deficient subset to obtain C. The restricted pair matchings give the opposite bound on the size of B, forcing equality and hence bijectivity.")),
                    Paragraph(Text("Conversely, contract C and delete the remaining vertices outside X. Extending a subset of X of size at most two to a pair proves its independence after contraction. A larger subset cannot be independent because its required matching would have too many vertices for B. This describes every independent set of the minor and yields the relabeling to Fin 4.")),
                    Paragraph(Text("Lao's Question 7.0.2 asks whether any such minor exists. Any minor relabeled to the uniform matroid on Fin 4 has a four-element ground, so applying the equivalence to that ground gives the graph condition. A graph certificate for any four-element X gives the required minor by the reverse implication."))),
                DescribeRole.Theorem))));

    private static DocumentBlock Definition(string name, string title, string body) =>
        Describe.Lean(Id(name), DeclarationHandle.Create(Module + "." + name), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(body))), DescribeRole.Definition);

    private static DocumentBlock Theorem(string name, string title, Formula statement, string body) =>
        Describe.Lean(Id(name), DeclarationHandle.Create(Module + "." + name), H(title),
            StatementSource.FromAuthor(Disp(statement)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(body))), DescribeRole.Theorem);

    private static DescribeId Id(string name) =>
        DescribeId.Create(name.Replace('_', '-').ToLowerInvariant());

    private static Formula GroundStatement() => GraphParameters(
        Equal(Call("ground", Call("transversal", V("A"))), V("univ")));

    private static Formula IndependenceStatement() => GraphParameters(
        Bind(Forall, "I", SetOf("L"),
            Logic(Call("Finite", V("I")), FormulaLogicOperator.Implies,
                Logic(Call("Indep", Call("transversal", V("A")), V("I")),
                    FormulaLogicOperator.Iff, Call("Matchable", V("A"), V("I"))))));

    private static Formula MinorStatement()
    {
        var ground = Call("ground", V("N"));
        var finFour = Call("Fin", D(4));
        var targetGround = Parenthesized(Seq(V("univ"), Sp, Colon, Sp, Call("Set", finFour)));
        var relabel = Bind(Exists, "e", Call("Equiv", Subtype(ground), Subtype(targetGround)),
            Equal(Call("mapSetEquiv", V("N"), V("e")), V("uniform24")));
        var minor = Bind(Exists, "N", Call("Matroid", V("L")),
            And(Call("IsMinor", V("N"), Call("transversal", V("A"))),
                And(Equal(ground, V("X")), relabel)));

        var pairDomain = Subtype(Union("C", "P"));
        var bijection = Bind(Exists, "f", Arrow(pairDomain, Subtype(V("B"))),
            And(Call("Bijective", V("f")),
                Bind(Forall, "x", pairDomain,
                    Call("A", V("x"), Call("f", V("x"))))));
        var pairMatchings = Bind(Forall, "P", SetOf("L"),
            Logic(new Formula.Relation(V("P"), FormulaRelationOperator.SubsetOf, V("X")),
                FormulaLogicOperator.Implies,
                Logic(Equal(Card("P"), D(2)), FormulaLogicOperator.Implies, bijection)));
        var neighborhood = Seq(V("let"), Sp, V("B"), Sp, Colon, Eq, Sp,
            Call("neighborhood", V("A"), Union("C", "X")), Semi, Sp,
            And(Equal(Card("B"), Seq(Card("C"), Sp, Plus, Sp, D(2))), pairMatchings));
        var certificate = Bind(Exists, "C", SetOf("L"),
            And(Call("Disjoint", V("C"), V("X")), neighborhood));
        var fixedGround = Bind(Forall, "X", SetOf("L"),
            Logic(Equal(Card("X"), D(4)), FormulaLogicOperator.Implies,
                Logic(minor, FormulaLogicOperator.Iff, certificate)));
        return VertexTypes(Finite("L", Finite("R",
            EdgeRelation(fixedGround))));
    }

    private static Formula GraphParameters(Formula body) => VertexTypes(EdgeRelation(body));

    private static Formula VertexTypes(Formula body) =>
        Bind(Forall, "L", new Formula.Subscript(V("Type"), V("u")),
            Bind(Forall, "R", new Formula.Subscript(V("Type"), V("v")), body));

    private static Formula EdgeRelation(Formula body) =>
        Bind(Forall, "A", Arrow(V("L"), Arrow(V("R"), V("Prop"))), body);

    private static Formula Finite(string type, Formula body) =>
        Seq(OpenBracket, Call("Finite", V(type)), CloseBracket, Sp, body);

    private static Formula Bind(Formula quantifier, string name, Formula domain, Formula body) =>
        Seq(quantifier, Sp, Parenthesized(Seq(V(name), Sp, Colon, Sp, domain)), Comma, Sp, body);

    private static Formula Logic(Formula left, FormulaLogicOperator op, Formula right) =>
        new Formula.Logic(Parenthesized(left), op, Parenthesized(right));

    private static Formula And(Formula left, Formula right) => Logic(left, FormulaLogicOperator.And, right);
    private static Formula V(string name) => F.Id(name);
    private static Formula Call(string name, params Formula[] arguments) => new Formula.Apply(V(name), [.. arguments]);
    private static Formula Arrow(Formula domain, Formula codomain) => new Formula.TypeArrow(domain, codomain);
    private static Formula SetOf(string type) => Call("Set", V(type));
    private static Formula Subtype(Formula set) => Call("Subtype", set);
    private static Formula Card(string name) => Call("ncard", V(name));
    private static Formula Union(string left, string right) => Parenthesized(Seq(V(left), Sp, Cup, Sp, V(right)));
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
}
