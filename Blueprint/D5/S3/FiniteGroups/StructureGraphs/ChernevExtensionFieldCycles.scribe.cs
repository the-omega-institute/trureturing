using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.StructureGraphs;

internal sealed class ChernevExtensionFieldCyclesDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/FiniteGroups/StructureGraphs/ChernevExtensionFieldCycles.";
    private const string Hypothesis =
        "The structure graph of a Galois field of extension degree > 1 different from GF (4) contains a cycle of length > 1.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/FiniteGroups/chernevchernev2026structuregraphs");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finite field of order p to the n with p prime, n greater than one and order different from four has a nontrivial directed structure-graph cycle.",
        H("Directed structure-graph cycles over finite extension fields"),
        Blocks(
            Node("phi", "The sum-and-product successor", SuccessorFormula(),
                "Definition 3.1 directs an edge from (a, b) to (a + b, ab). The multiplication keeps the order of the two inputs.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("structureGraph", "The directed structure graph", GraphFormula(),
                "Definition 3.1 uses ordered pairs as vertices. The adjacency relation permits self-loops.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("IsDirectedCycle", "A closed directed cycle", CycleFormula(),
                "The indices range from zero to r − 1. Injectivity makes the vertices distinct, and reducing the successor modulo r includes the edge from the last vertex to the first.",
                DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("claim", "Chernev–Chernev Hypothesis 6.1", ClaimFormula(),
                "Hypothesis 6.1, p. 8, reads “" + Hypothesis + "” The field K is arbitrary. Its cardinality is p to the n, where p is prime and n is the degree over the prime field.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "The universal cycle-existence theorem", ClaimFormula(),
                "Two steps from (−1, x) give (−1, x − x²) in every characteristic. A nonzero periodic point of x ↦ x − x² gives a nonfixed periodic vertex. "
                + "Listing its orbit through one minimal period yields distinct vertices and the closing edge. "
                + "In an odd-degree extension, a point whose image lies in the prime field has minimal polynomial of degree at most two. "
                + "Its degree divides the extension degree and hence is one. The complement of the prime field is therefore invariant, finite and nonempty. "
                + "In odd characteristic and even degree the quadratic subfield contains a square root of −1, which gives a four-cycle. "
                + "In characteristic two the degree is greater than two. An odd prime divisor of the degree gives an odd-degree subfield, and divisibility by four gives a subfield of order sixteen. "
                + "In that subfield a root of X⁴ + X + 1 supplies polynomial coordinates for an explicit eight-cycle. "
                + "Field embeddings preserve the successor and distinctness. The finite-field isomorphism given by equality of cardinalities transports the cycle to K.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("chernev-chernev-2026-structure-graphs-hypothesis-6-1"), ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create("chernev-extension-field-cycles-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(Disp(formula)),
            provenance, Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. arguments]);
    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Ex(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Instance(string name, Formula type, Formula body) =>
        Seq(OpenBracket, Call(name, type), CloseBracket, Comma, Sp, body);
    private static Formula EqTo(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Less(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula Par(Formula formula) => Seq(Open, formula, Close);
    private static Formula And(Formula left, Formula right) => Seq(left, Sp, Land, Sp, right);
    private static Formula If(Formula premise, Formula conclusion) => Seq(premise, Sp, Rightarrow, Sp, conclusion);
    private static Formula Nat() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula AnyType() => Seq(F.Id("Type"), Star);
    private static Formula Pair(Formula first, Formula second) => Par(Seq(first, Comma, Sp, second));
    private static Formula PairType(Formula type) => Seq(type, Sp, Times, Sp, type);
    private static Formula CycleIndex(Formula length) => Call("Fin", length);
    private static Formula ListType(Formula length, Formula vertex) => Par(Seq(CycleIndex(length), Sp, To, Sp, vertex));

    private static Formula SuccessorFormula()
    {
        Formula ring = F.Id("R"), a = F.Id("a"), b = F.Id("b");
        return All("R", AnyType(), Instance("Ring", ring,
            All("a", ring, All("b", ring, EqTo(Call("phi", Pair(a, b)),
                Pair(Seq(a, Plus, b), Seq(a, Sp, Cdot, Sp, b)))))));
    }

    private static Formula GraphFormula()
    {
        Formula ring = F.Id("R"), v = F.Id("v"), w = F.Id("w");
        return All("R", AnyType(), Instance("Ring", ring,
            All("v", PairType(ring), All("w", PairType(ring),
                Seq(Call("Adj", Call("structureGraph", ring), v, w), Sp, Leftrightarrow, Sp,
                    EqTo(Call("phi", v), w))))));
    }

    private static Formula CycleFormula()
    {
        Formula vertex = F.Id("V"), graph = F.Id("G"), r = F.Id("r"), v = F.Id("v");
        Formula i = F.Id("i"), j = F.Id("j");
        var successor = Call("mod", Seq(Call("val", i), Plus, D(1)), r);
        var edges = All("i", CycleIndex(r), All("j", CycleIndex(r),
            If(EqTo(Call("val", j), successor), Call("Adj", graph, Apply(v, i), Apply(v, j)))));
        return All("V", AnyType(), All("G", Call("Digraph", vertex),
            All("r", Nat(), All("v", ListType(r, vertex),
                Seq(Call("IsDirectedCycle", graph, r, v), Sp, Leftrightarrow, Sp,
                    Par(And(Less(D(0), r), And(Call("Injective", v), Par(edges)))))))));
    }

    private static Formula ClaimFormula()
    {
        Formula field = F.Id("K"), p = F.Id("p"), n = F.Id("n"), r = F.Id("r"), v = F.Id("v");
        var card = Call("card", field);
        var cycle = Ex("r", Nat(), Ex("v", ListType(r, PairType(field)),
            And(Less(D(1), r), Call("IsDirectedCycle", Call("structureGraph", field), r, v))));
        var premises = If(Call("Prime", p), If(Less(D(1), n),
            If(EqTo(card, new Formula.Power(p, n)),
                If(new Formula.Relation(card, FormulaRelationOperator.NotEqual, D(4)), cycle))));
        return All("K", F.Id("Type"), Instance("Field", field, Instance("Fintype", field,
            All("p", Nat(), All("n", Nat(), premises)))));
    }
}
