using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.StarForming.Foundations;

internal sealed class InvariantsDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Combinatorics/Graph/StarForming/Foundations/Invariants.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite graph independence and upper star formation", H("Finite graph invariants"),
        Blocks(Paragraph(Text("These definitions and local characterizations apply to arbitrary finite simple graphs. A star is a subgraph and need not be induced. Inclusion-minimality is distinct from minimum cardinality. The two-independent neighbor characterization also applies to every finite simple graph.")),
            Node("IsKIndependent", "Selected induced degree is less than k",
                Disp(Iff(Call("IsKIndependent", G, K, I),
                    All("v", V, Imp(Member(v, I), Lt(Degree(I, v), K))))),
                "Each selected vertex has fewer than k selected neighbours. For k equal "
                    + "to two, the induced graph is a disjoint union of edges and isolated vertices.",
                DescribeRole.Definition),
            Node("beta", "Maximum k-independent cardinality",
                Disp(Eq(Call("beta", G, K), Maximum("I", Independent(I)))),
                "Take the maximum cardinality over the k-independent subsets of V. "
                    + "The finite supremum has value zero if the family is empty.",
                DescribeRole.Definition),
            Node("IsStarForming", "A star containing each outside vertex",
                StarFormula(),
                "For every vertex outside S, the graph on S together with that vertex "
                    + "contains a star with k leaves containing the vertex. The centre is "
                    + "distinct from all leaves. Extra edges between leaves are allowed: "
                    + "the star is a subgraph, with no induced-subgraph requirement.",
                DescribeRole.Definition),
            Node("IsMinimalStarForming", "Inclusion-minimal star formation",
                Disp(Iff(Call("IsMinimalStarForming", G, K, S), And(Star(S),
                    All("T", Sets, Imp(Call("ProperSubset", T, S), new Formula.Not(Star(T))))))),
                "The set is star-forming and no proper subset is star-forming. "
                    + "This is inclusion-minimality rather than minimum cardinality.",
                DescribeRole.Definition),
            Node("SF", "Upper k-star-forming number",
                Disp(Eq(Call("SF", G, K), Maximum("S", Call("IsMinimalStarForming", G, K, S)))),
                "Take the maximum cardinality among all inclusion-minimal k-star-forming "
                    + "sets. The finite supremum has value zero if the family is empty.",
                DescribeRole.Definition),
            Node("LocalTwo", "Two local alternatives",
                Disp(Iff(Call("LocalTwo", G, S), LocalFormula())),
                "Every outside vertex either has two neighbours in S, or has a neighbour "
                    + "in S that itself has a neighbour in S. In the second alternative "
                    + "this further neighbour cannot be the outside vertex.",
                DescribeRole.Definition),
            Node("starForming_two_iff", "The local criterion equals the star definition",
                Disp(All("V", F.Id("Type"), All("G", Call("SimpleGraph", V),
                    All("S", Sets, Iff(Call("IsStarForming", G, D(2), S), Call("LocalTwo", G, S)))))),
                "In a two-leaf star, the outside vertex is either the centre, giving "
                    + "two neighbours in S, or a leaf, giving a centre and another leaf "
                    + "in S. Conversely, two selected neighbours give a star centred at "
                    + "the outside vertex; a selected neighbour with its own selected "
                    + "neighbour gives a star centred at that selected neighbour. The "
                    + "argument works on any vertex type with decidable equality and adjacency.",
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("dissociation-neighbor-uniqueness"),
                DeclarationHandle.Create(Prefix + "independent_iff"),
                H("The exact selected-neighbor condition"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/GraphInvariants/zhang2026doublegrafting")),
                Blocks(Paragraph(Text("For every finite simple graph with decidable equality and "
                    + "adjacency, a finite set is two-independent exactly when any two selected "
                    + "neighbors of a selected vertex are equal. This is the original local "
                    + "grafting proof's characterization, also used by canonical composition "
                    + "and cover arguments. No grafting or nonempty hypothesis is needed."))),
                DescribeRole.Theorem))));


    private static Formula G => F.Id("G");
    private static Formula V => F.Id("V");
    private static Formula K => F.Id("k");
    private static Formula S => F.Id("S");
    private static Formula T => F.Id("T");
    private static Formula I => F.Id("I");
    private static Formula v => F.Id("v");
    private static Formula Sets => Call("Finset", V);
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Ex(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Eq(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Lt(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Le(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Iff(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Or(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Or, b);
    private static Formula Member(Formula a, Formula b) => Call("Member", a, b);
    private static Formula Degree(Formula s, Formula x) => Call("d", G, s, x);
    private static Formula Star(Formula s) => Call("IsStarForming", G, K, s);
    private static Formula Independent(Formula s) => Call("IsKIndependent", G, K, s);
    private static Formula Maximum(string name, Formula condition) => Call("supCard",
        Seq(OpenBrace, F.Id(name), Sp, InMacro, Sp,
            Call("powerset", Call("univ", V)), Sp, Mid, Sp, condition, CloseBrace));

    private static Formula StarFormula()
    {
        var c = F.Id("c"); var l = F.Id("L"); var leaf = F.Id("ell");
        var copy = And(Eq(Call("card", l), K),
            And(new Formula.Not(Member(c, l)),
            And(Call("Subset", Call("insert", c, l), Call("insert", v, S)),
            And(All("ell", V, Imp(Member(leaf, l), Call("Adj", G, c, leaf))),
                Member(v, Call("insert", c, l))))));
        return Disp(Iff(Star(S), All("v", V, Imp(new Formula.Not(Member(v, S)),
            Ex("c", V, Ex("L", Sets, copy))))));
    }

    private static Formula LocalFormula()
    {
        var u = F.Id("u");
        return All("v", V, Imp(new Formula.Not(Member(v, S)),
            Or(Le(D(2), Degree(S, v)), Ex("u", V,
                And(Member(u, S), And(Call("Adj", G, v, u), Le(D(1), Degree(S, u))))))));
    }

    private static DocumentBlock Node(string selector, string title, Formula formula,
        string prose, DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(selector == "starForming_two_iff"
                ? "sf2-star-forming-two-iff" : "sf2-" + selector.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + selector), H(title),
            StatementSource.FromAuthor(formula), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
