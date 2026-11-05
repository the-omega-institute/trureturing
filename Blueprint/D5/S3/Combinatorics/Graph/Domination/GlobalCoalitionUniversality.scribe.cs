using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Domination;

internal sealed class GlobalCoalitionUniversalityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/Domination/GlobalCoalitionUniversality.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/FiniteGeometry/anholcer2025globalcoalitions");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The edgeless two-vertex graph has no global coalition realization, because every partition block has an actual coalition partner.",
        H("An obstruction to global coalition universality"),
        Blocks(
            Paragraph(Text("Anholcer, Besharati, Mojdeh and Samadzadeh, Global coalitions in graphs, arXiv:2509.15386v4, Definitions 1 and 2 and Section 7 Problem 58, use finite simple undirected graphs of order at least two. Global domination means domination in the graph and its loopless complement on the same vertices. SimpleGraph.IsDominating is the existing domination predicate: every vertex belongs to the set or has a neighbour in it. The complement has an edge precisely between distinct vertices that are not adjacent in the original graph.")),
            Paragraph(Text("The model definitions allow an arbitrary universe u and V : Type u; the braces on V indicate an implicit parameter. The closed question uses V : Type and W : Type, with Finite instances and Nat.card, so every actual finite vertex type in that universe is allowed. Only the counterexample is specifically labelled, by Fin 2. A and B in the graph formula are subtype vertices, and val extracts their actual subsets. No independent-block or maximum-partition condition is imposed.")),
            Node("GloballyDominating", "Global domination", GlobalFormula(),
                "For every graph G and actual subset A, both G.IsDominating A and G-complement.IsDominating A must hold. The identical set A and vertex type V are used in both clauses.", DescribeRole.Definition),
            Node("GlobalCoalition", "Actual global coalitions", CoalitionFormula(),
                "The four requirements are disjointness, failure of global domination for A, failure for B, and global domination of A union B. Ordinary coalition partitions can admit singleton dominating classes; these are not exceptions to the global definition.", DescribeRole.Definition),
            Node("GCPartition", "Global coalition partition records", PartitionFormula(),
                "GCPartition G is a structure with exactly the displayed three fields. blocks is a set of actual subsets of V. Setoid.IsPartition blocks says that the empty set is absent and each vertex belongs to a unique member of blocks; hence its members are nonempty, pairwise disjoint and cover V. partners quantifies over every member A, supplies B in the identical blocks, requires B distinct from A, and requires the complete GlobalCoalition G A B predicate. Individual non-domination follows from that predicate.", DescribeRole.Definition),
            Node("blocks", "The actual blocks", FieldFormula("blocks"),
                "The blocks field has type Set (Set V). The vertex type and graph parameters are implicit, followed by the explicit record parameter; its elements are the actual subsets, rather than labels or an independently chosen adjacency relation.", DescribeRole.Definition),
            Node("isPartition", "The partition field", FieldFormula("isPartition"),
                "For every pi : GCPartition G, the isPartition field proves Setoid.IsPartition pi.blocks. This retains all nonempty-block, disjointness and cover requirements of a vertex partition.", DescribeRole.Theorem),
            Node("partners", "The partner field", FieldFormula("partners"),
                "For every pi and every actual A in pi.blocks, this field supplies an actual B in pi.blocks with B unequal to A and GlobalCoalition G A B. It has no exceptional singleton case.", DescribeRole.Theorem),
            Node("globalCoalitionGraph", "The native graph on partition blocks", GraphFormula(),
                "The result has type SimpleGraph {A : Set V // A belongs to pi.blocks}. Its adjacency is exactly the displayed full coalition predicate. Symmetry exchanges A and B, uses symmetric disjointness and commutativity of union. A loop would make A union A globally dominating while A is not; union self gives a contradiction. Thus the native symmetric, loopless graph uses the actual coalition relation.", DescribeRole.Definition),
            Node("claim", "The complete universal realizability question", IffFormula(X("claim"), ClaimBody()),
                "Problem 58 asks: Is every graph realisable as a global coalition graph? In full, for every finite actual target type V of order at least two and every simple graph H on V, there exist an arbitrary finite actual host type W of order at least two, a simple graph G on W, an actual global coalition partition pi of G, and an ordinary graph isomorphism from its global coalition graph to H. Finite V is an anonymous instance binder. The existential Finite W proof is anonymous; G, its order bound and pi all belong to that same W. The earlier v1 Section 6 Problem 4 asks the same realizability question without the order restrictions; it is a separate statement boundary for the same question.", DescribeRole.Definition),
            Node("result", "Negation of the whole universal assertion", NotFormula(P(ClaimBody())),
                "The theorem states not claim, with every target, host and partition quantifier as above. Use the edgeless graph on Fin 2, which has order two. For any proposed host G and any actual pi, an isomorphism to this target has a preimage A of vertex zero. The partners field supplies B in the same partition and an actual global coalition between A and B, hence an actual adjacent pair in globalCoalitionGraph G pi. The isomorphism transports this adjacency to the edgeless target, a contradiction. The private lemma no_edgeless_realization supplies this argument for arbitrary universe-polymorphic hosts and arbitrary nonempty edgeless targets, and result applies it to Fin 2. This excludes every host and eligible partition for one legal target, rather than only a selected host. The same argument also excludes that target under the unrestricted v1 question. Whether every isolate-free target is globally realizable remains unsettled here; no classification or realization construction follows. No conclusion about the paper's other results or literature priority is asserted.", DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("anholcer-2025-global-coalition-universality"),
                    ResolutionKind.Refuted))),
        []));

    private static DocumentBlock Node(string selector, string title, Formula formula, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) => Describe.Lean(DescribeId.Create("gc-" + selector.Replace(".", "-").ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + selector), H(title), StatementSource.FromAuthor(Disp(formula)),
            selector == "result" ? AssessedProvenance.FromRepo(Source) : AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula X(string name) => F.Id(name);
    private static Formula P(Formula value) => Seq(Open, value, Close);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(X(name))), [.. args]);
    private static Formula QualifiedCall(string owner, string name, params Formula[] args) =>
        new Formula.Apply(Field(X(owner), name), [.. args]);
    private static Formula Field(Formula value, string name) => Seq(value, Dot, Operatorname, Grp(X(name)));
    private static Formula TypeU => Seq(X("Type"), Underscore, Grp(X("u")));
    private static Formula SetOf(Formula type) => Call("Set", type);
    private static Formula Graph(Formula type) => Call("SimpleGraph", type);
    private static Formula Typed(Formula value, Formula type) => Seq(value, Sp, Colon, Sp, type);
    private static Formula All(string name, Formula type, Formula body, bool implicitBinder = false) =>
        Seq(Forall, Sp, implicitBinder ? Seq(OpenBrace, Typed(X(name), type), CloseBrace) : P(Typed(X(name), type)), Comma, Sp, body);
    private static Formula Some(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, P(Typed(X(name), type)), Comma, Sp, body);
    private static Formula Logic(Formula a, FormulaLogicOperator op, Formula b) => new Formula.Logic(P(a), op, P(b));
    private static Formula And(Formula a, Formula b) => Logic(a, FormulaLogicOperator.And, b);
    private static Formula Imp(Formula a, Formula b) => Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula IffFormula(Formula a, Formula b) => Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula NotFormula(Formula a) => Seq(Neg, Sp, P(a));
    private static Formula Member(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.MemberOf, b);
    private static Formula LeqFormula(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula OverGraph(Formula body) => All("V", TypeU, All("G", Graph(X("V")), body), true);
    private static Formula GD(Formula g, Formula a) => Call("GloballyDominating", g, a);
    private static Formula Coalition(Formula g, Formula a, Formula b) => Call("GlobalCoalition", g, a, b);
    private static Formula Parts(Formula pi) => Field(pi, "blocks");
    private static Formula PartnerBody(Formula blocks) => All("A", SetOf(X("V")), Imp(Member(X("A"), blocks),
        Some("B", SetOf(X("V")), And(Member(X("B"), blocks), And(
            new Formula.Relation(X("B"), FormulaRelationOperator.NotEqual, X("A")), Coalition(X("G"), X("A"), X("B")))))));

    private static Formula GlobalFormula() => OverGraph(All("A", SetOf(X("V")), IffFormula(GD(X("G"), X("A")),
        And(Call("IsDominating", X("G"), X("A")), Call("IsDominating", Seq(X("G"), Caret, Grp(X("c"))), X("A"))))));

    private static Formula CoalitionFormula() => OverGraph(All("A", SetOf(X("V")), All("B", SetOf(X("V")),
        IffFormula(Coalition(X("G"), X("A"), X("B")), And(Call("Disjoint", X("A"), X("B")),
            And(NotFormula(GD(X("G"), X("A"))), And(NotFormula(GD(X("G"), X("B"))),
                GD(X("G"), P(Seq(X("A"), Sp, Cup, Sp, X("B")))))))))));

    private static Formula PartitionFormula() => OverGraph(Seq(Call("GCPartition", X("G")), Sp, Colon, Eq, Sp,
        Operatorname, Grp(X("structure")), Sp,
        P(Typed(X("blocks"), SetOf(SetOf(X("V"))))), Sp,
        P(Typed(X("isPartition"), QualifiedCall("Setoid", "IsPartition", X("blocks")))), Sp,
        P(Typed(X("partners"), PartnerBody(X("blocks"))))));

    private static Formula FieldFormula(string selector)
    {
        Formula pi = X("pi");
        Formula type = selector switch
        {
            "blocks" => SetOf(SetOf(X("V"))),
            "isPartition" => QualifiedCall("Setoid", "IsPartition", Parts(pi)),
            "partners" => PartnerBody(Parts(pi)),
            _ => throw new System.ArgumentOutOfRangeException(nameof(selector))
        };
        return All("V", TypeU, All("G", Graph(X("V")), All("pi", Call("GCPartition", X("G")), Typed(Field(pi, selector), type)), true), true);
    }

    private static Formula BlockType(Formula pi) => Seq(OpenBrace, Typed(X("C"), SetOf(X("V"))), Sp,
        Mid, Sp, Member(X("C"), Parts(pi)), CloseBrace);

    private static Formula GraphFormula()
    {
        Formula pi = X("pi"), a = X("A"), b = X("B");
        return OverGraph(All("pi", Call("GCPartition", X("G")), All("A", BlockType(pi), All("B", BlockType(pi),
            IffFormula(Call("Adj", Call("globalCoalitionGraph", X("G"), pi), a, b),
                Coalition(X("G"), Field(a, "val"), Field(b, "val")))))));
    }

    private static Formula ClaimBody()
    {
        Formula v = X("V"), w = X("W"), g = X("G"), pi = X("pi");
        Formula iso = QualifiedCall("SimpleGraph", "Iso", Call("globalCoalitionGraph", g, pi), X("H"));
        Formula host = Some("W", X("Type"), Seq(Exists, Sp,
            P(Typed(Underscore, Call("Finite", w))), Comma, Sp, Some("G", Graph(w),
                And(LeqFormula(D(2), QualifiedCall("Nat", "card", w)), Some("pi", Call("GCPartition", g), Call("Nonempty", P(iso)))))));
        return All("V", X("Type"), Seq(Forall, Sp, OpenBracket, Call("Finite", v), CloseBracket, Comma, Sp,
            Imp(LeqFormula(D(2), QualifiedCall("Nat", "card", v)), All("H", Graph(v), host))));
    }
}
