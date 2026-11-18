using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.ZeroForcing;

internal sealed class ConnectedForcingCrossingRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/ZeroForcing/ConnectedForcingCrossingRefutation.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Certificates/mukherjeeray2026connected");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The four-vertex path followed by the four-vertex star refutes the fixed ordered crossing in Problem 5.3: their size-one connected zero forcing counts are two and zero.",
        H("The ordered connected forcing crossing is false"),
        Blocks(
            Def("connected", "connectedForcing", "Initial connectivity and ordinary forcing", ConnectedFormula(),
                "The induced graph on the initial subset must be connected, and its ordinary Black closure must contain every vertex. Connectivity of later colored sets is not an additional rule. Black.force uses a colored source, an adjacent target and colored other neighbors; a derivation targeting an already colored vertex changes no closure membership. The existing chronological equivalence in ContingentThreshold explains the correspondence with a legal sequence of unique-white-neighbor forces."),
            Def("coefficient", "coefficient", "Actual vertex-subset coefficients", CoefficientFormula(),
                "Enumerate every finite vertex subset once, retain exactly the subsets of size i satisfying connectedForcing, and take their cardinality. This is a subset count rather than a minimum forcing number, coefficient oracle or hardcoded polynomial. Fintype supplies only the finite carrier enumeration; the predicate retains its mathematical semantics."),
            Def("leaves", "leafCount", "Degree-one vertices", LeavesFormula(),
                "Count the vertices whose neighbor subtype has cardinality one. For a finite simple graph this is exactly its number of degree-one vertices, including orders where that number is zero. The parameters p and q in the assertion are these actual counts, with no ordering or lower-bound restriction."),
            Def("claim", "claim", "Problem 5.3 with fixed order", ClaimFormula(),
                "Mukherjee and Ray ask: Given two trees T₁∈𝔗ₙ,ₚ₁ and T₂∈𝔗ₙ,ₚ₂, can we always find an integer l, with 1≤l≤n, such that Z_C(T₁,i)≤Z_C(T₂,i) for 1≤i≤l and Z_C(T₁,i)≥Z_C(T₂,i) for l+1≤i≤n? The formula quantifies arbitrary finite carriers and all their tree graphs. Equal leaf counts are permitted. Integer coefficient indices in the two positive ranges are converted by toNat; this preserves their values. No initial exchange of the two trees is allowed by the literal assertion."),
            Describe.Lean(DescribeId.Create("connected-crossing-result"), DeclarationHandle.Create(Prefix + "result"),
                H("The singleton obstruction"), StatementSource.FromAuthor(Disp(new Formula.Not(F.Id("claim")))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Take T₁=P₄ with edges 01,12,23 and T₂=K₁,₃ with edges 01,02,03. Mathlib certifies the path is a tree. The star is connected through its center and has three edges on four vertices, so it too is a tree. Every singleton induces a connected graph. Either path endpoint forces successively along the path; an interior singleton has a disjoint fort and cannot force all vertices. Every star singleton also has a disjoint fort: for the center use the three leaves, and for a leaf use the other two leaves. The imported fort invariant excludes every possible forcing derivation, including the leaf-to-center move followed by a stall. Exhausting the actual singleton subsets yields coefficients two and zero. Every permitted cutoff l includes i=1 in its low segment and would imply 2≤0. Section 4 of the source already prints this pair and its polynomials; no new example or coefficient discovery is asserted. Only the singleton coefficients are needed here. Swapping this particular pair admits cutoff two according to the source polynomials, while universal exchange-permitted, either-direction and leaf-ordered versions remain outside this result. The established source theorems and its separate Problem 5.2 are unaffected."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(ProblemSlugRef.Create("mukherjee-ray-2026-ordered-connected-forcing-crossing"), ResolutionKind.Refuted))), []));

    private static DocumentBlock Def(string id, string name, string title, Formula formula, string text) =>
        Describe.Lean(DescribeId.Create("connected-crossing-" + id), DeclarationHandle.Create(Prefix + name),
            H(title), StatementSource.FromAuthor(formula), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(text))), DescribeRole.Definition);
    private static Formula Call(string name, params Formula[] args)
    {
        var parts = name.Split('.');
        var symbols = new System.Collections.Generic.List<Formula>();
        foreach (var part in parts)
        {
            if (symbols.Count > 0) symbols.Add(Dot);
            symbols.Add(F.Id(part));
        }
        return new Formula.Apply(Seq(Operatorname, Grp(Seq([.. symbols]))), [.. args]);
    }
    private static Formula Par(Formula f) => Seq(Open, f, Close);
    private static Formula All(string name, Formula type, Formula body) => Seq(Forall, Sp, Par(Seq(F.Id(name), Sp, Colon, Sp, type)), Comma, Sp, body);
    private static Formula Ex(string name, Formula type, Formula body) => Seq(Exists, Sp, Par(Seq(F.Id(name), Sp, Colon, Sp, type)), Comma, Sp, body);
    private static Formula Inst(Formula type, Formula body) => Seq(OpenBracket, type, CloseBracket, Comma, Sp, body);
    private static Formula SetOf(string name, Formula type, Formula body) => Seq(OpenBrace, F.Id(name), Sp, Colon, Sp, type, Sp, Mid, Sp, body, CloseBrace);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Logic(Formula a, FormulaLogicOperator op, Formula b) => new Formula.Logic(Par(a), op, Par(b));
    private static Formula And(Formula a, Formula b) => Logic(a, FormulaLogicOperator.And, b);
    private static Formula Imp(Formula a, Formula b) => Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula N => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Z => Seq(Mathbb, Grp(F.Id("Z")));
    private static Formula V => F.Id("V");
    private static Formula G => F.Id("G");
    private static Formula S => F.Id("S");
    private static Formula Graph(Formula v) => Call("SimpleGraph", v);
    private static Formula ConnectedFormula() => Disp(All("V", F.Id("Type"), All("G", Graph(V), All("S", Call("Finset", V),
        Logic(Call("connectedForcing", G, S), FormulaLogicOperator.Iff,
            And(Call("Connected", Call("induce", G, Par(Seq(S, Sp, Colon, Sp, Call("Set", V))))), Call("IsZeroForcing", G, Par(Seq(S, Sp, Colon, Sp, Call("Set", V))))))))));
    private static Formula CoefficientFormula() => Disp(All("V", F.Id("Type"), Inst(Call("Fintype", V), All("G", Graph(V), All("i", N,
        Eq(Call("coefficient", G, F.Id("i")), Call("card", SetOf("S", Call("Finset", V),
            And(Eq(Call("card", S), F.Id("i")), Call("connectedForcing", G, S))))))))));
    private static Formula LeavesFormula() => Disp(All("V", F.Id("Type"), All("G", Graph(V),
        Eq(Call("leafCount", G), Call("Nat.card", SetOf("v", V,
            Eq(Call("Nat.card", SetOf("w", V, Call("Adj", G, F.Id("v"), F.Id("w")))), D(1))))))));
    private static Formula ClaimFormula()
    {
        Formula n = F.Id("n"), p = F.Id("p"), q = F.Id("q"), w = F.Id("W"), h = F.Id("H"), l = F.Id("l"), i = F.Id("i");
        Formula index = Call("toNat", i);
        Formula low = Imp(And(Le(D(1), i), Le(i, l)), Le(Call("coefficient", G, index), Call("coefficient", h, index)));
        Formula high = Imp(And(Le(new Formula.Binary(l, FormulaBinaryOperator.Add, D(1)), i), Le(i, Par(Seq(n, Sp, Colon, Sp, Z)))),
            Le(Call("coefficient", h, index), Call("coefficient", G, index)));
        Formula body = Ex("l", Z, And(Le(D(1), l), And(Le(l, Par(Seq(n, Sp, Colon, Sp, Z))), All("i", Z, And(low, high)))));
        body = Imp(Eq(Call("leafCount", h), q), body);
        body = Imp(Eq(Call("leafCount", G), p), body);
        body = Imp(Eq(Call("card", w), n), body);
        body = Imp(Eq(Call("card", V), n), body);
        body = Imp(Call("IsTree", h), body);
        body = Imp(Call("IsTree", G), body);
        body = All("G", Graph(V), All("H", Graph(w), body));
        body = Inst(Call("Fintype", V), Inst(Call("Fintype", w), body));
        body = All("V", F.Id("Type"), All("W", F.Id("Type"), body));
        body = All("n", N, All("p", N, All("q", N, body)));
        return Disp(Logic(F.Id("claim"), FormulaLogicOperator.Iff, body));
    }
}
