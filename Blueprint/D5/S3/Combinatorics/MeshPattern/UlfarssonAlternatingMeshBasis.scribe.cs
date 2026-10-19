using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.MeshPattern;

internal sealed class UlfarssonAlternatingMeshBasisDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/MeshPattern/UlfarssonAlternatingMeshBasis.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/PermutationPatterns/ulfarsson2024bisc");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every mesh-pattern basis of the even permutations consists exactly of fully shaded odd permutations.",
        H("The Mesh-Pattern Basis of the Even Permutations"),
        Blocks(
            Node("ulfarsson-mesh-pattern", "Mesh patterns", "MeshPattern", MeshPatternFormula(),
                "Ulfarsson writes: \"This inspired West [Wes90] to define barred patterns, but we will use the more expressive mesh patterns of Brändén and Claesson [BC11], which allow us to forbid letters from occupying certain regions in a pattern.\" (Section 2, page 3.) The structure has exactly the fields k : Nat, p : Equiv.Perm (Fin k), and R : Set (Fin (k + 1) × Fin (k + 1)); its constructor is displayed below. The permutation indices are zero-based; the cell coordinates range from 0 through k.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("ulfarsson-occurs", "Occurrence of a mesh pattern", "Occurs", OccursFormula(),
                "Ulfarsson writes: \"This inspired West [Wes90] to define barred patterns, but we will use the more expressive mesh patterns of Brändén and Claesson [BC11], which allow us to forbid letters from occupying certain regions in a pattern.\" (Section 2, page 3.) The selected positions form an order embedding e. Their values have the relative order of P.p. For an unselected point x, the two cardinalities count selected positions to its left and selected values below its value. Their pair must not be a shaded cell. The symbol s denotes the containing permutation σ.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("ulfarsson-avoidance", "Avoidance over all lengths", "Av", AvFormula(),
                "\"We let S denote the set of all permutations and Av(P) denote the permutations that avoid all the patterns in a set P.\" (Basic definitions, page 2.) The dependent sum records every length, including zero, together with its permutation.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("ulfarsson-basis", "A basis for a set of permutations", "IsBasis", IsBasisFormula(),
                "\"Given a set of permutations A, we call a set of patterns P a basis for A if A = Av(P), and no subset of P has this property.\" (Section 2, page 2.) IsBasis states the equality in the symmetric orientation Av P = A and expresses minimality by quantifying over every subset Q of P.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("ulfarsson-alternating", "The even permutations", "Alt", AltFormula(),
                "\"Let A be the union of the alternating subgroups\" (Conjecture 2.4.2, page 8). Alt contains the permutations of every length whose sign is 1. Permutations of lengths zero and one are included.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("ulfarsson-claim", "Conjecture 2.4.2", "claim", Disp(IffFormula(X("claim"), ClaimBody())),
                "\"Let A be the union of the alternating subgroups, and let P be a basis of patterns such that A = Av(P). Then P = {(p, {0, …, n} × {0, …, n}) : p ∈ S_n ∖ A for some n}.\" (Conjecture 2.4.2, page 8.) Here A is Alt, p ∈ S_n is encoded by Equiv.Perm (Fin n), full shading is R = Set.univ, and exclusion from A is sign p ≠ 1.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("ulfarsson-result", "Conjecture 2.4.2 holds", "result", Disp(ClaimBody()),
                "If a cell is unshaded, insert two points in that cell in either order. Both resulting permutations contain the pattern; exchanging the two points reverses the sign, so one resulting permutation is even. Therefore every forbidden pattern is fully shaded. A fully shaded pattern occurs only in its underlying permutation, which forces the forbidden patterns to be exactly the odd permutations with full shading. The argument uses only Av P = Alt; the minimality clause of IsBasis is unnecessary.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source))),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, Formula formula,
        string prose, DescribeRole role, AssessedProvenance provenance) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(formula), provenance,
            Blocks(Paragraph(Text(prose))), role);

    private static Formula MeshPatternFormula()
    {
        var k = X("k");
        var p = X("p");
        var r = X("R");
        return Disp(All("k", Naturals(), All("p", Perm(Fin(k)),
            All("R", SetType(CellType(k)),
                Seq(App(Q("MeshPattern", "mk"), k, p, r), Sp, Colon, Sp, X("MeshPattern"))))));
    }

    private static Formula OccursFormula()
    {
        var p = X("P");
        var n = X("n");
        var s = X("s");
        var e = X("e");
        var i = X("i");
        var j = X("j");
        var x = X("x");
        var c = X("c");
        var pk = Field(p, "k");
        var selectedOrder = All("i", Fin(pk), All("j", Fin(pk),
            IffFormula(Less(App(s, App(e, i)), App(s, App(e, j))),
                Less(App(Field(p, "p"), i), App(Field(p, "p"), j)))));
        var positions = CountFilter("i", Fin(pk), Less(App(e, i), x));
        var values = CountFilter("i", Fin(pk), Less(App(s, App(e, i)), App(s, x)));
        var excludedCell = new Formula.Not(Parenthesized(And(
            Equal(Call("val", Projection(c, 1)), positions),
            Equal(Call("val", Projection(c, 2)), values))));
        var shading = All("x", Fin(n), ImpliesFormula(
            new Formula.Not(Parenthesized(Member(x, App(Q("Set", "range"), e)))),
            All("c", CellType(pk), ImpliesFormula(Member(c, Field(p, "R")), excludedCell))));
        var occurrence = ExistsFormula("e", Call("OrderEmbedding", Fin(pk), Fin(n)),
            And(selectedOrder, shading));
        return Disp(All("P", X("MeshPattern"), All("n", Naturals(), All("s", Perm(Fin(n)),
            IffFormula(Call("Occurs", p, s), occurrence)))));
    }

    private static Formula AvFormula()
    {
        var p = X("P");
        var s = X("s");
        var q = X("q");
        var avoided = All("q", X("MeshPattern"), ImpliesFormula(Member(q, p),
            new Formula.Not(Parenthesized(Call("Occurs", q, Projection(s, 2))))));
        return Disp(All("P", SetType(X("MeshPattern")),
            Equal(Call("Av", p), PredicateSet("s", Permutations(), avoided))));
    }

    private static Formula IsBasisFormula()
    {
        var a = X("A");
        var p = X("P");
        var q = X("Q");
        var minimal = All("Q", SetType(X("MeshPattern")), ImpliesFormula(
            Seq(q, Sp, Subseteq, Sp, p),
            ImpliesFormula(Equal(Call("Av", q), a), Equal(q, p))));
        return Disp(All("A", SetType(Permutations()), All("P", SetType(X("MeshPattern")),
            IffFormula(Call("IsBasis", a, p), And(Equal(Call("Av", p), a), minimal)))));
    }

    private static Formula AltFormula() => Disp(Equal(X("Alt"), PredicateSet("s", Permutations(),
        Equal(App(Q("Equiv", "Perm", "sign"), Projection(X("s"), 2)), D(1)))));

    private static Formula ClaimBody()
    {
        var p = X("P");
        var q = X("q");
        var odd = new Formula.Relation(App(Q("Equiv", "Perm", "sign"), Field(q, "p")),
            FormulaRelationOperator.NotEqual, D(1));
        var target = PredicateSet("q", X("MeshPattern"), And(
            Equal(Field(q, "R"), Q("Set", "univ")), odd));
        return All("P", SetType(X("MeshPattern")), ImpliesFormula(
            Call("IsBasis", X("Alt"), p), Equal(p, target)));
    }

    private static Formula Permutations() => Seq(Sigma, Sp,
        Parenthesized(Seq(X("n"), Sp, Colon, Sp, Naturals())), Comma, Sp, Perm(Fin(X("n"))));

    private static Formula CountFilter(string variable, Formula type, Formula predicate) =>
        App(Q("Finset", "card"), App(Q("Finset", "filter"),
            Parenthesized(Seq(X(variable), Sp, Colon, Sp, type, Sp, Mapsto, Sp, predicate)),
            Parenthesized(Seq(Q("Finset", "univ"), Sp, Colon, Sp, Call("Finset", type)))));

    private static Formula PredicateSet(string name, Formula type, Formula predicate) =>
        Seq(OpenBrace, X(name), Sp, Colon, Sp, type, Sp, Mid, Sp, predicate, CloseBrace);

    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);

    private static Formula ExistsFormula(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);

    private static Formula IffFormula(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Iff, Parenthesized(b));

    private static Formula ImpliesFormula(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));

    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));

    private static Formula Less(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThan, b);

    private static Formula Member(Formula a, Formula b) => Seq(a, Sp, InMacro, Sp, b);
    private static Formula CellType(Formula k) => Seq(Fin(Add(k, D(1))), Sp, Times, Sp, Fin(Add(k, D(1))));
    private static Formula Perm(Formula type) => App(Q("Equiv", "Perm"), type);
    private static Formula Fin(Formula n) => Call("Fin", n);
    private static Formula SetType(Formula type) => Call("Set", type);
    private static Formula Naturals() => Seq(Mathbb, Grp(X("N")));
    private static Formula Field(Formula value, string name) => Seq(value, Dot, X(name));
    private static Formula Projection(Formula value, byte index) => Seq(value, Dot, D(index));
    private static Formula X(string name) => F.Id(name);
    private static Formula Q(params string[] names) => Seq([.. names.Select(X).SelectMany((name, i) =>
        i == 0 ? new[] { name } : new[] { Dot, name })]);
    private static Formula App(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
}
