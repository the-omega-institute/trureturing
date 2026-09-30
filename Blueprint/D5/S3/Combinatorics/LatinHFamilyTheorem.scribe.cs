using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics;

internal sealed class LatinHFamilyTheoremDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/LatinHFamilyTheorem.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Combinatorics/ghafari2026transversals");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For every integer k at least nine, the literal H square has the three displayed transversals. Every two transversals meet, although no entry belongs to all transversals.",
        H("Three transversals of the H family"),
        Blocks(
            Node("coordinate-permutations", "Uniform coordinate permutations",
                "coordinate_permutations", PermutationsFormula(),
                "For each of the three profiles, the six cap complement certificates exclude every column and symbol of the four bulk classes. The head, bulk and tail rows exhaust the square. Internal injectivity and this exclusion make each complete coordinate map a bijection, including the empty bulk when k equals nine."),
            Node("transversal-obstruction", "The distinguished-entry obstruction",
                "transversal_obstruction", ObstructionFormula(),
                "Choosing the unique entry in each row of an arbitrary transversal gives column and symbol permutations. Their sums force the total priority increment to be congruent to two k modulo four k. The row lower bounds sum to minus two k plus three. If at most one distinguished entry is selected, the upper bound is two k minus three, which contradicts that congruence."),
            Node("complete-family", "The complete H-family theorem",
                "result", ResultFormula(),
                "The parameter is an integer at least nine; its natural representative has exactly the same value and gives order four k. Latinness of the actual square is the explicit cited premise. Each literal profile gives one source entry in every row, column and symbol, contains precisely the two distinguished entries indexed by the other profiles, and the first two profiles meet exactly at the third distinguished entry. Their triple intersection is empty. Every arbitrary transversal contains at least two of the three distinguished entries, so any two transversals meet. The three explicit witnesses rule out every pinned entry.")),
        []));

    private static DocumentBlock Node(string id, string title, string declaration,
        Formula formula, string prose) =>
        Describe.Lean(DescribeId.Create("latin-h-family-" + id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(formula),
            declaration == "transversal_obstruction"
                ? AssessedProvenance.FromLiterature(Source)
                : AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula Exists(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), domain, body);
    private static Formula Eq(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Le(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Imp(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);
    private static Formula And(params Formula[] clauses)
    {
        Formula result = clauses[^1];
        for (var i = clauses.Length - 2; i >= 0; i--)
            result = new Formula.Logic(clauses[i], FormulaLogicOperator.And, result);
        return result;
    }
    private static Formula Nat() => new Formula.NamedConstant(FormulaIdentifier.Create("Nat"));
    private static Formula Int() => new Formula.NamedConstant(FormulaIdentifier.Create("Int"));
    private static Formula Rows(Formula k) => Call("Fin", Call("order", k));
    private static Formula Entries(Formula k) => Call("Prod", Rows(k), Call("Prod", Rows(k), Rows(k)));
    private static Formula Sets(Formula k) => Call("Set", Entries(k));
    private static Formula Member(Formula entry, Formula set) =>
        new Formula.Relation(entry, FormulaRelationOperator.MemberOf, set);
    private static Formula Inter(Formula left, Formula right) => Call("inter", left, right);
    private static Formula T(Formula k, Formula j) => Call("T", k, j);
    private static Formula Permutations(Formula k, Formula j) => And(
        Call("Bijective", Call("column", k, j)),
        Call("Bijective", Call("symbol", k, j)));

    private static Formula PermutationsFormula()
    {
        var k = F.Id("k"); var j = F.Id("j");
        return Disp(All("k", Nat(), Imp(Le(D(9), k),
            All("j", Call("Fin", D(3)), Permutations(k, j)))));
    }

    private static Formula ObstructionFormula()
    {
        var k = F.Id("k"); var s = F.Id("S");
        return Disp(All("k", Nat(), Imp(Le(D(9), k),
            All("S", Sets(k), Imp(Call("IsTransversal", k, s),
                Le(D(2), Call("ncard", Inter(Call("D", k), s))))))));
    }

    private static Formula ResultFormula()
    {
        var integer = F.Id("K"); var k = Call("toNat", integer);
        var j = F.Id("j"); var a = F.Id("a"); var e = F.Id("e");
        var s = F.Id("S"); var u = F.Id("U");
        var d = Call("D", k);
        var common = Inter(T(k, D(0)), T(k, D(1)));
        var profiles = All("j", Call("Fin", D(3)), And(
            Permutations(k, j),
            All("a", Rows(k), Eq(Call("symbol", k, j, a),
                Call("square", k, a, Call("column", k, j, a)))),
            Call("IsTransversal", k, T(k, j)),
            Eq(Inter(T(k, j), d), Call("diff", d,
                new Formula.SetLiteral([Call("distinguished", k, j)])))));
        var pairs = All("S", Sets(k), All("U", Sets(k),
            Imp(Call("IsTransversal", k, s), Imp(Call("IsTransversal", k, u),
                Exists("e", Entries(k), And(Member(e, s), Member(e, u)))))));
        return Disp(All("K", Int(), Imp(Le(D(9), integer),
            Imp(Call("IsLatin", Call("order", k), Call("square", k)), And(
                Eq(Call("intCast", Call("order", k)),
                    new Formula.Binary(D(4), FormulaBinaryOperator.Multiply, integer)),
                profiles,
                Eq(common, new Formula.SetLiteral([Call("d2", k)])),
                Eq(Inter(common, T(k, D(2))), new Formula.SetLiteral([])),
                pairs,
                All("e", Entries(k), new Formula.Not(Call("IsPinned", k, e))))))));
    }
}
