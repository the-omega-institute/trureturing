using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ArithSums;

internal sealed class DebskiBarrycadeOmittedElementRefutationDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ArithSums/DebskiBarrycadeOmittedElementRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/ArithSums/debski2026barrycades");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The printed i >= 3 relation in Conjecture 2 (2) is false at i = 3.",
        H("Refutation of the printed barrycade relation"),
        Blocks(
            Node("partialSums", "The partial-sum set", PartialSumsFormula(),
                "For a sequence mu, partialSums is the set of sums of its first k+1 entries. "
                    + "This is the paper's S_mu notation.", DescribeRole.Definition,
                AssessedProvenance.FromLiterature(Source)),
            Node("row", "The greedy row", RowFormula(),
                "row r k is the infimum of the positive entries not used in the first k "
                    + "positions of row r and whose new partial sum is absent from all earlier "
                    + "rows. The prefix is indexed by Fin k; the equivalent range notation is "
                    + "shown in the Lean fidelity example.", DescribeRole.Definition,
                AssessedProvenance.FromLiterature(Source)),
            Node("claim", "Printed Conjecture 2 (2)", ClaimFormula(),
                "The paper says: \"A1(i) is the smallest number that is omitted in the "
                    + "quasi-permutation rho_i\" and \"A2(i) = rho_i(1)\". Algorithm 1 line 7 "
                    + "says: \"Choose the smallest positive integer a such that a is not in U "
                    + "and s + a is not in P_(r-1).\" Conjecture 2 (2) then prints "
                    + "A2(i) = A1(i) + 1 for every i >= 3.", DescribeRole.Definition,
                AssessedProvenance.FromLiterature(Source)),
            Node("result", "The printed relation is false", ResultFormula(),
                "The repository proves that rho_3 = (4, 3, 1, 5, 6, ...) omits 2 and starts "
                    + "with 4. Its least omitted positive integer is therefore 2, so the relation "
                    + "would require 4 = 3 and fails at i = 3.", DescribeRole.Theorem,
                AssessedProvenance.FromRepo(),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("debski-barrycade-omitted-element-refutation"),
                    ResolutionKind.Refuted)))));

    private static DocumentBlock Node(
        string name,
        string title,
        Formula formula,
        string prose,
        DescribeRole role,
        AssessedProvenance provenance,
        OpenProblemResolutionClaim? claim = null) => Describe.Lean(
        DescribeId.Create("debski-barrycade-" + name.ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name), H(title),
        StatementSource.FromAuthor(formula), provenance,
        Blocks(Paragraph(Text(prose))), role, claim);

    private static Formula PartialSumsFormula()
    {
        var mu = F.Id("mu");
        var s = F.Id("s");
        var k = F.Id("k");
        var i = F.Id("i");
        var prefix = Seq(Sum, Underscore,
            Grp(Seq(i, Sp, InMacro, Sp, Call("range", Add(k, D(1))))), Sp,
            Call("mu", i));
        var set = Seq(OpenBrace, s, Sp, Bar, Sp,
            Exists("k", Nat(), Equal(s, prefix)), CloseBrace);
        return Disp(UniversalTyped("mu", new Formula.TypeArrow(Nat(), Nat()),
            Equal(Call("partialSums", mu), set)));
    }

    private static Formula RowFormula()
    {
        var r = F.Id("r");
        var k = F.Id("k");
        var a = F.Id("a");
        var i = F.Id("i");
        var j = F.Id("j");
        var n = F.Id("n");
        var prefix = Seq(new Formula.Subscript(Sum,
            Seq(i, Sp, InMacro, Sp, Call("Fin", k))), Sp,
            Call("row", r, Call("val", i)));
        var earlier = Seq(Cup, Underscore,
            Grp(Seq(j, Sp, Colon, Sp, OpenBrace, j, Sp, Lt, Sp, r, CloseBrace)), Sp,
            Call("partialSums", Parenthesized(Seq(LambdaLower, Sp, n, Sp, Mapsto, Sp,
                Call("row", Call("val", j), n)))));
        var predicate = And(
            Pos(a),
            UniversalTyped("i", Call("Fin", k),
                NotEqual(Call("row", r, Call("val", i)), a)),
            Not(Parenthesized(Seq(prefix, Sp, Plus, Sp, a, Sp, InMacro, Sp, earlier))));
        return Disp(UniversalMany(
            [Bound("r", Nat()), Bound("k", Nat())],
            Equal(Call("row", r, k), Call("sInf", Seq(OpenBrace, a, Sp, Bar, Sp,
                predicate, CloseBrace)))));
    }

    private static Formula ClaimFormula()
    {
        var i = F.Id("i");
        var n = F.Id("n");
        var m = F.Id("m");
        var k = F.Id("k");
        var omitted = Seq(OpenBrace, m, Sp, Bar, Sp,
            And(Pos(m), Universal("k", NotEqual(Call("row", Subtract(i, D(1)), k), m))),
            CloseBrace);
        var least = Call("IsLeast", omitted, n);
        var body = Implies(LessEqual(D(3), i),
            Universal("n", Implies(least,
                Equal(Call("row", Subtract(i, D(1)), D(0)), Add(n, D(1))))));
        return Disp(Universal("i", body));
    }

    private static Formula ResultFormula() => Disp(Not(F.Id("claim")));

    private static Formula Nat() => new Formula.NamedConstant(FormulaIdentifier.Create("Nat"));
    private static Formula.BoundVariable Bound(string name, Formula type) =>
        new Formula.BoundVariable(FormulaIdentifier.Create(name), type);
    private static Formula Universal(string name, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), Nat(), body);
    private static Formula UniversalTyped(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula UniversalMany(Formula.BoundVariable[] vars, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. vars], body);
    private static Formula Exists(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula LessEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula NotEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);
    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies,
            Parenthesized(right));
    private static Formula Not(Formula value) => new Formula.Not(value);
    private static Formula Pos(Formula value) => Less(F.D(0), value);
    private static Formula Less(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula And(params Formula[] clauses)
    {
        Formula result = Parenthesized(clauses[^1]);
        for (int index = clauses.Length - 2; index >= 0; index--)
            result = new Formula.Logic(Parenthesized(clauses[index]),
                FormulaLogicOperator.And, result);
        return result;
    }
}
