using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Partitions;

internal sealed class BallantineRegularSymmetricImageRefutationDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S1/Recurrence/Partitions/BallantineRegularSymmetricImageRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Recurrence/ballantine2024elementary");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Conjecture 16's d=5 column is false at n=4: the actual difference is 2, not 1.",
        H("A Counterexample to the Regular Elementary Symmetric Image Table"),
        Blocks(
            Paragraph(Text(
                "A partition of n is represented by Nat.Partition n, whose positive parts "
                    + "sum to n. Multiset powersetCard selects positions, so equal parts "
                    + "retain the multiplicity of the corresponding square-free monomials. "
                    + "Finite-set image removes duplicate image partitions.")),
            Node("elementary-symmetric-image", "The elementary symmetric image of a partition",
                PreFormula(),
                "For a partition lambda, pre(k,lambda) is the multiset obtained by taking "
                    + "every k-position submultiset of its parts and mapping it to its product.",
                "pre", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("image-family", "The image family ImP",
                ImPFormula(),
                "The filter retains exactly the partitions with at least k parts, and image "
                    + "applies pre(k) while counting equal images once.",
                "imP", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("regular-partition", "Regularity of an image partition",
                IsRegularFormula(),
                "IsRegular(d,mu) says that no part x of mu is divisible by d.",
                "IsRegular", DescribeRole.Definition,
                AssessedProvenance.FromLiterature(Source)),
            Node("regular-image-count", "The regular image count",
                RFormula(),
                "The value r(d,k,n) is the cardinality of the d-regular members of imP(k,n).",
                "r", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("printed-residue-table", "The printed residue-class table",
                TableFormula(),
                "Each displayed natDiv is natural-number division, hence the floor of the "
                    + "corresponding nonnegative rational quotient. Every branch is then cast "
                    + "to an integer. The rows are displayed column by column for d equal to "
                    + "2, 3, 4 and 5.",
                "table", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("conjecture-sixteen", "Conjecture 16",
                ClaimFormula(),
                "The source definitions say: \"Given a partition λ = (λ₁, "
                    + "λ₂, …, λ_ℓ) with ℓ ≥ k, we define pre_k(λ) to be "
                    + "the partition whose parts are the summands in the evaluation "
                    + "e_k(λ₁, λ₂, …, λ_ℓ).\" \"ImP_k(n) = "
                    + "pre_k(P_k(n))\" \"By contrast, a partition is d-regular if it "
                    + "contains no part which is a multiple of d.\" \"Let r_{d,k}(n) = "
                    + "|{λ | λ ∈ ImP_k(n) is d-regular}|.\" Conjecture 16 states: "
                    + "\"The value of r_{d,2}(n) − r_{d,3}(n) for d = 2, 3, 4, and 5 are "
                    + "shown in the columns of the following table. These values depend on "
                    + "the congruence class of n modulo 2, 6, 4, and 10, respectively. The "
                    + "first column of the table gives the congruence class for n.\"",
                "claim", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("conjecture-sixteen-refuted", "The printed table fails at d=5 and n=4",
                ResultFormula(),
                "For n=4, the degree-two image set is {(3), (4), (2,2,1), (1,1,1,1,1,1)} "
                    + "and the degree-three image set is {(2), (1,1,1,1)}. All six listed "
                    + "images are 5-regular, so the two cardinalities are 4 and 2. Their "
                    + "integer difference is 2, whereas the residue-four entry in the d=5 "
                    + "column is 3 natDiv(4,10) + 1 = 1.",
                "result", DescribeRole.Theorem, AssessedProvenance.FromRepo()))));

    private static DocumentBlock Node(
        string id, string title, Formula formula, string prose, string declaration,
        DescribeRole role, AssessedProvenance provenance) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(formula), provenance,
            Blocks(Paragraph(Text(prose))), role);

    private static Formula PreFormula()
    {
        var k = F.Id("k");
        var n = F.Id("n");
        var l = F.Id("l");
        var rhs = Call("map", F.Id("prod"), Call("powersetCard", Call("parts", l), k));
        return Disp(Universal(
            [Bound("k", Naturals()), Bound("n", Naturals()), Bound("l", Call("Partition", n))],
            Equal(Call("pre", k, l), rhs)));
    }

    private static Formula ImPFormula()
    {
        var k = F.Id("k");
        var n = F.Id("n");
        var l = F.Id("l");
        var predicate = Parenthesized(Seq(
            l, Colon, Sp, Call("Partition", n), Sp, Mapsto, Sp,
            LessEqual(k, Call("card", Call("parts", l)))));
        var filtered = Call("filter", predicate, Call("univ", Call("Partition", n)));
        var rhs = Call("image", Call("pre", k), filtered);
        return Disp(Universal([Bound("k", Naturals()), Bound("n", Naturals())],
            Equal(Call("imP", k, n), rhs)));
    }

    private static Formula IsRegularFormula()
    {
        var d = F.Id("d");
        var mu = F.Id("mu");
        var x = F.Id("x");
        var body = Universal([Bound("x", Naturals())],
            Implies(Member(x, mu), new Formula.Not(Divides(d, x))));
        return Disp(Universal(
            [Bound("d", Naturals()), Bound("mu", Call("Multiset", Naturals()))],
            Iff(Parenthesized(Call("IsRegular", d, mu)), Parenthesized(body))));
    }

    private static Formula RFormula()
    {
        var d = F.Id("d");
        var k = F.Id("k");
        var n = F.Id("n");
        var rhs = Call("card", Call("filter", Call("IsRegular", d), Call("imP", k, n)));
        return Disp(Universal(
            [Bound("d", Naturals()), Bound("k", Naturals()), Bound("n", Naturals())],
            Equal(Call("r", d, k, n), rhs)));
    }

    private static Formula TableFormula()
    {
        var d = F.Id("d");
        var n = F.Id("n");
        Formula q2 = NatDiv(Add(n, D(2)), D(4));
        Formula q3 = NatDiv(n, D(6));
        Formula q4 = NatDiv(n, D(4));
        Formula q5 = NatDiv(n, D(1, 0));
        return Disp(Universal([Bound("d", Naturals()), Bound("n", Naturals())],
            new Formula.Aligned([
                TableClause(d, n, D(2), D(2), D(0), q2),
                TableClause(d, n, D(2), D(2), D(1), D(0)),
                TableClause(d, n, D(3), D(6), D(0), Multiply(D(2), q3)),
                TableClause(d, n, D(3), D(6), D(1), q3),
                TableClause(d, n, D(3), D(6), D(2), Add(q3, D(1))),
                TableClause(d, n, D(3), D(6), D(3), Add(Multiply(D(2), q3), D(1))),
                TableClause(d, n, D(3), D(6), D(4), Add(q3, D(1))),
                TableClause(d, n, D(3), D(6), D(5), Add(q3, D(1))),
                TableClause(d, n, D(4), D(4), D(0), q4),
                TableClause(d, n, D(4), D(4), D(1), q4),
                TableClause(d, n, D(4), D(4), D(2), Add(q4, D(1))),
                TableClause(d, n, D(4), D(4), D(3), Add(q4, D(1))),
                TableClause(d, n, D(5), D(1, 0), D(0), Multiply(D(3), q5)),
                TableClause(d, n, D(5), D(1, 0), D(1), Multiply(D(4), q5)),
                TableClause(d, n, D(5), D(1, 0), D(2), Multiply(D(3), q5)),
                TableClause(d, n, D(5), D(1, 0), D(3), Add(Multiply(D(3), q5), D(1))),
                TableClause(d, n, D(5), D(1, 0), D(4), Add(Multiply(D(3), q5), D(1))),
                TableClause(d, n, D(5), D(1, 0), D(5), Add(Multiply(D(3), q5), D(2))),
                TableClause(d, n, D(5), D(1, 0), D(6), Add(Multiply(D(4), q5), D(2))),
                TableClause(d, n, D(5), D(1, 0), D(7), Add(Multiply(D(3), q5), D(2))),
                TableClause(d, n, D(5), D(1, 0), D(8), Add(Multiply(D(3), q5), D(2))),
                TableClause(d, n, D(5), D(1, 0), D(9), Add(Multiply(D(3), q5), D(3))),
                Parenthesized(Implies(
                    new Formula.Not(Member(d, FourColumns())),
                    Equal(Call("table", d, n), CastInt(D(0)))))
            ])));
    }

    private static Formula ClaimFormula()
    {
        var n = F.Id("n");
        var d = F.Id("d");
        var difference = Subtract(CastInt(Call("r", d, D(2), n)),
            CastInt(Call("r", d, D(3), n)));
        var equation = Equal(difference, Call("table", d, n));
        return Disp(Iff(
            Parenthesized(F.Id("claim")),
            Parenthesized(Universal(
                [Bound("n", Naturals()), Bound("d", Naturals())],
                Implies(Member(d, FourColumns()), equation)))));
    }

    private static Formula ResultFormula() => Disp(new Formula.Not(F.Id("claim")));

    private static Formula TableClause(
        Formula d, Formula n, Formula column, Formula modulus, Formula residue, Formula value)
    {
        var condition = And(
            Equal(d, column),
            Equal(new Formula.Modulo(n, modulus), residue));
        return Parenthesized(Implies(
            condition,
            Equal(Call("table", d, n), CastInt(value))));
    }

    private static Formula FourColumns() =>
        new Formula.SetLiteral([D(2), D(3), D(4), D(5)]);

    private static Formula NatDiv(Formula left, Formula right) =>
        Call("natDiv", left, right);

    private static Formula CastInt(Formula value) =>
        Parenthesized(Seq(value, Sp, Colon, Sp, Integers()));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula Universal(Formula.BoundVariable[] variables, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables], body);

    private static Formula Naturals() =>
        new Formula.NamedConstant(FormulaIdentifier.Create("Nat"));

    private static Formula Integers() =>
        new Formula.NamedConstant(FormulaIdentifier.Create("Int"));

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula LessEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);

    private static Formula Member(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.MemberOf, right);

    private static Formula Divides(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Divides, right);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(
            Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(
            Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));

    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Iff, right);

    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);

    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);

    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
}
