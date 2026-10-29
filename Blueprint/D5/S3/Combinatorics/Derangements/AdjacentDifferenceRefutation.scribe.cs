using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Derangements;

internal sealed class AdjacentDifferenceRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Derangements/AdjacentDifferenceRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/FiniteGroups/kagey2024a378495");
    private static readonly LibraryNoteRef Sequence =
        LibraryNoteRef.Create("D5/L/FiniteGroups/lang2014a238474");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The literal adjacent-column identity with the zero-based index n-4 fails at n=5: the actual cardinality difference is twenty and the absolute sequence value is six.",
        H("A Counterexample to the Literal Adjacent Difference"),
        Blocks(
            Node("sequence", "The zero-based auxiliary sequence", "b",
                "For every natural m, b(m) is (-1)^m times (m+3)! divided by 2(m+1), computed in the rationals. In the formulas, castQ denotes the natural-number embedding into the rationals. The factorial and m+1 are first computed in the natural numbers and then cast. The denominator is nonzero for every m >= 0. This is the formula of A238474 with offset zero: b(0)=3 and b(1)=-6. The exponent uses the rational number minus one, rather than natural truncated subtraction.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Sequence)),
            Node("literal-claim", "The literal adjacent-column conjecture", "claim",
                "The proposition claim asserts that for every natural n with 4 <= n, T(n,n-1)-T(n,n-2) equals the absolute value of b(n-4). Here T is the cardinality of all permutations of Fin n with no fixed point and no cycle factor of the forbidden length. Each cardinality is cast to the rationals before ordinary subtraction; the absolute value is rational. Every index subtraction is natural subtraction, and the hypothesis ensures that n-4 has its ordinary nonnegative meaning. The shift is exactly n-4, with no change of the zero offset of b and no upper bound on n.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("literal-refutation", "Five labels contradict the asserted equality", "result",
                "The proposition claim is false. At n=5, a derangement cannot contain a 4-cycle: the remaining label would be fixed. Thus excluded(5,4) is empty, whereas the cycle type (3,2) contributes exactly 5!/(2 times 3)=20 excluded permutations at length three. Applying the complementary-count identities to the same derangement set gives T(5,4)=T(5,3)+20 and hence the rational difference twenty. The source sequence has b(5-4)=b(1)=-6, whose absolute value is six. Since 20 differs from 6 and five satisfies the stated lower bound, this one exact counterexample negates the whole universal proposition. It does not assert a replacement formula or negate the separate terminal-column identity.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source))),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, AssessedProvenance provenance) =>
        Describe.Lean(DescribeId.Create("a378495-adjacent-" + id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(Disp(Statement(declaration))),
            provenance, Blocks(Paragraph(Text(prose))), role);

    private static Formula Statement(string declaration)
    {
        Formula m = F.Id("m"), n = F.Id("n");
        var value = new Formula.Fraction(
            Multiply(new Formula.Power(Seq(Open, new Formula.Negate(D(1)), Close), m),
                CastQ(Seq(Open, Add(m, D(3)), Close, Bang))),
            Multiply(D(2), CastQ(Add(m, D(1)))));
        var equality = new Formula.Relation(
            Subtract(CastQ(Call("T", n, Subtract(n, D(1)))),
                CastQ(Call("T", n, Subtract(n, D(2))))),
            FormulaRelationOperator.Equal, new Formula.Absolute(Call("b", Subtract(n, D(4)))));
        var universal = All("n", Nat(), new Formula.Logic(
            new Formula.Relation(D(4), FormulaRelationOperator.LessThanOrEqual, n),
            FormulaLogicOperator.Implies, equality));
        return declaration switch
        {
            "b" => All("m", Nat(), new Formula.Relation(Call("b", m),
                FormulaRelationOperator.Equal, value)),
            "claim" => new Formula.Logic(F.Id("claim"), FormulaLogicOperator.Iff, universal),
            "result" => new Formula.Not(F.Id("claim")),
            _ => throw new System.ArgumentException("Unknown declaration", nameof(declaration))
        };
    }

    private static Formula Nat() => new Formula.NamedConstant(FormulaIdentifier.Create("Nat"));
    private static Formula CastQ(Formula value) => Call("castQ", value);
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
}
