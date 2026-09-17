using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Partitions;

internal sealed class StephanEvenProductPartitionRecurrenceDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S1/Recurrence/Partitions/StephanEvenProductPartitionRecurrence.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Recurrence/perry2004a091915");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The greatest even product of partition parts triples when the total increases by three.",
        H("Stephan's Maximum Even Partition-Product Recurrence"),
        Blocks(
            Paragraph(Text(
                "In the formulas, partitionProducts(n) is the family of products of the "
                    + "parts of partitions of n, while evenPartitionProducts(n) is its "
                    + "subfamily of even products. IsGreatest records both attainment and "
                    + "an upper bound for every member of the corresponding family.")),
            Describe.Lean(
                DescribeId.Create("a091915-classical-maximum-product"),
                DeclarationHandle.Create(Prefix + "classicalMaximumProduct"),
                H("The unconstrained maximum partition product"),
                StatementSource.FromAuthor(ClassicalMaximumProductFormula()),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "The values at totals zero through four are 1, 1, 2, 3, and 4. "
                        + "Thereafter the recurrence removes three from the total and "
                        + "multiplies the value by three. This is the classical A000792 "
                        + "maximum without a parity constraint."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("a091915-classical-maximum-is-greatest"),
                DeclarationHandle.Create(Prefix + "classicalMaximumProduct_isGreatest"),
                H("The classical unconstrained extremal theorem"),
                StatementSource.FromAuthor(ClassicalGreatestFormula()),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "For every natural total n, classicalMaximumProduct(n) is attained by "
                        + "a partition of n and bounds the product of every partition of n. "
                        + "The theorem is stated publicly as the unconstrained extremal "
                        + "result used by the parity-constrained argument."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("a091915-even-product-recurrence"),
                DeclarationHandle.Create(Prefix + "result"),
                H("Stephan's even-product recurrence"),
                StatementSource.FromAuthor(ResultFormula()),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "For n greater than six, there is a greatest even partition product a "
                        + "at total n, and 3a is the greatest even partition product at n+3. "
                        + "For residues two and one modulo three the unconstrained optima "
                        + "2 times a power of three and 4 times a power of three are even. "
                        + "For residue zero the unconstrained power of three is odd, so the "
                        + "even constraint binds and the sharp value is 8 times a power of "
                        + "three. Each branch is multiplied by three after adding three."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create(
                        "oeis-a091915-stephan-even-product-partition-recurrence"),
                    ResolutionKind.Proved)))));

    private static Formula ClassicalMaximumProductFormula()
    {
        Formula n = F.Id("n");
        return Disp(And(
            Equal(Maximum(D(0)), D(1)),
            Equal(Maximum(D(1)), D(1)),
            Equal(Maximum(D(2)), D(2)),
            Equal(Maximum(D(3)), D(3)),
            Equal(Maximum(D(4)), D(4)),
            ForAll([Bound("n")],
                Equal(Maximum(Add(n, D(5))), Multiply(D(3), Maximum(Add(n, D(2))))))));
    }

    private static Formula ClassicalGreatestFormula()
    {
        Formula n = F.Id("n");
        return Disp(ForAll([Bound("n")],
            Call("IsGreatest", Call("partitionProducts", n), Maximum(n))));
    }

    private static Formula ResultFormula()
    {
        Formula n = F.Id("n"), a = F.Id("a");
        return Disp(ForAll([Bound("n")],
            Implies(
                Less(D(6), n),
                Exists([Bound("a")],
                    And(
                        Call("IsGreatest", Call("evenPartitionProducts", n), a),
                        Call("IsGreatest", Call("evenPartitionProducts", Add(n, D(3))),
                            Multiply(D(3), a)))))));
    }

    private static Formula Maximum(Formula n) => Call("classicalMaximumProduct", n);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. arguments]);

    private static Formula.BoundVariable Bound(string name) =>
        new(FormulaIdentifier.Create(name), Naturals());

    private static Formula Naturals() =>
        new Formula.NamedConstant(FormulaIdentifier.Create("Nat"));

    private static Formula ForAll(Formula.BoundVariable[] variables, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables], body);

    private static Formula Exists(Formula.BoundVariable[] variables, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.Exists, [.. variables], body);

    private static Formula And(Formula first, params Formula[] rest)
    {
        Formula result = rest[^1];
        for (int i = rest.Length - 1; i >= 0; i--)
        {
            Formula left = i == 0 ? first : rest[i - 1];
            result = new Formula.Logic(
                Parenthesized(left), FormulaLogicOperator.And, Parenthesized(result));
        }
        return result;
    }

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(
            Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula Less(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);

    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);

    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
}
