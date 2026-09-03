using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.PrimeProducts;

internal sealed class FiniteLocalResidueBlockingCriterionDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Analytic/PrimeProducts/FiniteLocalResidueBlockingCriterion."
            + "finite_local_residue_blocking_criterion";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finite offset set can cover every residue class only at primes no larger "
            + "than the number of offsets.",
        H("Finite Local Residue Blocking Criterion"),
        Blocks(Describe.Lean(
            DescribeId.Create("finite-local-residue-blocking-criterion"),
            DeclarationHandle.Create(Declaration),
            H("Only finitely many primes can completely block an offset set"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "For a finite set H of integer offsets, the local residue set modulo p "
                        + "is constructed as the image of h mapped to minus h in ZMod p. "
                        + "The local residue count nu_p(H) is its cardinality.")),
                Paragraph(Text(
                    "The image has at most the cardinality k of H. Thus every prime p "
                        + "larger than k has nu_p(H) strictly below p and cannot be a "
                        + "complete residue obstruction.")),
                Paragraph(Text(
                    "It follows that admissibility over all primes is equivalent to the "
                        + "same inequality restricted to primes at most k. This reduction "
                        + "concerns complete blocking only; the later numerical singular "
                        + "series retains its all-prime index."))),
            DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula TheoremFormula()
    {
        Formula offsets = F.Id("H");
        Formula size = F.Id("k");
        Formula prime = F.Id("p");
        Formula integers = new Formula.Integers();
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));
        Formula primes = F.Id("NatPrimes");
        Formula residueCount = new Formula.Apply(
            new Formula.Subscript(Nu, prime),
            [offsets]);

        Formula cardinalityPremise = new Formula.Relation(
            new Formula.Absolute(offsets),
            FormulaRelationOperator.Equal,
            size);
        Formula largePrimeBound = new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("p"),
            primes,
            new Formula.Logic(
                new Formula.Relation(
                    size,
                    FormulaRelationOperator.LessThan,
                    prime),
                FormulaLogicOperator.Implies,
                new Formula.Logic(
                    new Formula.Relation(
                        residueCount,
                        FormulaRelationOperator.LessThanOrEqual,
                        size),
                    FormulaLogicOperator.And,
                    new Formula.Relation(
                        residueCount,
                        FormulaRelationOperator.LessThan,
                        prime))));
        Formula allPrimeAdmissible = new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("p"),
            primes,
            new Formula.Relation(
                residueCount,
                FormulaRelationOperator.LessThan,
                prime));
        Formula boundedPrimeAdmissible = new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("p"),
            primes,
            new Formula.Logic(
                new Formula.Relation(
                    prime,
                    FormulaRelationOperator.LessThanOrEqual,
                    size),
                FormulaLogicOperator.Implies,
                new Formula.Relation(
                    residueCount,
                    FormulaRelationOperator.LessThan,
                    prime)));

        return Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                new Formula.BoundVariable(
                    FormulaIdentifier.Create("H"),
                    Call("Finset", integers)),
                new Formula.BoundVariable(
                    FormulaIdentifier.Create("k"),
                    naturals),
            ],
            new Formula.Logic(
                cardinalityPremise,
                FormulaLogicOperator.Implies,
                new Formula.Logic(
                    largePrimeBound,
                    FormulaLogicOperator.And,
                    new Formula.Logic(
                        allPrimeAdmissible,
                        FormulaLogicOperator.Iff,
                        boundedPrimeAdmissible)))));
    }
}
