using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.PrimeProducts;

internal sealed class FiniteOffsetSingularSeriesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Complete blocking is a finite prime check; the singular series is a convergent "
            + "product of the local correlation factors over every prime.",
        H("Finite Offset Singular Series"),
        Blocks(Describe.Lean(
            DescribeId.Create("finite-offset-blocking-and-singular-series"),
            DeclarationHandle.Create(
                "D5/S3/Analytic/PrimeProducts/FiniteOffsetSingularSeries."
                    + "finite_offset_blocking_and_singular_series"),
            H("Finite blocking and the full numerical product"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The finite set H contains integer offsets. localResidueCount(H,p) "
                        + "counts the image of h mapped to minus h in ZMod p. "
                        + "The displayed lambda is offsetLocalFactor(H), and its tprod "
                        + "is offsetSingularSeries(H); both use the full prime index.")),
                Paragraph(Text(
                    "The frozen residue criterion supplies the two blocking clauses. "
                        + "Beyond the maximum distance between offsets, the residue map "
                        + "is injective. An inductive quadratic binomial remainder bound "
                        + "then bounds the absolute local-factor deviation by C divided "
                        + "by p squared, where C depends only on H.")),
                Paragraph(Text(
                    "Summability of these deviations gives HasProd at the displayed "
                        + "all-prime product. Neither admissibility nor nonemptiness is "
                        + "assumed: a blocked configuration may have a zero local factor."))),
            DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula Relation(Formula left, FormulaRelationOperator operation, Formula right) =>
        new Formula.Relation(left, operation, right);

    private static Formula ForPrime(Formula body) => new Formula.Bind(
        FormulaQuantifier.ForAll, FormulaIdentifier.Create("p"), F.Id("NatPrimes"), body);

    private static Formula TheoremFormula()
    {
        Formula offsets = F.Id("H");
        Formula size = F.Id("k");
        Formula prime = F.Id("p");
        Formula cardinality = Call("card", offsets);
        Formula count = Call("localResidueCount", offsets, prime);
        Formula bound = ForPrime(Implies(
            Relation(size, FormulaRelationOperator.LessThan, prime),
            And(Relation(count, FormulaRelationOperator.LessThanOrEqual, size),
                Relation(count, FormulaRelationOperator.LessThan, prime))));
        Formula allPrimes = ForPrime(Relation(count, FormulaRelationOperator.LessThan, prime));
        Formula smallPrimes = ForPrime(Implies(
            Relation(prime, FormulaRelationOperator.LessThanOrEqual, size),
            Relation(count, FormulaRelationOperator.LessThan, prime)));
        Formula criterion = new Formula.Logic(allPrimes, FormulaLogicOperator.Iff, smallPrimes);
        Formula numerator = new Formula.Binary(
            D(1), FormulaBinaryOperator.Subtract, new Formula.Fraction(count, prime));
        Formula denominator = new Formula.Power(
            new Formula.Binary(D(1), FormulaBinaryOperator.Subtract, new Formula.Fraction(D(1), prime)),
            cardinality);
        Formula factors = Seq(Open, prime, Colon, Sp, F.Id("NatPrimes"), Sp, Mapsto, Sp,
            new Formula.Fraction(numerator, denominator), Close);
        Formula convergence = Call("HasProd", factors, Call("tprod", factors));

        return Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                new Formula.BoundVariable(FormulaIdentifier.Create("H"), Call("Finset", new Formula.Integers())),
                new Formula.BoundVariable(FormulaIdentifier.Create("k"), Seq(Mathbb, Grp(F.Id("N")))),
            ],
            Implies(Relation(cardinality, FormulaRelationOperator.Equal, size),
                And(bound, And(criterion, convergence)))));
    }
}
