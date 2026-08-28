using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.PrimeProducts;

internal sealed class PrimePrecisionEntropyContractionDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Analytic/PrimeProducts/PrimePrecisionEntropyContraction."
            + "prime_precision_entropy_contraction";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Each added prime-exponent digit contracts unresolved entropy exactly.",
        H("Prime Precision Entropy Contraction"),
        Blocks(Describe.Lean(
            DescribeId.Create("prime-precision-entropy-contraction"),
            DeclarationHandle.Create(Declaration),
            H("One precision step has the exact prime contraction factor"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Fix a zeta parameter above one and a prime. The channel law is the "
                        + "canonical geometric prime-exponent probability mass function.")),
                Paragraph(Text(
                    "At each precision, filter the channel on the unresolved tail, translate "
                        + "the conditional law back to zero, and weight its entropy by the "
                        + "tail probability.")),
                Paragraph(Text(
                    "Geometric memorylessness identifies the translated conditional law with "
                        + "the original channel. The tail mass is the corresponding prime ratio "
                        + "raised to the precision, giving both displayed levels and their exact "
                        + "one-step contraction."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula parameter = F.Id("s");
        Formula prime = F.Id("p");
        Formula precision = F.Id("k");
        Formula value = F.Id("v");
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));
        Formula reals = Seq(Mathbb, Grp(F.Id("R")));
        Formula primes = Seq(Operatorname, Grp(F.Id("Primes")));
        Formula channel = Call("primeExponentPMF", parameter, prime);
        Formula ratio = new Formula.Power(
            Seq(prime),
            Seq(Minus, parameter));
        Formula sourceEntropy = Call("H", channel);

        Formula ResidualEntropy(Formula depth)
        {
            Formula tail = new Formula.SetBuilder(
                new Formula.Relation(
                    value,
                    FormulaRelationOperator.GreaterThanOrEqual,
                    depth),
                value,
                naturals);
            Formula shifted = Seq(
                value,
                Sp,
                Mapsto,
                Sp,
                value,
                Sp,
                Minus,
                Sp,
                Seq(Open, depth, Close));
            Formula residualLaw = Call("map", shifted, Call("filter", channel, tail));
            Formula tailProbability = Call("Pr", channel, tail);
            return Multiply(tailProbability, Call("H", residualLaw));
        }

        Formula RatioPower(Formula exponent) => new Formula.Power(
            Seq(Open, ratio, Close),
            Seq(exponent));

        Formula successor = Add(precision, D(1));
        Formula atPrecision = new Formula.Relation(
            ResidualEntropy(precision),
            FormulaRelationOperator.Equal,
            Multiply(RatioPower(precision), sourceEntropy));
        Formula atSuccessor = new Formula.Relation(
            ResidualEntropy(successor),
            FormulaRelationOperator.Equal,
            Multiply(RatioPower(successor), sourceEntropy));
        Formula contraction = new Formula.Relation(
            ResidualEntropy(successor),
            FormulaRelationOperator.Equal,
            Multiply(ratio, ResidualEntropy(precision)));
        Formula conclusion = new Formula.Logic(
            atPrecision,
            FormulaLogicOperator.And,
            new Formula.Logic(atSuccessor, FormulaLogicOperator.And, contraction));
        Formula parameterBound = new Formula.Relation(
            D(1),
            FormulaRelationOperator.LessThan,
            parameter);

        return Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                new Formula.BoundVariable(
                    FormulaIdentifier.Create("s"),
                    reals),
                new Formula.BoundVariable(
                    FormulaIdentifier.Create("p"),
                    primes),
                new Formula.BoundVariable(
                    FormulaIdentifier.Create("k"),
                    naturals),
            ],
            new Formula.Logic(parameterBound, FormulaLogicOperator.Implies, conclusion)));
    }

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(F.Id(name), [.. arguments]);
}
