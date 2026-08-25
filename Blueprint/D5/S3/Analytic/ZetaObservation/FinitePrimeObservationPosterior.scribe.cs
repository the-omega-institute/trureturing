using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.ZetaObservation;

internal sealed class FinitePrimeObservationPosteriorDocument
    : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite prime observations freeze only the observed zeta coordinates.",
        H("Finite Prime Observation Posterior"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("finite-prime-observation-posterior"),
                DeclarationHandle.Create(
                    "D5/S3/Analytic/ZetaObservation/"
                        + "FinitePrimeObservationPosterior."
                        + "finite_prime_observation_posterior"),
                H("Finite prime observations preserve the unobserved posterior"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Fix a zeta exponent above one, a finite set of observed primes, "
                            + "and their exponent readings. Every finite exponent cylinder "
                            + "on a disjoint prime set is independent of the observed "
                            + "cylinder.")),
                    Paragraph(Text(
                        "For every nonzero integer realizing those readings, the observed "
                            + "prime powers form the known factor. The canonical quotient "
                            + "reconstructs the integer, is coprime to the product of the "
                            + "observed primes, and has the original exponent at every "
                            + "unobserved prime."))),
                DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula exponent = F.Id("s");
        Formula observed = F.Id("S");
        Formula reading = F.Id("k");
        Formula integer = F.Id("N");

        Formula domain = new Formula.Relation(
            F.D(1), FormulaRelationOperator.LessThan, exponent);
        Formula posterior = Call(
            "IndependentObservedAndUnobservedCylinders", exponent, observed, reading);
        Formula reconstruction = new Formula.Relation(
            integer,
            FormulaRelationOperator.Equal,
            Call(
                "Product",
                Call("observedPrimeFactor", observed, reading),
                Call("unobservedCofactor", observed, reading, integer)));
        Formula coprimality = Call(
            "CoprimeToObservedPrimeProduct", observed, reading, integer);
        Formula preservation = Call(
            "PreservesEveryUnobservedExponent", observed, reading, integer);
        Formula decomposition = new Formula.Logic(
            reconstruction,
            FormulaLogicOperator.And,
            new Formula.Logic(
                coprimality,
                FormulaLogicOperator.And,
                preservation));
        Formula conclusion = new Formula.Logic(
            posterior,
            FormulaLogicOperator.And,
            decomposition);

        return F.Disp(new Formula.Logic(
            domain,
            FormulaLogicOperator.Implies,
            conclusion));
    }
}
