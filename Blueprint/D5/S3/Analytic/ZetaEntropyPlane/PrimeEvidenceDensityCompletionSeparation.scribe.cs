using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.ZetaEntropyPlane;

internal sealed class PrimeEvidenceDensityCompletionSeparationDocument
    : IScribeDocumentDefinition
{
    private const string DeclarationPrefix =
        "D5/S3/Analytic/ZetaEntropyPlane/PrimeEvidenceDensityCompletionSeparation.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Prime-coordinate count and cumulative evidence have distinct convergence behaviors.",
        H("Prime Count And Evidence Completion Separate"),
        Blocks(Describe.Lean(
            DescribeId.Create("prime-evidence-density-completion-separation"),
            DeclarationHandle.Create(DeclarationPrefix
                + "prime_evidence_density_completion_separation"),
            H("Coordinate count does not determine cumulative completion"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The prime index is infinite, yet the explicit inverse-square weak "
                        + "Bernoulli evidence family is positive, summable, and vanishes "
                        + "along the cofinite filter.")),
                Paragraph(Text(
                    "The prime support has zero natural counting ratio while its reciprocal "
                        + "evidence diverges. Full and empty support witnesses then make the "
                        + "density-versus-summability inequivalence explicit."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula primes = Call("NatPrimes");
        Formula prime = F.Id("p");
        Formula delta = new Formula.Power(prime, Grp(Seq(Minus, D(2))));
        Formula positiveLaw = Call("positiveBiasLaw", delta);
        Formula negativeLaw = Call("negativeBiasLaw", delta);
        Formula evidence = Seq(
            Minus, Log, Open, Call("bhattacharyya", positiveLaw, negativeLaw), Close);
        Formula evidenceFamily = Seq(Open, prime, Sp, Mapsto, Sp, evidence, Close);
        Formula positive = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [new Formula.BoundVariable(FormulaIdentifier.Create("p"), primes)],
            Seq(D(0), Sp, Lt, Sp, evidence));
        Formula summable = new Formula.Apply(F.Id("Summable"), [evidenceFamily]);
        Formula vanishing = Call(
            "Tendsto", evidenceFamily, F.Id("cofinite"), Call("nhds", D(0)));
        Formula weak = And(
            Call("Infinite", primes), And(positive, And(summable, vanishing)));

        Formula primeSupport = F.Id("primeNaturals");
        Formula sparse = And(
            Call("Tendsto", CountingRatio(primeSupport), F.Id("atTop"), Call("nhds", D(0))),
            Not(IsSummable(primeSupport, D(1))));
        Formula full = And(
            ForallPrimeIn(primeSupport), IsSummable(primeSupport, D(2)));
        Formula empty = And(
            Call("Tendsto", CountingRatio(Emptyset), F.Id("atTop"), Call("nhds", D(0))),
            IsSummable(Emptyset, D(1)));
        return Disp(And(weak, And(sparse, And(full, empty))));
    }

    private static Formula ForallPrimeIn(Formula support)
    {
        Formula primes = Call("NatPrimes");
        Formula prime = F.Id("p");
        return new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [new Formula.BoundVariable(FormulaIdentifier.Create("p"), primes)],
            Seq(prime, Sp, InMacro, Sp, support));
    }

    private static Formula CountingRatio(Formula support) =>
        new Formula.Apply(F.Id("naturalCountingRatio"), [support]);

    private static Formula EvidenceFamily(Formula support, Formula exponent) =>
        new Formula.Apply(F.Id("restrictedPrimeEvidence"), [support, exponent]);

    private static Formula IsSummable(Formula support, Formula exponent) =>
        new Formula.Apply(F.Id("Summable"), [EvidenceFamily(support, exponent)]);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula Not(Formula value) =>
        Seq(Neg, Sp, value);

    private static Formula Emptyset => F.Seq(F.Emptyset);
}
