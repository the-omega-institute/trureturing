using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.ZetaEntropyPlane;

internal sealed class ZeroDensityReciprocalPrimeSetDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Analytic/ZetaEntropyPlane/ZeroDensityReciprocalPrimeSet."
            + "zero_density_divergent_reciprocal_prime_set";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A zero-relative-density prime set can carry divergent reciprocal mass and, "
            + "under the product-law criterion, statistical completion.",
        H("Zero-Density Reciprocal Prime Evidence"),
        Blocks(Describe.Lean(
            DescribeId.Create("zero-density-divergent-reciprocal-prime-set"),
            DeclarationHandle.Create(Declaration),
            H("Sparse primes can retain divergent reciprocal evidence"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "There is one subset of the primes whose relative counting ratio tends "
                        + "to zero while its reciprocal-prime family is not summable.")),
                Paragraph(Text(
                    "The Lean witness is a classical, noncomputable selection: its block "
                        + "endpoints use Nat.find on analytic existence of enough reciprocal "
                        + "mass. It is not a computable enumeration of the subset.")),
                Paragraph(Text(
                    "For the same subset, evidence asymptotic to one over p yields mutually "
                        + "singular transcript laws under the singularity-versus-divergent-"
                        + "energy equivalence from the source's Theorem 233.1. No separate "
                        + "absolute-continuity-versus-summability premise is assumed."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula support = F.Id("S");
        Formula prime = F.Id("p");
        Formula evidence = F.Id("e");
        Formula lawP = F.Id("mu");
        Formula lawQ = F.Id("nu");
        Formula reciprocal = Seq(
            Open, prime, Colon, Sp, support, Sp, Mapsto, Sp,
            new Formula.Fraction(D(1), prime), Close);
        Formula restrictedEvidence = Seq(
            Open, prime, Colon, Sp, support, Sp, Mapsto, Sp,
            evidence, Open, prime, Close, Close);

        Formula densityZero = Seq(
            Lim, Underscore, Grp(F.Id("n"), To, Infty), Sp,
            Call("relativePrimeCountingRatio", support, F.Id("n")), Sp, Eq, Sp, D(0));
        Formula reciprocalDiverges = Seq(
            Neg, Sp, Call("Summable", reciprocal));
        Formula asymptoticEvidence = Call(
            "IsTheta", restrictedEvidence, F.Id("cofinite"), reciprocal);
        Formula completion = Seq(lawP, Sp, Perp, Sp, lawQ);
        Formula evidenceDiverges = Seq(Neg, Sp, Call("Summable", evidence));
        Formula singularityCriterion = new Formula.Logic(
            completion,
            FormulaLogicOperator.Iff,
            evidenceDiverges);
        Formula conditionalCompletion = Seq(
            Forall, Sp, evidence, Comma, Sp, lawP, Comma, Sp, lawQ, Comma, Sp,
            new Formula.Logic(
                singularityCriterion,
                FormulaLogicOperator.Implies,
                new Formula.Logic(
                    asymptoticEvidence,
                    FormulaLogicOperator.Implies,
                    completion)));
        Formula leaves = new Formula.Logic(
            densityZero,
            FormulaLogicOperator.And,
            new Formula.Logic(
                reciprocalDiverges,
                FormulaLogicOperator.And,
                conditionalCompletion));

        return Disp(Seq(
            Exists, Sp, support, Sp, Subseteq, Sp, F.Id("Primes"), Comma, Sp,
            leaves));
    }
}
