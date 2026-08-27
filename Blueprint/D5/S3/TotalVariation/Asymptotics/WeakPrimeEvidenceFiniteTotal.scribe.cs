using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.TotalVariation.Asymptotics;

internal sealed class WeakPrimeEvidenceFiniteTotalDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Prime-indexed weak Bernoulli coordinates have positive, vanishing, summable "
            + "negative-log affinity evidence.",
        H("Weak Prime Evidence Has Finite Total"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("weak-prime-evidence-finite-total"),
                DeclarationHandle.Create(
                    "D5/S3/TotalVariation/Asymptotics/WeakPrimeEvidenceFiniteTotal."
                        + "weak_prime_evidence_finite_total"),
                H("Infinitely many weak coordinates can have finite total evidence"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For each prime p, take the canonical symmetric Bernoulli pair with "
                            + "opposite biases p to the power minus two. Its Bhattacharyya "
                            + "affinity is strictly below one, so its negative logarithm is "
                            + "positive.")),
                    Paragraph(Text(
                        "The frozen second-order expansion bounds the remainder by a constant "
                            + "multiple of p to the power minus eight. The leading term is a "
                            + "multiple of p to the power minus four. Both prime-power series "
                            + "are summable, and summability also forces the evidence terms to "
                            + "vanish along the cofinite filter."))),
                DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula prime = F.Id("p");
        Formula primes = Seq(Operatorname, Grp(F.Id("NatPrimes")));
        Formula evidence = Evidence(prime);
        Formula evidenceFamily = Seq(
            Open, prime, Sp, Mapsto, Sp, evidence, Close);
        Formula positive = Seq(
            Forall, Sp, prime, Colon, Sp, primes, Comma, Sp,
            D(0), Sp, Lt, Sp, evidence);
        Formula summable = new Formula.Apply(F.Id("Summable"), [evidenceFamily]);
        Formula vanishing = Call(
            "Tendsto", evidenceFamily, F.Id("cofinite"), Call("nhds", D(0)));
        return Disp(new Formula.Logic(
            Grp(positive),
            FormulaLogicOperator.And,
            new Formula.Logic(summable, FormulaLogicOperator.And, vanishing)));
    }

    private static Formula Evidence(Formula prime)
    {
        Formula delta = new Formula.Power(prime, Grp(Seq(Minus, D(2))));
        Formula positiveLaw = Call("positiveBiasLaw", delta);
        Formula negativeLaw = Call("negativeBiasLaw", delta);
        Formula affinity = Call("bhattacharyya", positiveLaw, negativeLaw);
        return Seq(Minus, Log, Open, affinity, Close);
    }
}
