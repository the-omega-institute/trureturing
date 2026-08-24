using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.ArithmeticTomography;

internal sealed class FinitePrimeInformationBudgetDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        Formula primeSet = F.Id("S");
        Formula precision = Kappa;
        Formula window = F.Id("N");
        Formula prime = Seq(F.Id("p"));
        Formula primes = Seq(Operatorname, Grp(F.Id("NatPrimes")));
        Formula positiveNaturals = Seq(Operatorname, Grp(F.Id("PNat")));
        Formula finitePrimeSet = Seq(
            Operatorname, Grp(F.Id("Finset")), Open, primes, Close);
        Formula precisionAtPrime = Seq(precision, Open, prime, Close);
        Formula primePower = new Formula.Power(prime, precisionAtPrime);
        Formula product = Seq(
            Prod, Underscore, Grp(prime, InMacro, Sp, primeSet), Sp, primePower);
        Formula logWindow = Seq(
            Operatorname, Grp(F.Id("logb")), Open, D(2), Comma, Sp, window, Close);
        Formula logPrime = Seq(
            Operatorname, Grp(F.Id("logb")), Open, D(2), Comma, Sp, prime, Close);
        Formula sum = Seq(
            Sum, Underscore, Grp(prime, InMacro, Sp, primeSet), Sp,
            precisionAtPrime, Sp, logPrime);
        Formula statement = Disp(Seq(
            Forall, Sp, primeSet, Colon, Sp, finitePrimeSet, Comma, Sp,
            precision, Colon, Sp, primes, Sp, To, Sp, positiveNaturals, Comma, Sp,
            window, InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma,
            RowBreak, Grp(), D(0), Sp, Lt, Sp, window, Sp, Land, Sp,
            window, Sp, Leq, Sp, product, Sp, Rightarrow, Sp,
            RowBreak, Grp(), logWindow, Sp, Leq, Sp, sum, Dot));

        return DocumentDefinition.Create(ScribeNode.Create(
            "A complete finite prime-power readout meets the exact base-two information budget.",
            H("Finite Prime Information Budget"),
            Blocks(
                Describe.Lean(
                    DescribeId.Create("finite-prime-information-budget"),
                    DeclarationHandle.Create(
                        "D5/S3/Observer/ArithmeticTomography/"
                            + "FinitePrimeInformationBudget."
                            + "finite_prime_information_budget"),
                    H("The prime-power precision sum bounds the window information"),
                    StatementSource.FromAuthor(statement),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text(
                            "Let S be a finite set whose elements carry primality proofs, and "
                                + "let kappa assign every prime a positive natural precision. "
                                + "For a positive window size N, the public completeness premise "
                                + "states that N does not exceed the selected prime-power product.")),
                        Paragraph(Text(
                            "The base-two logarithm is increasing on positive reals. Applying it "
                                + "to the completeness bound and expanding the logarithm of the "
                                + "finite product gives the sum of kappa(p) times logb(2,p), which "
                                + "is therefore at least logb(2,N).")),
                        Paragraph(Text(
                            "The proof directly applies Real.logb_le_logb, Real.log_prod, and "
                                + "Real.log_pow from the pinned library. Prime and positive-precision "
                                + "restrictions are encoded in the public carriers rather than "
                                + "introduced by auxiliary definitions."))),
                    DescribeRole.Theorem))));
    }
}
