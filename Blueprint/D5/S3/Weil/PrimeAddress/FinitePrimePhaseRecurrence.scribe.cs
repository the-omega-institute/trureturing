using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.PrimeAddress;

internal sealed class FinitePrimePhaseRecurrenceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every finite set of prime phases returns arbitrarily close to coherent phase.",
        H("Finite Prime Phase Recurrence"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("finite-prime-phase-recurrence"),
                DeclarationHandle.Create(
                    "D5/S3/Weil/PrimeAddress/FinitePrimePhaseRecurrence."
                    + "finite_prime_phase_recurrence"),
                H("Finite prime phases recur above every bound"),
                StatementSource.FromAuthor(RecurrenceStatement()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Compactness of the finite product of unit circles gives a convergent "
                    + "subsequence of sampled prime-phase vectors. Quotients of consecutive "
                    + "subsequence terms converge to the coherent phase. Sampling with a step "
                    + "larger than the requested bound makes the resulting recurrence time "
                    + "larger than that bound."))),
                DescribeRole.Theorem)),
        []));

    private static Formula RecurrenceStatement()
    {
        var primes = F.Id("P");
        var prime = F.Id("p");
        var bound = F.Id("B");
        var phase = Seq(
            Exp, Open, F.Id("i"), Sp, Xi, Sp, Log, Sp, prime, Close);
        var phaseError = new Formula.Norm(Seq(phase, Sp, Minus, Sp, D(1)));

        return Disp(Seq(
            Forall, Sp, primes, Colon, Sp,
            Call("Finset", F.Id("Primes")), Comma, Sp,
            Varepsilon, Comma, Sp, bound, Sp, InMacro, Sp, Mathbb, Grp(F.Id("R")), Comma,
            RowBreak, Grp(),
            D(0), Sp, Lt, Sp, Varepsilon, Sp, Rightarrow, Sp,
            Exists, Sp, Xi, Sp, InMacro, Sp, Mathbb, Grp(F.Id("R")), Comma, Sp,
            bound, Sp, Lt, Sp, Xi, Sp, Land, Sp,
            Forall, Sp, prime, Sp, InMacro, Sp, primes, Comma, Sp,
            phaseError, Sp, Lt, Sp, Varepsilon));
    }
}
