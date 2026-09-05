using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.PrimeZeckendorf;

internal sealed class NoNaturalPrimeChoiceDocument : IScribeDocumentDefinition
{
    private const string DeclarationPrefix =
        "D5/S3/Analytic/PrimeZeckendorf/NoNaturalPrimeChoice.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every natural prime is moved by an explicit permutation of the prime type, so the "
            + "fully symmetric prime carrier has no globally distinguished element.",
        H("No Natural Prime Choice"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("no-prime-is-fixed-by-every-permutation"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "no_prime_is_fixed_by_every_permutation"),
                H("No prime is fixed by every prime permutation"),
                StatementSource.FromAuthor(NoFixedPrimeFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For an arbitrary natural prime p, choose three when p is two and "
                            + "choose two otherwise. The chosen prime differs from p in both "
                            + "cases, and swapping the two prime values gives a permutation "
                            + "that moves p.")),
                    Paragraph(Text(
                        "The construction is uniform over the selected prime. Thus the result "
                            + "rules out a common fixed point for the full permutation group; "
                            + "it does not merely exhibit one movable prime."))),
                DescribeRole.Theorem))));

    private static Formula NoFixedPrimeFormula()
    {
        Formula primes = Seq(F.Id("Nat"), Dot, F.Id("Primes"));
        Formula primePermutations = Seq(
            F.Id("Equiv"), Dot,
            Operatorname, Grp(F.Id("Perm")), Open, primes, Close);
        Formula prime = F.Id("p");
        Formula relabel = F.Id("relabel");

        return Disp(Seq(
            Forall, Sp, prime, Colon, Sp, primes, Comma, Sp,
            Exists, Sp, relabel, Colon, Sp, primePermutations, Comma, Sp,
            relabel, Open, prime, Close, Sp, Neq, Sp, prime, Dot));
    }
}
