using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.FiniteSieve;

internal sealed class SieveRamanujanDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SieveRamanujan.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Ramanujan sums and additive character orthogonality identify finite sieve frequencies.",
        H("Ramanujan expansion of a finite sieve"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("sieve-character-add"),
                DeclarationHandle.Create(Prefix + "sieve_character_add"),
                H("Addition of phases"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The positive phase exp(2 pi i t) sends addition of real frequencies to multiplication. This identity splits the residue and shift phases in weighted sieve sums."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("sieve-character-orthogonality"),
                DeclarationHandle.Create(Prefix + "sieve_character_orthogonality"),
                H("The uniform character average"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Let each positive q_i divide Q. The average over x modulo Q of exp(2 pi i x sum_i r_i/q_i) is one when the rational total frequency is an integer and zero otherwise. Writing the frequency over Q reduces the statement to the primitive additive character on ZMod Q. Its trivial-character sum is Q, cancelling the uniform-average denominator. There is no conjugation or additional Q factor."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("sieve-centered-ramanujan-expansion"),
                DeclarationHandle.Create(Prefix + "sieve_centered_ramanujan_expansion"),
                H("The centred Ramanujan expansion"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For squarefree positive Q, write P=Q/phi(Q). The function P times the indicator that x+d is coprime to Q, minus one, equals the sum over nontrivial divisors q of Q of mu(q)c_q(x.val+d)/phi(q). Multiplicativity gives the prime-factor expansion. At a prime p the Ramanujan sum is p-1 if p divides the argument and -1 otherwise; the resulting product is the reduced-residue indicator times P. The divisor q=1 has coefficient and Ramanujan sum both equal to one, so centring removes exactly this term. Natural shifts including zero and reduction of x+d modulo Q are retained. This pointwise identity supplies the frequencies for weighted moment expansions."))),
                DescribeRole.Theorem))));
}
