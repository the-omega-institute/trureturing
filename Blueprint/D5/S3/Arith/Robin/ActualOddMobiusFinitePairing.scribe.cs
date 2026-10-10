using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin;

internal sealed class ActualOddMobiusFinitePairingDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual odd Mobius coefficients give exact finite dyadic reconstruction and clipped kernel pairing with its terminal payment.",
        H("Actual Odd Mobius Finite Pairing"),
        Blocks(
            Paragraph(Text(
                "Use the actual arithmetic Mobius function mu, the full positive "
                + "prefix M(N)=sum from 1 to N of mu(n), and its odd restriction "
                + "O(N). Every kernel P is a real-valued function on the actual "
                + "integer inputs, with J(n)=P(n)-P(n+1).")),
            Describe.Lean(
                DescribeId.Create("actual-odd-mobius-finite-pairing"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/ActualOddMobiusFinitePairing.result"),
                H("The exact odd pairing and terminal remainder"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every natural cutoff N, M(N)=O(N)-O(N/2), where "
                        + "natural division supplies the floor. Iteration terminates "
                        + "and gives O(N)=sum over all exponents a with 2^a<=N "
                        + "of M(N/2^a), including the empty sum at N=0.")),
                    Paragraph(Text(
                        "For every real-valued kernel P and cutoff N, the exact "
                        + "sum of M(n)*J(n) from 1 to N equals the sum over odd "
                        + "m from 1 to N of mu(m)*(P(m)-P(min(2*m,N+1))). "
                        + "The inclusive cutoff, original unit source and final "
                        + "N+1 boundary are retained literally.")),
                    Paragraph(Text(
                        "Subtracting the untruncated odd pairing "
                        + "sum mu(m)*(P(m)-P(2*m)) gives exactly the terminal "
                        + "sum over odd N/2<m<=N of "
                        + "mu(m)*(P(2*m)-P(N+1)). If 2*m=N+1 its bracket is "
                        + "exactly zero. Both even and odd cutoffs are covered.")),
                    Paragraph(Text(
                        "Mathlib supplies the actual Mobius function, "
                        + "multiplicativity, squarefree vanishing, prime value, "
                        + "finite sum algebra and telescoping. The consumed "
                        + "parity coefficient and multiples bijection specialize "
                        + "the primeDifference supplier inside the existing "
                        + "FibonacciAtomic.MertensBoundary proof to prime 2 and "
                        + "modulus 1. The finite clipped pairing and terminal "
                        + "payment implement actual-prefix theory section 453.")),
                    Paragraph(Text(
                        "These are finite identities that specialize directly to "
                        + "the original factorial-tail kernel. Passing to an infinite "
                        + "odd pairing requires a separate vanishing terminal estimate; "
                        + "no convergence, critical tail bound or RH conclusion is asserted."))),
                DescribeRole.Theorem))));
}
