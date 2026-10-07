using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin;

internal sealed class PrimePrefixMobiusDirectedAbelDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual finite harmonic Mobius tail retains its complete anchored Abel identity and a one-sided lower budget from actual prefix differences.",
        H("Directed Abel Budgets for Actual Harmonic Mobius Prefixes"),
        Blocks(
            Paragraph(Text(
                "The harmonicPrefix H(N) is the inclusive positive sum of "
                + "Mathlib's actual Mobius coefficients mu(k)/k. "
                + "prefixDifference Q_D(n)=H(n)-H(D) retains the same lower "
                + "cutoff, and weightedTail S(D,M,b) sums mu(n)b(n)/n on "
                + "D<n<=M. The real weight b is arbitrary until the stated "
                + "order conditions are imposed.")),
            Describe.Lean(
                DescribeId.Create("prime-prefix-mobius-directed-abel"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/PrimePrefixMobiusDirectedAbel.result"),
                H("The complete finite identity and exact directed budgets"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every natural D<M and every real weight b, "
                        + "S=b(M)Q_D(M)+sum over D<n<=M-1 of "
                        + "(b(n)-b(n+1))Q_D(n). The terminal term is retained. "
                        + "At M=D+1 the inner sum is empty, leaving exactly "
                        + "the one actual Mobius summand. No infinite "
                        + "rearrangement or limiting argument is used.")),
                    Paragraph(Text(
                        "If b is nonnegative and antitone on [D+1,M], "
                        + "and every actual Q_D(n) for D<n<=M is at least "
                        + "-e with e>=0, then S>=-e*b(D+1). All coefficient "
                        + "increments in the anchored identity are nonnegative "
                        + "and their total, including the terminal coefficient, "
                        + "is exactly b(D+1). Only this one-sided lower "
                        + "prefix-difference bound is required.")),
                    Paragraph(Text(
                        "If instead every original prefix on the complete "
                        + "[D,M] satisfies abs(H(n))<=delta, the exact signed "
                        + "anchor remains available: delta+H(D)>=0 and "
                        + "S>=-(delta+H(D))*b(D+1). The assumption includes "
                        + "n=D, which pays nonnegativity of this budget. "
                        + "For H(D)<0 it is smaller than the coarse 2*delta "
                        + "budget. When the first weight is zero, the same "
                        + "nonnegative antitone conditions force the entire "
                        + "finite tail to be zero.")),
                    Paragraph(Text(
                        "Mathlib's existing Finset.sum_Ioc_by_parts and "
                        + "finite telescoping algebra are directly consumed. "
                        + "The private harmonic range adapter and telescoping "
                        + "proof are adapted from dbsanfte/RiemannGaussian, "
                        + "RiemannGaussian/MoebiusHarmonicMonotoneTail.lean at "
                        + "revision 24444671cee3bf643ff1307909b961a329372a9e, "
                        + "under Apache License Version 2.0. The one-sided "
                        + "comparison and exact anchor transport retain the "
                        + "literal Mobius objects. No mathematical priority "
                        + "claim is made for the classical Abel formula.")),
                    Paragraph(Text(
                        "The original Robin weight's identity, its actual "
                        + "nonnegative antitone window or complete variation, "
                        + "odd/full harmonic reconstruction, quantitative "
                        + "Gaussian prefix decay, infinite-tail acceptance "
                        + "and critical normalization remain separate "
                        + "obligations. This finite theorem proves neither "
                        + "the final Robin sign nor RH."))),
                DescribeRole.Theorem))));
}
