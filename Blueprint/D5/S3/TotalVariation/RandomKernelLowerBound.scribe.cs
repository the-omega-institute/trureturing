using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.TotalVariation;

internal sealed class RandomKernelLowerBoundDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Sharp minimax obstruction from diagonal subset sources.",
        H("The stochastic-kernel minimax radius"),
        Blocks(
            Paragraph(Text(
                "Use the full source space Option(Fin d times Fin d), its independent "
                + "completion, the half-L1 total variation, and the real supremum "
                + "worstError from RandomKernelExtremum. A matrix K is column stochastic "
                + "when every entry is nonnegative and every output column sums to one. "
                + "For a finite label subset S, matchingLaw(S) is uniform on the "
                + "diagonal active cells indexed by S, with zero blocking mass. "
                + "The event matchingEvent(S) consists of the off-diagonal active "
                + "cells with both labels in S.")),
            Paragraph(Text(
                "The lower proof uses only diagonal subset sources. For each input "
                + "diagonal cell, the point-source test bounds output mass on the "
                + "full off-diagonal event by e. For each k-element subset S, its "
                + "uniform diagonal law has completion event mass (k-1)/k. Summing "
                + "all diagonal input columns defines a nonnegative zero-diagonal "
                + "weight w with induced k-subset weight at least (k-1)-k*e. "
                + "Deleting each vertex counts each off-diagonal ordered pair "
                + "card-2 times. Induction propagates the subset lower bound to "
                + "the full d-set, whose weight is at most d*e by the point tests. "
                + "This gives (d-1)(k-1)<=k(d+k-2)e for every 2<=k<=d. "
                + "Taking the finite maximum gives rho(d)<=e, even when active "
                + "mass can leak into the blocking state.")),
            Describe.Lean(
                DescribeId.Create("stochastic-kernel-minimax"),
                DeclarationHandle.Create(
                    "D5/S3/TotalVariation/RandomKernelLowerBound.stochastic_kernel_minimax"),
                H("An attained global minimum"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every natural d>=2, rho(d) is the least element of the set "
                    + "of worstError(K) over all column-stochastic kernels K. The "
                    + "explicit optimalKernel(d) belongs to that class and realizes "
                    + "the least element. Completion preserves nonnegativity and "
                    + "total mass, so total variation is at most one and its real "
                    + "supremum is well-defined as an upper bound on every source "
                    + "error. Applying the sharp uniform lower bound to that "
                    + "supremum closes the lower half of the minimax assertion."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("maximizing-matching-attains"),
                DeclarationHandle.Create(
                    "D5/S3/TotalVariation/RandomKernelLowerBound.maximizing_matching_attains"),
                H("Every maximizing diagonal subset is extremal"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every natural d>=2 and every subset S of Fin d of cardinal "
                    + "k>=2 satisfying beta(d)=c(d,k), the uniform diagonal source "
                    + "matchingLaw(S) has error exactly rho(d) under optimalKernel(d). "
                    + "Its completed mass on matchingEvent(S) is (k-1)/k, while "
                    + "the kernel output puts (k-1)beta(d) there. The maximizing "
                    + "identity makes their difference rho(d). The event lower "
                    + "bound and the full-source upper bound give equality."))),
                DescribeRole.Theorem))));
}
