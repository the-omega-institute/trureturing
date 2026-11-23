using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Recovery;

internal sealed class QubitGibbsDeficitDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Quantum/Recovery/QubitGibbsDeficit.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For a reducing retained qubit the full Gibbs deficit splits into entropy loss and block gaps.",
        H("Exact reducing-qubit Gibbs deficit"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("reducing-qubit-gibbs-deficit"),
                DeclarationHandle.Create(Owner + "reducing_qubit_gibbs_deficit"),
                H("Deficit at an arbitrary joint density"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let E be a nonempty finite environment. In the reducing basis of the retained qubit, "
                        + "the field is block diagonal with two arbitrary Hermitian blocks B_i. Write "
                        + "g_i = log Tr exp(B_i), gamma_i = exp(B_i) / Tr exp(B_i), and m = max(g_0,g_1). "
                        + "The joint comparison density tau is block diagonal with blocks gamma_i / 2. "
                        + "The actual partial trace Phi over E sends tau to I/2, and both reference "
                        + "densities are faithful.")),
                    Paragraph(Text(
                        "For every joint density rho let P = Phi(rho), let p_i be the diagonal entries of P, "
                        + "and let V(rho) be S(rho) - S(P) plus Re Tr(rho diag(B_0,B_1)). Then "
                        + "m - V(rho) = D(rho || tau) - D(P || Phi(tau)) + sum_i p_i (m - g_i). "
                        + "The trace-log expressions are the finite branches of Umegaki relative entropy "
                        + "because both support inclusions hold. The trial density can be singular and may "
                        + "have off-diagonal retained blocks.")),
                    Paragraph(Text(
                        "Block functional calculus gives the i-th log(tau) block as B_i - "
                        + "(g_i + log 2) I. Expanding the two relative entropies cancels the scalar "
                        + "log(2) shifts. The trace pairing with the remaining scalar blocks reads the "
                        + "actual populations p_i, whose sum is one."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("reducing-qubit-gibbs-argmax"),
                DeclarationHandle.Create(Owner + "reducing_qubit_gibbs_argmax"),
                H("Pure marginals and all maximizing densities"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The maximum of V over all joint densities is m. Each winning label i achieves "
                        + "m at the density supported on that retained basis vector with environment "
                        + "density gamma_i. Its retained marginal is the rank-one diagonal matrix unit.")),
                    Paragraph(Text(
                        "For an arbitrary rho, equality V(rho) = m requires every positive p_i to have "
                        + "g_i = m. It also requires rho to be either the block mixture with blocks "
                        + "p_i gamma_i, or the product P tensor gamma_0 when gamma_0 = gamma_1. These "
                        + "conditions together suffice. In particular, at a tie with distinct Gibbs "
                        + "densities the optimizer set is the segment between the two pure-marginal states.")),
                    Paragraph(Text(
                        "Data processing gives nonnegative conditional loss for the two faithful "
                        + "references. At zero loss the fixed ordinary Petz map of the partial trace "
                        + "recovers rho. Its (i,j) block is P_ij sqrt(gamma_i) sqrt(gamma_j). Taking "
                        + "the partial trace forces either zero off-diagonal marginal or unit trace "
                        + "overlap of the two roots. That overlap forces equal roots by the squared "
                        + "Hilbert-Schmidt norm of their difference. The explicit recovery formula "
                        + "also verifies the converse in both cases."))),
                DescribeRole.Theorem))));
}
