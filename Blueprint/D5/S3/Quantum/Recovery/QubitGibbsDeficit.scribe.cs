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
                DescribeRole.Theorem))));
}
