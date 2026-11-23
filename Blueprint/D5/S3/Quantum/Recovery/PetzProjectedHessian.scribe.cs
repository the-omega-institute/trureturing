using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Recovery;

internal sealed class PetzProjectedHessianDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An explicit representative of the trace pairing in the two-flag Hessian metric.",
        H("Weighted trace pairing on the partial-trace kernel"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("petz-projected-hessian-representative"),
                DeclarationHandle.Create("D5/S3/Quantum/Recovery/PetzProjectedHessian.representative_spec"),
                H("The representative and its exact energy"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Index the matrix by a retained bit and a flag bit. Give each ordered " +
                        "entry a positive real weight, symmetric under transposition. The " +
                        "weighted energy is the sum of squared moduli divided by these weights.")),
                    Paragraph(Text(
                        "For each retained pair, let a and b be the same-flag weights and let " +
                        "y and z be the corresponding entries of the Hermitian test. The " +
                        "representative has same-flag entries ±ab(y−z)/(a+b). Its inter-flag " +
                        "entries are the original entries multiplied by their weights.")),
                    Paragraph(Text(
                        "The representative is Hermitian and has zero right partial trace. " +
                        "Against any zero-marginal matrix its weighted real pairing equals the " +
                        "real trace pairing with the original test. Each retained pair contributes " +
                        "ab|y−z|²/(a+b) plus the weighted squared moduli of its two inter-flag entries " +
                        "to the representative's energy."))),
                DescribeRole.Theorem))));
}
