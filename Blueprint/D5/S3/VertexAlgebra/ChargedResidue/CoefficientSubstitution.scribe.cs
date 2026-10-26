using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.ChargedResidue;

internal sealed class CoefficientSubstitutionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Formal collision residue coefficients.",
        H("CoefficientSubstitution"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("charged-residue-coeff-subst-jacobian"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/ChargedResidue/CoefficientSubstitution.coeff_subst_jacobian"),
                H("Coefficient substitution with the Jacobian"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/VertexAlgebra/flm1988monster")),
                Blocks(Paragraph(Text("For every complex formal power series f, unit u and natural coefficient n, the nth coefficient of f(X*u) times u^(-(n+1)) times the formal derivative of X*u equals the nth coefficient of f. The proof splits off the constant term and cancels its positive-degree contribution using the derivative of an inverse unit power. It includes n=0 and imposes no polynomial or support restriction on f."))),
                DescribeRole.Theorem))));
}
