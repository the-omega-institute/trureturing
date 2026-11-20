using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence;

internal sealed class FiniteTransferSeriesDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/FiniteTransferSeries.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite matrix powers give an exact formal resolvent with a unit-constant polynomial denominator.",
        H("Generating series of finite matrix observations"),
        Blocks(
            Node("walk-series", "walks", "Shifted series of matrix powers", DescribeRole.Definition,
                "For a finite index type with decidable equality, a rational square matrix M, and rational vectors u and v, "
                + "walks(M,u,v) is a formal power series with zero constant coefficient and coefficient uᵀM^m v at degree m+1."),
            Node("walk-resolvent", "walks_resolvent", "Matrix inverse and polynomial denominator", DescribeRole.Theorem,
                "Set A = I−XM over the rational polynomial ring and B = I−XM over the rational formal power series ring. "
                + "The constant coefficient of det A is one. The shifted series is X·uᵀB⁻¹v, "
                + "and multiplying it by det A gives the polynomial X·uᵀadj(A)v. "
                + "The coefficient of degree m of the entrywise matrix series is M^m. "
                + "Multiplication by B has constant coefficient I and cancels every higher coefficient by the matrix power law. "
                + "The determinant condition gives a formal inverse, so the coefficient series is that inverse. "
                + "The adjugate identity then clears the denominator."))));

    private static DocumentBlock Node(string id, string name, string title, DescribeRole role, string statement) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(statement))), role);
}
