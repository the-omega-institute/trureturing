using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Semigroups;

internal sealed class WuCubicThermalBasisDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Quantum/Semigroups/WuCubicThermalBasis.";
    private static readonly LibraryNoteRef Wu = LibraryNoteRef.Create("D5/L/SpinModels/wu2026sharp");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A complex common eigenbasis for the signed two-mode CAR generator and product Gibbs modular conjugation.",
        H("Thermal degree and signed modular charge"),
        Blocks(
            Describe.Lean(DescribeId.Create("generator-direction"),
                DeclarationHandle.Create(Owner + "generator_direction"),
                H("Generator eigenvalues"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Wu),
                Blocks(
                    Paragraph(Text("In Wu v1, Remark 3.15, equation (3.54), take exponent three and two equal-cap signed CAR modes with r = exp(β/3). Use the actual generator and Gibbs matrix from WuCubicOperatorBridge. For every real r ≥ 0 the one-mode rates are a = 1/(1 + r³) and b = r³a. In local order I, E₀₁, E₁₀, diag(b,−a), the degrees are 0, 1, 1, 2 and the signed charges are 0, −1, 1, 0.")),
                    Paragraph(Text("For each pair k of local indices, the direction Vₖ is the ordinary product of the left family, which includes a parity matrix on the second mode for the two off-diagonal local directions, and the right family. The degree d(k) and charge q(k) are the sums of the corresponding local labels. The actual positive-sign generator sends Vₖ to d(k)Vₖ. In the parity-adjusted tensor coordinates, its two signed dissipators act as the sum of the two local generators; the local degrees follow by the identity a+b=1."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("modular-direction"),
                DeclarationHandle.Create(Owner + "modular_direction"),
                H("Gibbs modular eigenvector equation"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Wu),
                Blocks(Paragraph(Text("For any real r ≠ 0 and every label k, D(r)Vₖ = (r³)^(q(k)) VₖD(r). The Gibbs matrix is the diagonal product of the two local occupation weights. The parity factors commute with these diagonal weights, so the modular charges add."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("modular-linear-direction"),
                DeclarationHandle.Create(Owner + "modularLinear_direction"),
                H("Actual modular conjugation"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Wu),
                Blocks(Paragraph(Text("For r > 0 the Gibbs matrix is invertible. The complex-linear map X ↦ D(r)XD(r)⁻¹ sends every Vₖ to (r³)^(q(k))Vₖ. The same directions diagonalize the generator."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("expansion"),
                DeclarationHandle.Create(Owner + "expansion"),
                H("Expansion in sixteen directions"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Wu),
                Blocks(Paragraph(Text("For r ≥ 0 and every complex matrix X on the two-mode occupation space, undo the parity factor on the left off-diagonal block and apply the one-mode coefficient formula (aX₀₀+bX₁₁, X₀₁, X₁₀, X₀₀−X₁₁) in each index. The resulting sixteen coefficients give X as their linear combination of the Vₖ. The sixteen directions span a sixteen-dimensional complex matrix space, so the explicit family defines a complex basis. Its coordinates are the stated coefficients."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("abs-charge-le-degree"),
                DeclarationHandle.Create(Owner + "abs_charge_le_degree"),
                H("Degree bounds absolute charge"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Wu),
                Blocks(Paragraph(Text("For every pair of local labels, the absolute value of the sum of the two signed charges is at most the sum of the two degrees."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("generator-high-charge-hermitian"),
                DeclarationHandle.Create(Owner + "generator_highChargeHermitian"),
                H("Physical degree-two Hermitian direction"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Wu),
                Blocks(Paragraph(Text("For r ≥ 0 the difference V₍₁,₁₎ − V₍₂,₂₎ is a degree-two generator eigenvector. The two summands have charges −2 and 2, saturating the absolute-charge bound. Their difference is the sum of the matrix units joining occupations (0,0) and (1,1) in both directions, hence is nonzero and Hermitian."))),
                DescribeRole.Theorem))));
}
