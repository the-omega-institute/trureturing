using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Hiai;

internal sealed class SupportPowerLimitsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Hiai/SupportPowerLimits.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Divergence/hiai2025geometrictraceconvexity");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite spectral support decompositions and positive matrix power limits",
        H("Finite spectral support decompositions and positive matrix power limits"), Blocks([
            Describe.Lean(DescribeId.Create("cfc-eigenmatrix"),
                DeclarationHandle.Create(Prefix + "cfc_eigenmatrix"),
                H("Spectral functions on an eigenmatrix"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("For arbitrary finite rectangular complex matrices, if A is Hermitian and A V equals V times the real diagonal lambda, then its spectral function f acts on V as the diagonal f of lambda. No continuity assumption on f is required on a finite spectrum."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("support-rpow-shift-tendsto"),
                DeclarationHandle.Create(Prefix + "support_rpow_shift_tendsto"),
                H("Shifted powers on the support"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("For a positive semidefinite matrix A and every nonzero real exponent q, the CFC function that is zero on the zero eigenspace and equals (x plus epsilon) to q elsewhere converges to A to q as positive epsilon tends to zero. This includes negative exponents."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("kernel-projection-data"),
                DeclarationHandle.Create(Prefix + "kernel_projection_data"),
                H("The complementary support projection"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("For a positive semidefinite matrix A whose kernel is contained in the kernel of B, Q equals I minus the spectral support of A. It is selfadjoint, idempotent and positive semidefinite, and both A Q and B Q vanish."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("rpow-on-eigenmatrix"),
                DeclarationHandle.Create(Prefix + "rpow_on_eigenmatrix"),
                H("Real powers on an eigenspace"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("For a positive semidefinite matrix X, if X V equals c times V, then X to real exponent q times V equals c to q times V. The scalar and matrix powers use the same totalized real-power convention."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("shifted-rpow-formula"),
                DeclarationHandle.Create(Prefix + "shifted_rpow_formula"),
                H("Spectral formula for a positive shift"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("For a positive semidefinite matrix A and positive epsilon, the real power of A plus epsilon I is the CFC function (x plus epsilon) to q on the fixed spectrum of A."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("inverse-shift-split"),
                DeclarationHandle.Create(Prefix + "inverse_shift_split"),
                H("The support and kernel parts of a shift"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("For every real exponent q, the power of A plus positive epsilon I splits into its support-restricted CFC power and epsilon to q times the complementary support projection. The identity is valid for singular A and negative q."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("tendsto-positive-rpow"),
                DeclarationHandle.Create(Prefix + "tendsto_positive_rpow"),
                H("Continuity of positive powers"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("For a net of eventually positive semidefinite matrices converging to a positive semidefinite M, every strictly positive real power converges to the same power of M. The filter and finite matrix dimension are arbitrary."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("psd-nested-rpow"),
                DeclarationHandle.Create(Prefix + "psd_nested_rpow"),
                H("Composition of finite spectral real powers"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("For a positive semidefinite A and real p and q, the iterated real power (A to p) to q equals A to p times q. The scalar real-power identity is applied on the nonnegative finite spectrum."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("tendsto-trace-power"),
                DeclarationHandle.Create(Prefix + "tendsto_tracePower"),
                H("Continuity of positive trace powers"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Under eventual positive semidefiniteness and convergence to a positive semidefinite matrix, the real trace of every strictly positive matrix power converges. This combines positive-power continuity with the continuous real trace."))), DescribeRole.Theorem)])));
}
