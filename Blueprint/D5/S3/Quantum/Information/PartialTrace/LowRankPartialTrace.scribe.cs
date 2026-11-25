using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Information.PartialTrace;

internal sealed class LowRankPartialTraceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Two alternative tensor sites share the same rank-constrained projection mass.",
        H("Low-rank partial trace on disjoint tensor sites"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("partial-trace-rank-bound"),
                DeclarationHandle.Create("D5/S3/Quantum/Information/PartialTrace/LowRankPartialTrace.frobenius_sq_partialTraceLeft_le_rank_mul"),
                H("Partial trace under an actual matrix rank bound"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every finite complex matrix on a tensor product, the Frobenius norm "
                    + "square of the first-factor partial trace is at most the actual matrix rank "
                    + "times the input norm square. Singular-value decomposition writes the matrix "
                    + "as a sum of rank-one terms. Reshaping each pair of singular vectors bounds "
                    + "the norm of its partial trace by one. Cauchy–Schwarz then bounds the "
                    + "square of the sum of the nonzero singular values."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("two-site-mass-bound"),
                DeclarationHandle.Create("D5/S3/Quantum/Information/PartialTrace/LowRankPartialTrace.two_site_mass_sum_le"),
                H("Projection mass on two alternative sites"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Let the two disjoint sites have the same positive dimension m, with any "
                    + "finite remaining factor. Each normalized partial trace inserts an identity "
                    + "on its traced site. The two Hilbert–Schmidt projections commute and "
                    + "compose to the projection that traces both sites. The squared norm of the "
                    + "common complement bounds the sum of the two projection masses by the "
                    + "input mass plus the mass on the union. The union has dimension m squared, "
                    + "so an actual rank cap of m bounds the latter mass by one over m times the "
                    + "input mass. The resulting factor of one plus one over m holds after "
                    + "summing over a finite family, including products through quantum memory "
                    + "blocks of dimension at most m."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("basis-encoder-attainment"),
                DeclarationHandle.Create("D5/S3/Quantum/Information/PartialTrace/LowRankPartialTrace.basis_encoder_attains"),
                H("Attainment by storing the first site"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Store the first site and record the basis outcome of the remaining two "
                    + "factors. Each rectangular encoder matrix is a coisometry onto the "
                    + "stored site, and its adjoint products sum to the input identity. The "
                    + "normalized reverse therefore uses the adjoint in each outcome block. "
                    + "Each composite product has rank m. Its squared mass is m on the first "
                    + "site and one on the second site, so the summed bound is attained."))),
                DescribeRole.Theorem))));
}
