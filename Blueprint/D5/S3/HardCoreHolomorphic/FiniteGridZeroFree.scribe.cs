using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.HardCoreHolomorphic;

internal sealed class FiniteGridZeroFreeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual finite-square-grid nonvanishing from typed complex neighborhoods.",
        H("FiniteGridZeroFree"),
        Blocks(
            Describe.Lean(DescribeId.Create("hc-final-finitegridzerofree-finite-grid-partition-control"),
                DeclarationHandle.Create("D5/S3/HardCoreHolomorphic/FiniteGridZeroFree.finite_grid_partition_control"),
                H("finite grid partition control"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Simultaneous strong induction on actual vertex cardinality. The first component bounds every untyped graph partition away from zero. The second represents every compatible nonroot graph vacancy in its genuine type tube. All recursive calls have strictly fewer vertices; no same-size conclusion is used to prove itself. Holomorphic and geometric facts are actual dependencies."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("hc-final-finitegridzerofree-finite-grid-partition-lower"),
                DeclarationHandle.Create("D5/S3/HardCoreHolomorphic/FiniteGridZeroFree.finite_grid_partition_lower"),
                H("finite grid partition lower"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A quantitative common lower modulus for every actual finite induced grid. The exponential volume factor is explicit and includes the empty graph."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("hc-final-finitegridzerofree-finite-grid-zero-free"),
                DeclarationHandle.Create("D5/S3/HardCoreHolomorphic/FiniteGridZeroFree.finite_grid_zero_free"),
                H("finite grid zero free"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Unconditional finite-grid nonvanishing on the constructed common activity neighborhood. There is no supplied nonvanishing, contraction, typing or graph-size hypothesis."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("hc-final-finitegridzerofree-finite-grid-zero-free-explicit"),
                DeclarationHandle.Create("D5/S3/HardCoreHolomorphic/FiniteGridZeroFree.finite_grid_zero_free_explicit"),
                H("finite grid zero free explicit"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The explicit interval and width are in the theorem statement, for all finite vertex domains at once. This is the actual independent-set sum."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("hc-final-finitegridzerofree-finite-grid-independence-polynomial-zero-free"),
                DeclarationHandle.Create("D5/S3/HardCoreHolomorphic/FiniteGridZeroFree.finite_grid_independencePolynomial_zero_free"),
                H("finite grid independencePolynomial zero free"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The same result for the existing integer-coefficient independence polynomial, via its proved actual-configuration evaluation identity."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("hc-final-finitegridzerofree-finite-grid-origin-increment"),
                DeclarationHandle.Create("D5/S3/HardCoreHolomorphic/FiniteGridZeroFree.finite_grid_origin_increment"),
                H("finite grid origin increment"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The local partition increment for every present origin remains in a common right half-plane. The derived bound supports stable ordered logarithms."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("hc-final-finitegridzerofree-finite-grid-vacancy-bound"),
                DeclarationHandle.Create("D5/S3/HardCoreHolomorphic/FiniteGridZeroFree.finite_grid_vacancy_bound"),
                H("finite grid vacancy bound"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every actual marked vacancy, even at a boundary vertex or an absent vertex, has modulus at most two on the same complex neighborhood."))), DescribeRole.Theorem))));
}
