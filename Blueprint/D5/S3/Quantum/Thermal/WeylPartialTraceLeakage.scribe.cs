using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Thermal;

internal sealed class WeylPartialTraceLeakageDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Derive the actual bipartite Weyl twirl from the existing reconstruction theorem and obtain operator-norm and normalized Hilbert-Schmidt leakage certificates. No arbitrary twirl certificate is assumed.",
        H("Physical Weyl Partial-Trace Leakage"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("word-star-mul"),
                DeclarationHandle.Create("D5/S3/Quantum/Thermal/WeylPartialTraceLeakage.word_star_mul"),
                H("word star mul"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The actual finite Weyl matrices have the required adjoint inverse; their unitarity is proved from the repository shift and clock identities."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("weyl-completeness"),
                DeclarationHandle.Create("D5/S3/Quantum/Thermal/WeylPartialTraceLeakage.weyl_completeness"),
                H("weyl completeness"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Applying actual Weyl reconstruction to matrix units yields the entrywise completeness relation used by the concrete averaging calculation."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("twirlsum-partialtrace"),
                DeclarationHandle.Create("D5/S3/Quantum/Thermal/WeylPartialTraceLeakage.twirlSum_partialTrace"),
                H("twirlSum partialTrace"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Expand the tensor-local conjugations entrywise and sum the derived completeness identity. The result is the physical partial trace with its exact dimension factor."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("average-eq-zero-of-partialtrace-zero"),
                DeclarationHandle.Create("D5/S3/Quantum/Thermal/WeylPartialTraceLeakage.average_eq_zero_of_partialTrace_zero"),
                H("average eq zero of partialTrace zero"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Zero physical partial trace discharges the general averaging theorem premise. No zero-average assumption is supplied by the caller."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("physical-leakage-bounds"),
                DeclarationHandle.Create("D5/S3/Quantum/Thermal/WeylPartialTraceLeakage.physical_leakage_bounds"),
                H("physical leakage bounds"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every bipartite matrix with zero first partial trace, the largest actual local Weyl commutator operator norm lies between the matrix operator norm and twice that norm. The Euclidean operator norm scope is explicit."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("physical-zero-leakage-iff"),
                DeclarationHandle.Create("D5/S3/Quantum/Thermal/WeylPartialTraceLeakage.physical_zero_leakage_iff"),
                H("physical zero leakage iff"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a matrix with the physical centering condition, zero finite Weyl leakage is equivalent to the matrix itself being zero."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("trace-commutator-square"),
                DeclarationHandle.Create("D5/S3/Quantum/Thermal/WeylPartialTraceLeakage.trace_commutator_square"),
                H("trace commutator square"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Derive the trace-square polarization identity for a genuine unitary commutator, retaining both complex cross terms."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("trace-square-sum"),
                DeclarationHandle.Create("D5/S3/Quantum/Thermal/WeylPartialTraceLeakage.trace_square_sum"),
                H("trace square sum"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Summing the concrete centered Weyl conjugations cancels the two cross terms, yielding the exact trace-square identity for arbitrary, possibly non-Hermitian, matrices."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("normalized-hs-leakage-identity"),
                DeclarationHandle.Create("D5/S3/Quantum/Thermal/WeylPartialTraceLeakage.normalized_hs_leakage_identity"),
                H("normalized hs leakage identity"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Taking real traces and dividing by the full bipartite dimension gives the exact normalized Hilbert-Schmidt identity with prefactor 1/(2 M^2). No operator-norm to Hilbert-Schmidt norm substitution is made."))), DescribeRole.Theorem))));
}
