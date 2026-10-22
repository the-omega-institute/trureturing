using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra;

internal sealed class LatticeThetaCharacterDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/LatticeThetaCharacter.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual finite-charge restrictions of the all-charge Sugawara zero mode.",
        H("Actual Lattice Theta Character"),
        Blocks(
            Definition("cutoff-coeff-equiv", "cutoffCoeffEquiv", "Finite cutoff coefficient equivalence",
                "The charge-supported actual Sugawara eigenspace is identified with finitely supported coefficients on the literal charge and energy cutoff. The original H, H*gramComplex D = 1, and gramComplex D*H = 1 hypotheses are retained."),
            Theorem("cutoff-index-finite", "cutoffIndex_finite", "Finite fixed-charge energy fibres",
                "For every finite charge set and every signed integer energy, the literal cutoff index is finite by oscillatorLeFinite and a dependent finite charge sum."),
            Theorem("cutoff-grade-finite", "cutoffActualGrade_finiteDimensional", "Finite actual cutoff eigenspaces",
                "The actual charge-supported Sugawara eigenspace is finite-dimensional through its actual coefficient basis. This does not invoke a trace on an infinite full grade."),
            Definition("theta-restriction", "thetaRestriction", "Actual reflected restriction",
                "For a symmetric finite charge set, thetaLinear is restricted to the actual charge-supported Sugawara eigenspace. The restriction is built by codRestrict and domRestrict from the actual operator."),
            Theorem("cutoff-theta-trace-neutral-sum", "cutoff_theta_trace_neutral_sum", "Finite actual theta trace",
                "The finite matrix trace of the actual restricted theta operator is the signed occupation sum over the neutral charge labels. Reflection is applied before diagonal cancellation, and no infinite-grade or scalar proxy trace is used."),
            Theorem("actual-trace-series", "actual_theta_trace_series", "Actual trace series",
                "The neutral actual traces are grouped by integer oscillator energy. The signed occupation majorant gives absolute summability and a HasSum for the actual coefficient series, including the zero-rank case and complex phases."),
            Paragraph(Text("The full positive-grade specialization, named indefinite cutoff limit, eta normalization, and identity-ground S endpoint remain open in this implementation checkpoint.")))));

    private static DocumentBlock Theorem(string id, string name, string title, string prose) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);

    private static DocumentBlock Definition(string id, string name, string title, string prose) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);
}
