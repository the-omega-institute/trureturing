using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Spacetime;

internal sealed class FiniteCausalPathsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite Causal Path Bounds.",
        H("Finite Causal Path Bounds"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("finitecausalpaths-path-length-bound"),
                DeclarationHandle.Create("D5/S3/ConceptDynamics/Spacetime/FiniteCausalPaths.path_length_bound"),
                H("A legal archive bounds every causal path"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The archive's strict causal order is converted to Mathlib's partial-order interface, and "
                    + "its set-of-pairs relation series becomes an LTSeries. The direct application of "
                    + "LTSeries.length_lt_card gives at most N minus one edges for N archived events."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("finitecausalpaths-transgen-iff-bounded-series"),
                DeclarationHandle.Create("D5/S3/ConceptDynamics/Spacetime/FiniteCausalPaths.transGen_iff_bounded_series"),
                H("Bounded sequences characterize transitive closure"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For any generating subrelation of a legal archive, a nonempty TransGen path is "
                    + "equivalent to a finite relation series with matching endpoints and length at most N "
                    + "minus one. Mathlib's reflexive-transitive list-chain witness supplies the tail after "
                    + "the first edge, and its list-to-series equivalence supplies the series. This is a "
                    + "general finite theorem, including the vacuity of an empty event set."))),
                DescribeRole.Theorem))));
}
