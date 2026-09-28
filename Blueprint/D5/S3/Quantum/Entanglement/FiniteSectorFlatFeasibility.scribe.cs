using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement;

internal sealed class FiniteSectorFlatFeasibilityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact flat basis output under arbitrary positive source and target sector ranks.",
        H("Flat Sector Rank Feasibility"),
        Blocks(Describe.Lean(
            DescribeId.Create("finite-sector-flat-feasibility"),
            DeclarationHandle.Create("D5/S3/Quantum/Entanglement/FiniteSectorFlatFeasibility.flat_feasibility"),
            H("Positive rank multiples characterize feasibility"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "For every pair of positive sector-rank functions r and d, two actual "
                    + "local quantum channels produce the exact flat target state on each "
                    + "logical basis sector if and only if r(s)=d(s)m(s) for a positive "
                    + "integer m(s) in every sector.")),
                Paragraph(Text(
                    "Necessity uses actual finite dilations. Purity of the joint flat output "
                    + "forces the local amplitudes through the target vector, and an "
                    + "environment projection identifies an integer rank. Sufficiency "
                    + "constructs sectorwise coordinate equivalences, combines them into "
                    + "a local isometry, traces out the residual coordinate, and verifies "
                    + "each exact basis output."))),
            DescribeRole.Theorem))));
}
