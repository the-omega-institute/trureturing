using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.CausalMoments;

internal sealed class CertifiedSparseCausalWitnessDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ConceptDynamics/CausalMoments/CertifiedSparseCausalWitness.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Restricting the existing rational moment construction to the initial support yields a sparse witness with no new atoms. Such a witness has a checked zero-or-one-step representation, while accepted traces preserve the original causal LP semantics.",
        H("Complete checked sparse causal witnesses"),
        Blocks(
            Describe.Lean(DescribeId.Create("supported-replacement"),
                DeclarationHandle.Create(Prefix + "exists_supported_moment_replacement"), H("Select only initially supported causal atoms"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Apply the existing rational Caratheodory construction to the support subtype, then push the small latent law back to the original carrier. All nominated moments and hard support exclusions are preserved."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("accepted-certificate-exists"),
                DeclarationHandle.Create(Prefix + "exists_accepted_moment_certificate"), H("Completeness of the finite certificate language"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Already sparse inputs use an empty trace. Otherwise the difference from a supported sparse replacement is a valid null direction with pivot ratio one. This existence proof does not supply an executable discovery algorithm."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("row-query-array"),
                DeclarationHandle.Create(Prefix + "rowQueryArray"), H("Finite array adapter for original rows and query"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Coordinate zero holds the original objective; successor coordinates hold the original LP rows. This adapter changes no coefficient or feasibility semantics."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("checked-causal-witness"),
                DeclarationHandle.Create(Prefix + "checked_causal_problem_witness"), H("Return a sparse law for the unchanged causal problem"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("An accepted trace packages its actual output as FiniteResponseLaw on the original carrier, retains all LinearFeasible constraints and the exact objective, and bounds support by the row count plus two."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("checked-lower-endpoint"),
                DeclarationHandle.Create(Prefix + "checked_lower_endpoint_witness"), H("Reuse the original lower dual certificate"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The checked sparse output remains an attaining primal witness. The existing lower-bound certificate theorem certifies the same exact endpoint without altering its constraint system."))), DescribeRole.Theorem))));
}
