using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.NikolovSegal.TypeA.Products;

internal sealed class PartIISupportedDetOneTransportDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Type-A Supported Det One Transport.",
        H("Type-A Supported Det One Transport"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("typea-partiisupporteddetonetransport-exists-outside-embedding"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/TypeA/Products/PartIISupportedDetOneTransport.exists_outside_embedding"),
                H("exists outside embedding"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("An actual unused coordinate exists from the strict cardinal bound."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("typea-partiisupporteddetonetransport-outside-scalar-commutes"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/TypeA/Products/PartIISupportedDetOneTransport.outside_scalar_commutes"),
                H("outside scalar commutes"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Scaling an unused coordinate commutes with the genuine supported matrix, rather than assuming a determinant-one transport oracle."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("typea-partiisupporteddetonetransport-supported-permutation-sl-transport"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/TypeA/Products/PartIISupportedDetOneTransport.supported_permutation_SL_transport"),
                H("supported permutation SL transport"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every coordinate permutation of a supported target is realized by a GENUINE determinant-one matrix. A single unused diagonal coordinate corrects the permutation determinant and leaves the target unchanged."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("typea-partiisupporteddetonetransport-supported-coordinate-sl-transport"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/TypeA/Products/PartIISupportedDetOneTransport.supported_coordinate_SL_transport"),
                H("supported coordinate SL transport"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("extension of the precise first-block coordinate correspondence, with literal support recovery for both matrices."))),
                DescribeRole.Theorem),
            Paragraph(Text("Nikolov and Segal, On finitely generated profinite groups, I: Strong completeness and uniform bounds, Annals of Mathematics165 (2007),171-238, DOI10.4007/annals.2007.165.171, Section10, Proposition10.2 and equations(45)-(50). PartII: Products in quasisimple groups, Annals of Mathematics165 (2007),239-273, DOI10.4007/annals.2007.165.239, Theorem1.2, Lemma4.1, Sections2,5,6 and9, Proposition6.2, Propositions6.5 and6.7, and equation(13). The type-A arguments use explicit matrix and central-quotient geometry, finite-field arithmetic, Sylow conjugacy and constructive ordered class products. They establish the untwisted projective type-A family above uniform group-cardinality cutoffs. They do not establish exhaustion of all finite simple groups, general central covers, general width/RBP or strong completeness. The explicit fixed-power class and supported-factor width proofs replace the cited Section5 [SW]/[LS2] inputs in this type-A application. No originality claim or redistribution of the papers is made.")))));
}
