using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.NikolovSegal.Unitary;

internal sealed class UnitaryWidthEndpointStabilizerDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual unitary width endpoint stabilizer supplies the parameterized matrix, finite-field or ordered-product identities consumed by the whole-SU K5 width and intrinsic prescribed-product proof paths. All original hypotheses and actual carriers are retained; this source provides no oracle for bare automorphism recognition.",
        H("Unitary Width Endpoint Stabilizer"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("unitary-unitarywidthendpointstabilizer-inverse-coordinate-row"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/Unitary/UnitaryWidthEndpointStabilizer.inverse_coordinate_row"),
                H("inverse coordinate row"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Fixing a literal coordinate row also fixes that row in the actual inverse."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("unitary-unitarywidthendpointstabilizer-reflected-coordinate-column"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/Unitary/UnitaryWidthEndpointStabilizer.reflected_coordinate_column"),
                H("reflected coordinate column"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The other endpoint is forced by actual SU fixedness, not a flag premise."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("unitary-unitarywidthendpointstabilizer-four-operations-endpoint-stabilizer"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/Unitary/UnitaryWidthEndpointStabilizer.four_operations_endpoint_stabilizer"),
                H("four operations endpoint stabilizer"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("One absolute four-operation Hermitian elimination puts every actual SU matrix of dimension≥4 in the two-endpoint stabilizer. Both endpoint equalities are derived. This is a rank-reduction bridge, not a full width theorem."))),
                DescribeRole.Theorem),
            Paragraph(Text("The results concern special-unitary matrix groups over finite fields. Their geometric setting is Nikolov and Segal, On finitely generated profinite groups, II: Products in quasisimple groups, Annals of Mathematics 165 (2007), 239-273, DOI 10.4007/annals.2007.165.239. Prescribed-product statements retain their field-size, rank and automorphism hypotheses.")))));
}
