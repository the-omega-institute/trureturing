using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.NikolovSegal.Unitary;

internal sealed class UnitaryRankTwoCoordinatesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual unitary rank two coordinates supplies the parameterized matrix, finite-field or ordered-product identities consumed by the whole-SU K5 width and intrinsic prescribed-product proof paths. All original hypotheses and actual carriers are retained; this source provides no oracle for bare automorphism recognition.",
        H("Unitary Rank Two Coordinates"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("unitary-unitaryranktwocoordinates-coordinatematrix"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/Unitary/UnitaryRankTwoCoordinates.coordinateMatrix"),
                H("coordinateMatrix"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Change of basis by diag(τ,1): D⁻¹ A D."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("unitary-unitaryranktwocoordinates-coordinatematrix-conjugation"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/Unitary/UnitaryRankTwoCoordinates.coordinateMatrix_conjugation"),
                H("coordinateMatrix conjugation"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The parameterized coordinateMatrix conjugation statement describes the actual unitary geometry or prescribed ordered-product construction. Its Lean telescope retains every field, rank, involution, input and equality hypothesis shown."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("unitary-unitaryranktwocoordinates-coordinatematrix-det"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/Unitary/UnitaryRankTwoCoordinates.coordinateMatrix_det"),
                H("coordinateMatrix det"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The parameterized coordinateMatrix det statement describes the actual unitary geometry or prescribed ordered-product construction. Its Lean telescope retains every field, rank, involution, input and equality hypothesis shown."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("unitary-unitaryranktwocoordinates-coordinatematrix-mul"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/Unitary/UnitaryRankTwoCoordinates.coordinateMatrix_mul"),
                H("coordinateMatrix mul"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The parameterized coordinateMatrix mul statement describes the actual unitary geometry or prescribed ordered-product construction. Its Lean telescope retains every field, rank, involution, input and equality hypothesis shown."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("unitary-unitaryranktwocoordinates-coordinatematrix-inverse"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/Unitary/UnitaryRankTwoCoordinates.coordinateMatrix_inverse"),
                H("coordinateMatrix inverse"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The parameterized coordinateMatrix inverse statement describes the actual unitary geometry or prescribed ordered-product construction. Its Lean telescope retains every field, rank, involution, input and equality hypothesis shown."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("unitary-unitaryranktwocoordinates-scalesl"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/Unitary/UnitaryRankTwoCoordinates.scaleSL"),
                H("scaleSL"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The parameterized scaleSL statement describes the actual unitary geometry or prescribed ordered-product construction. Its Lean telescope retains every field, rank, involution, input and equality hypothesis shown."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("unitary-unitaryranktwocoordinates-scalesl-val"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/Unitary/UnitaryRankTwoCoordinates.scaleSL_val"),
                H("scaleSL val"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The parameterized scaleSL val statement describes the actual unitary geometry or prescribed ordered-product construction. Its Lean telescope retains every field, rank, involution, input and equality hypothesis shown."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("unitary-unitaryranktwocoordinates-coordinatematrix-fixed"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/Unitary/UnitaryRankTwoCoordinates.coordinateMatrix_fixed"),
                H("coordinateMatrix fixed"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Each entry of the changed SU2 basis lies in the actual fixed subfield."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("unitary-unitaryranktwocoordinates-fixedcoordinatematrix"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/Unitary/UnitaryRankTwoCoordinates.fixedCoordinateMatrix"),
                H("fixedCoordinateMatrix"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The literal fixed-field coordinate matrix, with membership proved entry by entry."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("unitary-unitaryranktwocoordinates-fixedcoordinatematrix-coe"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/Unitary/UnitaryRankTwoCoordinates.fixedCoordinateMatrix_coe"),
                H("fixedCoordinateMatrix coe"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The parameterized fixedCoordinateMatrix coe statement describes the actual unitary geometry or prescribed ordered-product construction. Its Lean telescope retains every field, rank, involution, input and equality hypothesis shown."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("unitary-unitaryranktwocoordinates-tofixedsl"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/Unitary/UnitaryRankTwoCoordinates.toFixedSL"),
                H("toFixedSL"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Actual SU2 → native SL2 over its fixed field."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("unitary-unitaryranktwocoordinates-fromfixedsl"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/Unitary/UnitaryRankTwoCoordinates.fromFixedSL"),
                H("fromFixedSL"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Inclusion into F followed by the inverse actual change of basis."))),
                DescribeRole.Definition),
            Paragraph(Text("The results concern special-unitary matrix groups over finite fields. Their geometric setting is Nikolov and Segal, On finitely generated profinite groups, II: Products in quasisimple groups, Annals of Mathematics 165 (2007), 239-273, DOI 10.4007/annals.2007.165.239. Prescribed-product statements retain their field-size, rank and automorphism hypotheses.")))));
}
