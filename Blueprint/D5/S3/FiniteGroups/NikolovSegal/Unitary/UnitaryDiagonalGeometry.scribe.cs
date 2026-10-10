using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.NikolovSegal.Unitary;

internal sealed class UnitaryDiagonalGeometryDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual unitary diagonal geometry supplies the parameterized matrix, finite-field or ordered-product identities consumed by the whole-SU K5 width and intrinsic prescribed-product proof paths. All original hypotheses and actual carriers are retained; this source provides no oracle for bare automorphism recognition.",
        H("Unitary Diagonal Geometry"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("unitary-unitarydiagonalgeometry-hermitianform"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/Unitary/UnitaryDiagonalGeometry.hermitianForm"),
                H("hermitianForm"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The parameterized hermitianForm statement describes the actual unitary geometry or prescribed ordered-product construction. Its Lean telescope retains every field, rank, involution, input and equality hypothesis shown."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("unitary-unitarydiagonalgeometry-adjoint"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/Unitary/UnitaryDiagonalGeometry.adjoint"),
                H("adjoint"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The parameterized adjoint statement describes the actual unitary geometry or prescribed ordered-product construction. Its Lean telescope retains every field, rank, involution, input and equality hypothesis shown."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("unitary-unitarydiagonalgeometry-diagonalsl"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/Unitary/UnitaryDiagonalGeometry.diagonalSL"),
                H("diagonalSL"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The parameterized diagonalSL statement describes the actual unitary geometry or prescribed ordered-product construction. Its Lean telescope retains every field, rank, involution, input and equality hypothesis shown."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("unitary-unitarydiagonalgeometry-diagonal-hermitian"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/Unitary/UnitaryDiagonalGeometry.diagonal_hermitian"),
                H("diagonal hermitian"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The parameterized diagonal hermitian statement describes the actual unitary geometry or prescribed ordered-product construction. Its Lean telescope retains every field, rank, involution, input and equality hypothesis shown."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("unitary-unitarydiagonalgeometry-diagonal-conjugation-entries"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/Unitary/UnitaryDiagonalGeometry.diagonal_conjugation_entries"),
                H("diagonal conjugation entries"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The parameterized diagonal conjugation entries statement describes the actual unitary geometry or prescribed ordered-product construction. Its Lean telescope retains every field, rank, involution, input and equality hypothesis shown."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("unitary-unitarydiagonalgeometry-pairswap"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/Unitary/UnitaryDiagonalGeometry.pairSwap"),
                H("pairSwap"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The parameterized pairSwap statement describes the actual unitary geometry or prescribed ordered-product construction. Its Lean telescope retains every field, rank, involution, input and equality hypothesis shown."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("unitary-unitarydiagonalgeometry-pairedentries"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/Unitary/UnitaryDiagonalGeometry.pairedEntries"),
                H("pairedEntries"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The parameterized pairedEntries statement describes the actual unitary geometry or prescribed ordered-product construction. Its Lean telescope retains every field, rank, involution, input and equality hypothesis shown."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("unitary-unitarydiagonalgeometry-pairedentries-hermitian"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/Unitary/UnitaryDiagonalGeometry.pairedEntries_hermitian"),
                H("pairedEntries hermitian"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The parameterized pairedEntries hermitian statement describes the actual unitary geometry or prescribed ordered-product construction. Its Lean telescope retains every field, rank, involution, input and equality hypothesis shown."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("unitary-unitarydiagonalgeometry-prod-zpow-base"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/Unitary/UnitaryDiagonalGeometry.prod_zpow_base"),
                H("prod zpow base"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The parameterized prod zpow base statement describes the actual unitary geometry or prescribed ordered-product construction. Its Lean telescope retains every field, rank, involution, input and equality hypothesis shown."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("unitary-unitarydiagonalgeometry-prod-pairedentries"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/Unitary/UnitaryDiagonalGeometry.prod_pairedEntries"),
                H("prod pairedEntries"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The parameterized prod pairedEntries statement describes the actual unitary geometry or prescribed ordered-product construction. Its Lean telescope retains every field, rank, involution, input and equality hypothesis shown."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("unitary-unitarydiagonalgeometry-oddswap"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/Unitary/UnitaryDiagonalGeometry.oddSwap"),
                H("oddSwap"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The parameterized oddSwap statement describes the actual unitary geometry or prescribed ordered-product construction. Its Lean telescope retains every field, rank, involution, input and equality hypothesis shown."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("unitary-unitarydiagonalgeometry-oddentries"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/Unitary/UnitaryDiagonalGeometry.oddEntries"),
                H("oddEntries"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The parameterized oddEntries statement describes the actual unitary geometry or prescribed ordered-product construction. Its Lean telescope retains every field, rank, involution, input and equality hypothesis shown."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("unitary-unitarydiagonalgeometry-prod-oddentries"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/Unitary/UnitaryDiagonalGeometry.prod_oddEntries"),
                H("prod oddEntries"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The parameterized prod oddEntries statement describes the actual unitary geometry or prescribed ordered-product construction. Its Lean telescope retains every field, rank, involution, input and equality hypothesis shown."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("unitary-unitarydiagonalgeometry-oddentries-hermitian"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/Unitary/UnitaryDiagonalGeometry.oddEntries_hermitian"),
                H("oddEntries hermitian"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The parameterized oddEntries hermitian statement describes the actual unitary geometry or prescribed ordered-product construction. Its Lean telescope retains every field, rank, involution, input and equality hypothesis shown."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("unitary-unitarydiagonalgeometry-evendiagonal"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/Unitary/UnitaryDiagonalGeometry.evenDiagonal"),
                H("evenDiagonal"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The parameterized evenDiagonal statement describes the actual unitary geometry or prescribed ordered-product construction. Its Lean telescope retains every field, rank, involution, input and equality hypothesis shown."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("unitary-unitarydiagonalgeometry-odddiagonal"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/Unitary/UnitaryDiagonalGeometry.oddDiagonal"),
                H("oddDiagonal"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The parameterized oddDiagonal statement describes the actual unitary geometry or prescribed ordered-product construction. Its Lean telescope retains every field, rank, involution, input and equality hypothesis shown."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("unitary-unitarydiagonalgeometry-evendiagonal-unitary"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/Unitary/UnitaryDiagonalGeometry.evenDiagonal_unitary"),
                H("evenDiagonal unitary"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The parameterized evenDiagonal unitary statement describes the actual unitary geometry or prescribed ordered-product construction. Its Lean telescope retains every field, rank, involution, input and equality hypothesis shown."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("unitary-unitarydiagonalgeometry-odddiagonal-unitary"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/Unitary/UnitaryDiagonalGeometry.oddDiagonal_unitary"),
                H("oddDiagonal unitary"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The parameterized oddDiagonal unitary statement describes the actual unitary geometry or prescribed ordered-product construction. Its Lean telescope retains every field, rank, involution, input and equality hypothesis shown."))),
                DescribeRole.Theorem),
            Paragraph(Text("The results concern special-unitary matrix groups over finite fields. Their geometric setting is Nikolov and Segal, On finitely generated profinite groups, II: Products in quasisimple groups, Annals of Mathematics 165 (2007), 239-273, DOI 10.4007/annals.2007.165.239. Prescribed-product statements retain their field-size, rank and automorphism hypotheses.")))));
}
