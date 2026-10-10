using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.NikolovSegal.Unitary;

internal sealed class UnitaryRankTwoGeometryDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual unitary rank two geometry supplies the parameterized matrix, finite-field or ordered-product identities consumed by the whole-SU K5 width and intrinsic prescribed-product proof paths. All original hypotheses and actual carriers are retained; this source provides no oracle for bare automorphism recognition.",
        H("Unitary Rank Two Geometry"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("unitary-unitaryranktwogeometry-j"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/Unitary/UnitaryRankTwoGeometry.J"),
                H("J"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The parameterized J statement describes the actual unitary geometry or prescribed ordered-product construction. Its Lean telescope retains every field, rank, involution, input and equality hypothesis shown."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("unitary-unitaryranktwogeometry-j-eq"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/Unitary/UnitaryRankTwoGeometry.J_eq"),
                H("J eq"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The parameterized J eq statement describes the actual unitary geometry or prescribed ordered-product construction. Its Lean telescope retains every field, rank, involution, input and equality hypothesis shown."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("unitary-unitaryranktwogeometry-exists-antifixed"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/Unitary/UnitaryRankTwoGeometry.exists_antifixed"),
                H("exists antifixed"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The parameterized exists antifixed statement describes the actual unitary geometry or prescribed ordered-product construction. Its Lean telescope retains every field, rank, involution, input and equality hypothesis shown."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("unitary-unitaryranktwogeometry-adjoint-mul"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/Unitary/UnitaryRankTwoGeometry.adjoint_mul"),
                H("adjoint mul"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The parameterized adjoint mul statement describes the actual unitary geometry or prescribed ordered-product construction. Its Lean telescope retains every field, rank, involution, input and equality hypothesis shown."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("unitary-unitaryranktwogeometry-hermitian-iff-inverse"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/Unitary/UnitaryRankTwoGeometry.hermitian_iff_inverse"),
                H("hermitian iff inverse"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The parameterized hermitian iff inverse statement describes the actual unitary geometry or prescribed ordered-product construction. Its Lean telescope retains every field, rank, involution, input and equality hypothesis shown."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("unitary-unitaryranktwogeometry-inverse-matrix"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/Unitary/UnitaryRankTwoGeometry.inverse_matrix"),
                H("inverse matrix"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The parameterized inverse matrix statement describes the actual unitary geometry or prescribed ordered-product construction. Its Lean telescope retains every field, rank, involution, input and equality hypothesis shown."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("unitary-unitaryranktwogeometry-hermitian-iff-entries"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/Unitary/UnitaryRankTwoGeometry.hermitian_iff_entries"),
                H("hermitian iff entries"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The parameterized hermitian iff entries statement describes the actual unitary geometry or prescribed ordered-product construction. Its Lean telescope retains every field, rank, involution, input and equality hypothesis shown."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("unitary-unitaryranktwogeometry-specialunitary"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/Unitary/UnitaryRankTwoGeometry.specialUnitary"),
                H("specialUnitary"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Actual SU2 for the Hermitian anti-diagonal, as a subgroup of native SL2."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("unitary-unitaryranktwogeometry-mem-specialunitary"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/Unitary/UnitaryRankTwoGeometry.mem_specialUnitary"),
                H("mem specialUnitary"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The parameterized mem specialUnitary statement describes the actual unitary geometry or prescribed ordered-product construction. Its Lean telescope retains every field, rank, involution, input and equality hypothesis shown."))),
                DescribeRole.Theorem),
            Paragraph(Text("The results concern special-unitary matrix groups over finite fields. Their geometric setting is Nikolov and Segal, On finitely generated profinite groups, II: Products in quasisimple groups, Annals of Mathematics 165 (2007), 239-273, DOI 10.4007/annals.2007.165.239. Prescribed-product statements retain their field-size, rank and automorphism hypotheses.")))));
}
