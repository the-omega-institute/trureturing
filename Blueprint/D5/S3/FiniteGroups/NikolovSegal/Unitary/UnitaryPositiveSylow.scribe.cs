using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.NikolovSegal.Unitary;

internal sealed class UnitaryPositiveSylowDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual unitary positive sylow supplies the parameterized matrix, finite-field or ordered-product identities consumed by the whole-SU K5 width and intrinsic prescribed-product proof paths. All original hypotheses and actual carriers are retained; this source provides no oracle for bare automorphism recognition.",
        H("Unitary Positive Sylow"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("unitary-unitarypositivesylow-upper-pow"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/Unitary/UnitaryPositiveSylow.upper_pow"),
                H("upper pow"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The parameterized upper pow statement supplies a live step in the actual unitary geometry or prescribed ordered-product construction. Its Lean telescope retains every field, rank, involution, input and equality hypothesis shown."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("unitary-unitarypositivesylow-upper-pow-diag"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/Unitary/UnitaryPositiveSylow.upper_pow_diag"),
                H("upper pow diag"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The parameterized upper pow diag statement supplies a live step in the actual unitary geometry or prescribed ordered-product construction. Its Lean telescope retains every field, rank, involution, input and equality hypothesis shown."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("unitary-unitarypositivesylow-unitriangular-of-p-power"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/Unitary/UnitaryPositiveSylow.unitriangular_of_p_power"),
                H("unitriangular of p power"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Any actual upper triangular p-power-order SL matrix in defining characteristic has diagonal one, by the Frobenius power identity."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("unitary-unitarypositivesylow-positiveu-maximal"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/Unitary/UnitaryPositiveSylow.positiveU_maximal"),
                H("positiveU maximal"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Actual positive unitary U is maximal among p-subgroups. The proof uses its proved intrinsic normalizer and the native normalizer condition for finite p-groups; it assumes neither the unitary group order nor an index."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("unitary-unitarypositivesylow-positiveusylow"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/Unitary/UnitaryPositiveSylow.positiveUSylow"),
                H("positiveUSylow"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Genuine native Sylow with exactly the actual positive-unitriangular SU carrier."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("unitary-unitarypositivesylow-positiveusylow-tosubgroup"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/Unitary/UnitaryPositiveSylow.positiveUSylow_toSubgroup"),
                H("positiveUSylow toSubgroup"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The parameterized positiveUSylow toSubgroup statement supplies a live step in the actual unitary geometry or prescribed ordered-product construction. Its Lean telescope retains every field, rank, involution, input and equality hypothesis shown."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("unitary-unitarypositivesylow-exists-positiveu-sylow"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/Unitary/UnitaryPositiveSylow.exists_positiveU_sylow"),
                H("exists positiveU sylow"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The parameterized exists positiveU sylow statement supplies a live step in the actual unitary geometry or prescribed ordered-product construction. Its Lean telescope retains every field, rank, involution, input and equality hypothesis shown."))),
                DescribeRole.Theorem),
            Paragraph(Text("These parameterized results and their consumed helpers support proofs about actual matrix groups over finite fields. Every displayed Lean statement retains its original hypotheses. This package contains no finite enumeration or benchmark-instance deposit. The source geometry is Nikolov and Segal, On finitely generated profinite groups, II: Products in quasisimple groups, Annals of Mathematics165 (2007),239-273, DOI10.4007/annals.2007.165.239. The proof implementation is repository-derived and no originality claim is made. Bare arbitrary automorphism classification, small-field/tiny-rank coverage for the prescribed products, all-family exhaustion and strong completeness are separate obligations. Escape registration is unfinished under CLAUDE3.9 and issue12291; this is not declared_validated registration.")))));
}
