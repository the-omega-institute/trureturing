using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.NikolovSegal.Unitary;

internal sealed class UnitaryWidthRankThreeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual unitary width rank three supplies the parameterized matrix, finite-field or ordered-product identities consumed by the whole-SU K5 width and intrinsic prescribed-product proof paths. All original hypotheses and actual carriers are retained; this source provides no oracle for bare automorphism recognition.",
        H("Unitary Width Rank Three"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("unitary-unitarywidthrankthree-rankthree-prepare-first"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/Unitary/UnitaryWidthRankThree.rankThree_prepare_first"),
                H("rankThree prepare first"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("One actual lower root creates a nonzero first coordinate when necessary. Isotropy excludes a row supported on the middle coordinate."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("unitary-unitarywidthrankthree-rankthree-clear-last"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/Unitary/UnitaryWidthRankThree.rankThree_clear_last"),
                H("rankThree clear last"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A unit last pivot is cleared by one genuine lower short root, retaining its central quadratic term in every characteristic."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("unitary-unitarywidthrankthree-rankthree-four-factor"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/Unitary/UnitaryWidthRankThree.rankThree_four_factor"),
                H("rankThree four factor"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Actual SU3 has four alternating unitriangular factors over EVERY finite quadratic field, including F4/F9. Relative norm and trace are used in the constructed roots; no low-field exception or decomposition input occurs."))),
                DescribeRole.Theorem),
            Paragraph(Text("The results concern special-unitary matrix groups over finite fields. Their geometric setting is Nikolov and Segal, On finitely generated profinite groups, II: Products in quasisimple groups, Annals of Mathematics 165 (2007), 239-273, DOI 10.4007/annals.2007.165.239. Prescribed-product statements retain their field-size, rank and automorphism hypotheses.")))));
}
