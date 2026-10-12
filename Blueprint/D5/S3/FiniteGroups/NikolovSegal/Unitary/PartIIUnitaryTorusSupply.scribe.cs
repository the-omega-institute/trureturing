using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.NikolovSegal.Unitary;

internal sealed class PartIIUnitaryTorusSupplyDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual part iiunitary torus supply supplies the parameterized matrix, finite-field or ordered-product identities consumed by the whole-SU K5 width and intrinsic prescribed-product proof paths. All original hypotheses and actual carriers are retained; this source provides no oracle for bare automorphism recognition.",
        H("Part IIUnitary Torus Supply"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("unitary-partiiunitarytorussupply-actual-steinberg-iff-hermitian"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/Unitary/PartIIUnitaryTorusSupply.actual_steinberg_iff_hermitian"),
                H("actual steinberg iff hermitian"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The literal anti-diagonal Hermitian matrix equation is equivalent to Fix(field/inverse-transpose); neither presentation assumes unitary coverage. This connects the torus arithmetic to actual SU witnesses."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("unitary-partiiunitarytorussupply-actual-even-unitary-upper-torus-values"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/Unitary/PartIIUnitaryTorusSupply.actual_even_unitary_upper_torus_values"),
                H("actual even unitary upper torus values"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("One genuine SU torus before every upper SU target, even ranks>=4. The complete finite-field separation proof is consumed, not assumed."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("unitary-partiiunitarytorussupply-actual-odd-unitary-upper-torus-values"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/Unitary/PartIIUnitaryTorusSupply.actual_odd_unitary_upper_torus_values"),
                H("actual odd unitary upper torus values"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The same actual full-upper-unitary kernel in every odd rank>=3. The central norm-one diagonal correction is the proved arithmetic one."))),
                DescribeRole.Theorem),
            Paragraph(Text("The results concern special-unitary matrix groups over finite fields. Their geometric setting is Nikolov and Segal, On finitely generated profinite groups, II: Products in quasisimple groups, Annals of Mathematics 165 (2007), 239-273, DOI 10.4007/annals.2007.165.239. Prescribed-product statements retain their field-size, rank and automorphism hypotheses.")))));
}
