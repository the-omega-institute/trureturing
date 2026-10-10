using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.NikolovSegal.Unitary;

internal sealed class PartIIUnitaryRadicalTorusDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual part iiunitary radical torus supplies the parameterized matrix, finite-field or ordered-product identities consumed by the whole-SU K5 width and intrinsic prescribed-product proof paths. All original hypotheses and actual carriers are retained; this source provides no oracle for bare automorphism recognition.",
        H("Part IIUnitary Radical Torus"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("unitary-partiiunitaryradicaltorus-unitaryradical"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/Unitary/PartIIUnitaryRadicalTorus.unitaryRadical"),
                H("unitaryRadical"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Definition6.6(ii), with the actual V support and true Steinberg law."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("unitary-partiiunitaryradicaltorus-actual-unitary-radical-regular-torus-values"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/Unitary/PartIIUnitaryRadicalTorus.actual_unitary_radical_regular_torus_values"),
                H("actual unitary radical regular torus values"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Genuine rank-independent-support torus kernel for V*. Separation is required ONLY on first-row/last-column roots, not every matrix root. ONE actual determinant-one unitary h precedes ALL targets and all witnesses remain in V*, including the noncommutative corner coordinate."))),
                DescribeRole.Theorem),
            Paragraph(Text("The results concern special-unitary matrix groups over finite fields. Their geometric setting is Nikolov and Segal, On finitely generated profinite groups, II: Products in quasisimple groups, Annals of Mathematics 165 (2007), 239-273, DOI 10.4007/annals.2007.165.239. Prescribed-product statements retain their field-size, rank and automorphism hypotheses.")))));
}
