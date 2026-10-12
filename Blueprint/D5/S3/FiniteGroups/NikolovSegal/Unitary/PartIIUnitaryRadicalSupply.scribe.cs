using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.NikolovSegal.Unitary;

internal sealed class PartIIUnitaryRadicalSupplyDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual part iiunitary radical supply supplies the parameterized matrix, finite-field or ordered-product identities consumed by the whole-SU K5 width and intrinsic prescribed-product proof paths. All original hypotheses and actual carriers are retained; this source provides no oracle for bare automorphism recognition.",
        H("Part IIUnitary Radical Supply"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("unitary-partiiunitaryradicalsupply-actual-uniform-unitary-radical-fixed-torus"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/Unitary/PartIIUnitaryRadicalSupply.actual_uniform_unitary_radical_fixed_torus"),
                H("actual uniform unitary radical fixed torus"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A true UNIFORM radical fixed-inner-action result, all ranks k+4 and every original positive divisor power s|q. The Q cutoff 2q+2 precedes all groups/ranks, the same genuine determinant-one unitary h precedes ALL s and ALL targets, and the witness lies in V*, including its corner. No scalar PRODUCT or radical coverage premise is retained. This does not yet handle arbitrary prescribed diagonal/field/graph automorphisms."))),
                DescribeRole.Theorem),
            Paragraph(Text("The results concern special-unitary matrix groups over finite fields. Their geometric setting is Nikolov and Segal, On finitely generated profinite groups, II: Products in quasisimple groups, Annals of Mathematics 165 (2007), 239-273, DOI 10.4007/annals.2007.165.239. Prescribed-product statements retain their field-size, rank and automorphism hypotheses.")))));
}
