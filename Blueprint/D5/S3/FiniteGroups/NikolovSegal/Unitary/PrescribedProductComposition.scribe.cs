using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.NikolovSegal.Unitary;

internal sealed class PrescribedProductCompositionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "In an arbitrary group, ordered corrected automorphism value sets concatenate through Fin-indexed tuples. The proof transports corrections through genuine inner automorphisms and retains target-independent correction choices. These helpers are consumed by the five-block intrinsic SU construction.",
        H("Prescribed Product Composition"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("unitary-prescribedproductcomposition-covers"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/Unitary/PrescribedProductComposition.Covers"),
                H("Covers"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("One genuine right-inner correction is selected before all targets in T. The full prescribed tuple and original divisor powers are retained."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("unitary-prescribedproductcomposition-covers-append"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/Unitary/PrescribedProductComposition.covers_append"),
                H("covers append"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Consume two consecutive coverage blocks without reordering their values. The resulting correction still precedes every target of the set product."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("unitary-prescribedproductcomposition-covers-of-left-inner"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/Unitary/PrescribedProductComposition.covers_of_left_inner"),
                H("covers of left inner"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A genuine left inner change of the supplied automorphisms can be absorbed into right-inner corrections, before any target is chosen."))),
                DescribeRole.Theorem),
            Paragraph(Text("The results concern special-unitary matrix groups over finite fields. Their geometric setting is Nikolov and Segal, On finitely generated profinite groups, II: Products in quasisimple groups, Annals of Mathematics 165 (2007), 239-273, DOI 10.4007/annals.2007.165.239. Prescribed-product statements retain their field-size, rank and automorphism hypotheses.")))));
}
