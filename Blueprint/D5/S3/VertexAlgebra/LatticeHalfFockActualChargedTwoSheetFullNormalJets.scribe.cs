using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra;

internal sealed class LatticeHalfFockActualChargedTwoSheetFullNormalJetsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/LatticeHalfFockActualChargedTwoSheetFullNormalJets.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/VertexAlgebra/flm1988monster");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual charged retained-energy fields and literal two-sheet normal jets",
        H("Charged Two-Sheet Full Normal Jets"), Blocks(
            Paragraph(Text("The construction keeps the original unrestricted lattice, determinant-unit witness, integral charges, signed pairing, chargeScalar, and actual tensor target. The retained Gaussian is applied through the existing native correction evaluation, so every asserted equality remains an equality of the original fields or their original integer modes on arbitrary targets.")),
            Describe.Lean(DescribeId.Create("two-sheet-composition"),
                DeclarationHandle.Create(Prefix + "two_sheet_composition"),
                H("Formal Two-Sheet Composition"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source), Blocks(Paragraph(Text(
                    "For t=4u/(1-u)^2 with 1-u nonzero, the formal composition identity t(1-u)^2=4u is proved directly. This is only the algebraic coordinate relation; it does not by itself identify either charged chart with the original field."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("retained-energy-field-recurrence"),
                DeclarationHandle.Create(Prefix + "retained_energy_field_recurrence"),
                H("Whole-Field Retained-Energy Recurrence"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source), Blocks(Paragraph(Text(
                    "The original full retained polynomial recurrence is transported through nativeCorrectionEvaluation and the genuine Ytw source bridge. It is therefore consumed by a whole field, not by a scalar evaluation or vacuum-only projection."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("retained-energy-normal-jet-recurrence"),
                DeclarationHandle.Create(Prefix + "retained_energy_normal_jet_recurrence"),
                H("Every Integer Normal Jet Satisfies the Recurrence"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source), Blocks(Paragraph(Text(
                    "Applying an arbitrary original mode to an arbitrary actual target tensor gives the retained recurrence componentwise. The target is unrestricted and no polynomial coefficient is discarded."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("retained-energy-field-finite-gaussian"),
                DeclarationHandle.Create(Prefix + "retained_energy_field_finite_gaussian"),
                H("Whole-Field Finite Gaussian Expansion"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source), Blocks(Paragraph(Text(
                    "The compiled finite expansion retains every normal-energy label, the actual chargedEnergyGaussian coefficient, and the independent X(none) shift before native field evaluation."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("retained-energy-normal-jet-finite-gaussian"),
                DeclarationHandle.Create(Prefix + "retained_energy_normal_jet_finite_gaussian"),
                H("Finite Gaussian Expansion At Every Normal Jet"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source), Blocks(Paragraph(Text(
                    "The whole-field finite expansion is projected to each original integer mode and arbitrary actual target tensor by linearity of the HVertexOperator coefficient map."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("charged-product-two-sheet-normalization"),
                DeclarationHandle.Create(Prefix + "charged_product_two_sheet_normalization"),
                H("Exact Charged Product Normalization"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source), Blocks(Paragraph(Text(
                    "The exact charged tensor ordered-product theorem is consumed with its literal chargeScalar product and halfContraction finsum. No auxiliary chart binomial or replacement target is introduced."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("charged-product-two-sheet-normalization-below-start"),
                DeclarationHandle.Create(Prefix + "charged_product_two_sheet_normalization_below_start"),
                H("Both Literal Charts Vanish Below Their Signed Starts"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source), Blocks(Paragraph(Text(
                    "The exact plus and minus below-start bounds are applied to the charged product target, preserving the signed g distinction and the negative-charge monodromy already present in the original chart supplier."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("source-normal-jet-gaussian-closed"),
                DeclarationHandle.Create(Prefix + "source_normal_jet_gaussian_closed"),
                H("Source Gaussian Closure On Every Normal Jet"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source), Blocks(Paragraph(Text(
                    "The existing genuine source-field Gaussian theorem is consumed at every integer mode and arbitrary actual target. It remains a source-power bridge and does not claim complete charged all-j closure."))), DescribeRole.Theorem),
            Paragraph(Text("These results close the actual whole-field retained Gaussian consumer and its arbitrary normal jets, and expose the exact charged product normalization and both below-start chart branches. The regular charged scalar ratio, complete Lambda/J jet comparison, twisted Jacobi closure, and both original all-j endpoint identities remain open. The broader moonshine, VOA, CFT, anomaly, fusion, string, and AdS/CFT objective remains active and is not claimed complete by this scoped module.")))));
}
