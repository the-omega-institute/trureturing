using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.SpacetimeArithmetic;

internal sealed class RichRationalDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ConceptDynamics/SpacetimeArithmetic/RichRational.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual guarded pairs of balanced histories support exact rational arithmetic.",
        H("Rich Rational Histories"),
        Blocks(
            Paragraph(Text("Formula projection does not express the dependent archive carriers here. "
                + "The resolving Lean handles carry the typed statements; this narrative supplies no separate formula.")),
            Describe.Lean(
                DescribeId.Create("fraction-carrier"),
                DeclarationHandle.Create(Prefix + "Fraction"),
                H("Two balanced histories and a nonzero denominator"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Each component is a balanced rich history with its actual archive, context and selection. "
                        + "The stored denominator proof states that its integer readout is nonzero. Rational readout "
                        + "divides the two integer readouts in Rat."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("cross-kernel"),
                DeclarationHandle.Create(Prefix + "cross_iff_readout"),
                H("Cross-products characterize equal readout"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Integer cross-product equality is equivalent to rational readout equality by injective "
                        + "integer casts and the standard fraction cancellation theorem. The kernel setoid is on "
                        + "these actual pairs; its equivalence laws give reflexivity, symmetry and transitivity."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("inverse-domain"),
                DeclarationHandle.Create(Prefix + "inverse_guard_iff"),
                H("The inverse guard is numerical nonzeroness"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The numerator must read nonzero for the guarded inverse to swap the two histories. "
                        + "Division has the same condition on the divisor numerator. Both guards are invariant under "
                        + "cross-product equivalence."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("native-addition"),
                DeclarationHandle.Create(Prefix + "add_readout"),
                H("Native addition has the exact sum readout"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The numerator is the parallel composition of the product of the first numerator with the "
                        + "second denominator, followed by the product of the second numerator with the first "
                        + "denominator. The denominator is the product of the two denominators. Closure and the "
                        + "equation use the actual B2 operations."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("native-product"),
                DeclarationHandle.Create(Prefix + "mul_readout"),
                H("Native multiplication has the exact product readout"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The numerator multiplies the two numerators and the denominator multiplies the two "
                        + "denominators, retaining the generated product archives. Nonzero integer products give "
                        + "denominator closure."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("native-negation"),
                DeclarationHandle.Create(Prefix + "neg_readout"),
                H("Event complement negates the readout"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The numerator uses B1 event complement in its balanced context. The denominator is "
                        + "retained literally."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("native-inverse"),
                DeclarationHandle.Create(Prefix + "inv_readout"),
                H("Guarded swapping gives the reciprocal readout"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The inverse swaps numerator and denominator and requires the numerator readout to be "
                        + "nonzero. This partial rich operation is not extended at zero."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("native-division"),
                DeclarationHandle.Create(Prefix + "div_readout"),
                H("Guarded cross-products give the division readout"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Division uses the first numerator times the divisor denominator over the first denominator "
                        + "times the divisor numerator. The divisor-numerator guard makes that denominator nonzero. "
                        + "Congruence is proved with guards for both representatives."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("integer-retention"),
                DeclarationHandle.Create(Prefix + "integerEmbedding_readout"),
                H("Integer embedding keeps the input history"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The numerator is exactly the supplied balanced history. The denominator is the arbitrary-d "
                        + "canonical representative of one. Its rational readout is the integer cast of the supplied "
                        + "history readout."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/ConceptDynamics/Spacetime/ParallelComposition")),
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/ConceptDynamics/Spacetime/GeneratedProduct")),
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/ConceptDynamics/Spacetime/ComplementFibers"))
        ]));
}
