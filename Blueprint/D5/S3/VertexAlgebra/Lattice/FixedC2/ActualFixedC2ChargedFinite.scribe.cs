using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.Lattice.FixedC2;

internal sealed class ActualFixedC2ChargedFiniteDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/Lattice/FixedC2/ActualFixedC2ChargedFinite.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finite-dimensional module over the neutral image contains all charged single-oscillator classes.",
        H("Finite Spans for Charged Ground States and Single Oscillators"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("actual-fixed-c2-charged-single-span"),
                DeclarationHandle.Create(Prefix + "leechChargedSingleSpan"),
                H("The span of neutral multiples of the ground and first oscillators"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a fixed charge c, use the ground class and the first "
                    + "oscillator class in each Leech basis direction as generators. For each "
                    + "generator take the image of the neutral subspace under multiplication by "
                    + "that generator. Their sum is the indicated charged submodule."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("actual-fixed-c2-charged-single-span-finite"),
                DeclarationHandle.Create(Prefix + "leech_charged_single_span_finite"),
                H("The charged span is finite-dimensional"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The neutral image is finite-dimensional over the complex "
                    + "numbers. Its image under multiplication by any generator is finite-dimensional, "
                    + "and the sum is indexed by the ground and the finitely many basis directions."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actual-fixed-c2-charged-single-span-multiplication"),
                DeclarationHandle.Create(Prefix + "leech_charged_single_span_mul_mem"),
                H("Neutral multiplication preserves the charged span"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The neutral image is a subalgebra containing the unit. "
                    + "The unit puts each generator in its own summand, and associativity absorbs "
                    + "a neutral multiplier into the neutral factor of each product. This gives "
                    + "stability under the actual neutral (-1)-mode on representatives."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actual-fixed-c2-charged-oscillator-in-single-span"),
                DeclarationHandle.Create(Prefix + "leech_charged_oscillator_class_mem"),
                H("All single oscillators on a nonzero charge belong to the span"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A nonzero Leech charge has squared norm at least four. "
                    + "Each weighted quadratic mode on its ground state comes from multiplication "
                    + "by a neutral class and thus lies in the charged span after taking the quotient. "
                    + "The single-oscillator isolation applies in the inverse image of this span, "
                    + "which contains intrinsic C2. The first oscillators are already generators."))),
                DescribeRole.Theorem))));
}
