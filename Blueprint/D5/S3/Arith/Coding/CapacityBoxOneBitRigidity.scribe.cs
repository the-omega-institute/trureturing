using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Coding;

internal sealed class CapacityBoxOneBitRigidityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Capacity-box unit-edge colours depend only on the axis and layer, and different axes use disjoint sets of bits.",
        H("Capacity Box One-Bit Rigidity"),
        Blocks(Describe.Lean(
            DescribeId.Create("edge-colour"),
            DeclarationHandle.Create(
                "D5/S3/Arith/Coding/CapacityBoxOneBitRigidity.edgeColour"),
            H("Colour of a unit Boolean edge"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(
                "The colour of a unit edge is the unique coordinate at which its two Boolean "
                    + "words differ."))),
            DescribeRole.Definition),
        Describe.Lean(
            DescribeId.Create("unit-edge"),
            DeclarationHandle.Create(
                "D5/S3/Arith/Coding/CapacityBoxOneBitRigidity.UnitEdge"),
            H("Directed capacity edge"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(
                "A unit edge increases one capacity coordinate by one while fixing every other coordinate."))),
            DescribeRole.Definition),
        Describe.Lean(
            DescribeId.Create("one-bit-embedding"),
            DeclarationHandle.Create(
                "D5/S3/Arith/Coding/CapacityBoxOneBitRigidity.OneBitEmbedding"),
            H("One-bit capacity code"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(
                "A one-bit capacity code is injective and maps every unit edge to two Boolean words at Hamming distance one."))),
            DescribeRole.Definition),
        Describe.Lean(
            DescribeId.Create("raise"),
            DeclarationHandle.Create(
                "D5/S3/Arith/Coding/CapacityBoxOneBitRigidity.raise"),
            H("Increase one coordinate"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(
                "The indicated coordinate is increased by one when its value is below capacity."))),
            DescribeRole.Definition),
        Describe.Lean(
            DescribeId.Create("unit-edge-colour"),
            DeclarationHandle.Create(
                "D5/S3/Arith/Coding/CapacityBoxOneBitRigidity.unitEdgeColour"),
            H("Colour of a capacity edge"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(
                "The colour of a capacity edge is the unique bit changed by its image."))),
            DescribeRole.Definition),
        Describe.Lean(
            DescribeId.Create("colour-depends-only-on-layer"),
            DeclarationHandle.Create(
                "D5/S3/Arith/Coding/CapacityBoxOneBitRigidity.colour_depends_only_on_layer"),
            H("Colours are constant across a layer"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(
                "Two edges increasing the same axis from the same starting value have the "
                    + "same colour, regardless of their other coordinates. Lowering those "
                    + "coordinates one at a time connects each edge to the same axis fibre."))),
            DescribeRole.Theorem),
        Describe.Lean(
            DescribeId.Create("different-axes-distinct-colours"),
            DeclarationHandle.Create(
                "D5/S3/Arith/Coding/CapacityBoxOneBitRigidity.different_axes_distinct_colours"),
            H("Different axes use different colours"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(
                "Any two layer edges on distinct axes can be transported to edges with a "
                    + "common starting state. If they changed the same bit, their other "
                    + "endpoints would have equal codes, contradicting injectivity."))),
            DescribeRole.Theorem))));
}
