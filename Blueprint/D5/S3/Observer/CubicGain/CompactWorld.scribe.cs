using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.CubicGain;

internal sealed class CompactWorldDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The closure equations hold for every actual strict parent, using the same original gain and fixed drift throughout",
        H("CompactWorld"),
        Blocks(
        Paragraph(Text("The closure equations hold for every actual strict parent, using the same original gain and fixed drift throughout. Multiplication by U=1+2b applies uniformly to the entire gain polynomial, and gain_scale expresses the linearity of interpolation and gives its clock-four equation.")),
        Paragraph(Text("Bounded fifth responses already bound ε and the original whole gain. For b≤1, U≤3 gives a bound for every scaled gain sample. For b≥1, U/j≤3, U/n≤3 and U/T≤2 bound scaled samples 1,3,2 respectively. The scaled clock-four reading and the cubic fourth-difference identity then bound sample zero. This establishes a uniform bound on the whole scaled gain, including b→∞.")),
        Describe.Lean(
            DescribeId.Create("cubic-gain-gain-scale"),
            DeclarationHandle.Create("D5/S3/Observer/CubicGain/CompactWorld.gain_scale"),
            H("gain scale"),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("For every sample vector a and real scalars t,s, multiplying all four samples by t multiplies the whole interpolated gain at s by t."))),
            DescribeRole.Theorem),
        Describe.Lean(
            DescribeId.Create("cubic-gain-closureworld-actual"),
            DeclarationHandle.Create("D5/S3/Observer/CubicGain/CompactWorld.closureWorld_actual"),
            H("closureWorld actual"),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("Every strict parent gives a ClosureWorld with its compact source, drift offset, original gain, whole scaled gain and actual fifth and sixth responses."))),
            DescribeRole.Theorem),
        Describe.Lean(
            DescribeId.Create("cubic-gain-bounded-fifth-bounds-scaled-gain"),
            DeclarationHandle.Create("D5/S3/Observer/CubicGain/CompactWorld.bounded_fifth_bounds_scaled_gain"),
            H("bounded fifth bounds scaled gain"),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("For every real M there are bounds D,G,H such that every strict parent with |P₅|≤M has |ε|≤D, |aᵢ|≤G and |(Ua)ᵢ|≤H for all four original sample indices."))),
            DescribeRole.Theorem))));
}
