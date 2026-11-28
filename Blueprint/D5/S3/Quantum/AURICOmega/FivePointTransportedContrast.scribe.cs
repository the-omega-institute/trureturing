using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.AURICOmega;

internal sealed class FivePointTransportedContrastDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Which reading differences are possible when both transported points enter the Gram form?",
        H("Five-point contrasts with bilateral transport entries"),
        Blocks(Describe.Lean(DescribeId.Create("transported-contrast"),
            DeclarationHandle.Create(
                "D5/S3/Quantum/AURICOmega/FivePointTransportedContrast.exists_transported_readings_iff"),
            H("The exact rational range with two transported points"),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("Fix rational t between zero and one and a rational contrast d. "
                    + "Use the point order x, y, z, w, v, with w and v the two transported points. "
                    + "The symmetric matrix has unit diagonal and nonnegative entries. "
                    + "The pairs xy, zw, and zv all read t. The pairs xz and yv both read a, "
                    + "and yz and xw both read b. The three other entries are free. A matrix "
                    + "with nonnegative quadratic form on every rational weight vector and "
                    + "a minus b equal to d exists exactly when d squared is within the following bound.")),
                Paragraph(Text("For t at most one half, the bound is (1 − t²)². "
                    + "For t greater than one half with (t − 1/2)² at most 1 − t², "
                    + "it is (5/4 − t)². In the remaining case it is (2t − 1)²(1 − t²).")),
                Paragraph(Text("The same classification and witnesses hold over every linearly "
                    + "ordered field. The rational specialization fixes the scalar domain "
                    + "used for the five local transport readings.")),
                Paragraph(Text("Exchange x with y and w with v to reverse the contrast. "
                    + "For a nonnegative contrast, delete v and split the four-point form "
                    + "using the simultaneous exchanges of x with z and y with w. The resulting "
                    + "two binary forms restrict the contrast. In each range a four-point "
                    + "witness can be chosen with the yw entry zero and b at most both t and a.")),
                Paragraph(Text("For the fifth point take its projection in the span of y and z "
                    + "with coefficients (a − bt)/(1 − b²) and (t − ba)/(1 − b²). "
                    + "The witnesses have b strictly below one, and both coefficients are "
                    + "nonnegative. Testing the residual of x with the coefficients reversed "
                    + "shows that the fifth diagonal can be filled by nonnegative slack. "
                    + "The construction realizes the prescribed Gram readings on these five points. Extending "
                    + "them to a kernel on an entire heap is a separate existence problem."))),
            DescribeRole.Theorem)),
        []));
}
