using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Computability.DescriptionComplexity;

internal sealed class BidirectionalTransformationDescriptionBoundDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Two inverse compilers bound both description costs and their distance.",
        H("Bidirectional Transformation Description Bound"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("bidirectional-transformation-description-bounds"),
                DeclarationHandle.Create(
                    "D5/S0/Computability/DescriptionComplexity/"
                    + "BidirectionalTransformationDescriptionBound."
                    + "bidirectional_transformation_description_bounds"),
                H("Two described transformations bound both endpoint complexities"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Objects and transformations use the canonical description-system family. "
                        + "One application relation records both directions, and each compiler "
                        + "combines an endpoint description with a transformation description.")),
                    Paragraph(Text(
                        "The two application premises state that the forward transformation sends "
                        + "x to y and the reverse transformation sends y to x. Applying the frozen "
                        + "one-way compiler theorem in each direction gives the first two public "
                        + "inequalities.")),
                    Paragraph(Text(
                        "A case split on the ordering of the two endpoint complexities turns their "
                        + "natural-number distance into one subtraction. The corresponding directional "
                        + "bound is then enlarged by the maxima of the transformation costs and fixed "
                        + "compiler overheads.")),
                    Paragraph(Text(
                        "Pinned Mathlib was searched for natural-distance lemmas and supplies "
                        + "Nat.dist_eq_sub_of_le and Nat.dist_eq_sub_of_le_right. The repository-wide "
                        + "description-complexity search found only the imported one-way predecessor; "
                        + "no theorem containing all three public clauses was present."))),
                DescribeRole.Theorem)),
        []));

    private static Formula TheoremFormula()
    {
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula proposition = Seq(Operatorname, Grp(F.Id("Prop")));
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));
        Formula objectType = F.Id("Object"), transformationType = F.Id("Transformation");
        Formula objectCode = F.Id("ObjectCode"), transformationCode = F.Id("TransformationCode");
        Formula objects = F.Id("objects"), transformations = F.Id("transformations");
        Formula applies = F.Id("applies");
        Formula forwardOverhead = F.Id("forwardOverhead");
        Formula reverseOverhead = F.Id("reverseOverhead");
        Formula forwardCompiler = F.Id("forwardCompiler");
        Formula reverseCompiler = F.Id("reverseCompiler");
        Formula forwardTransformation = F.Id("u"), reverseTransformation = F.Id("v");
        Formula x = F.Id("x"), y = F.Id("y");
        Formula complexityOf(Formula system, Formula value) =>
            Seq(new Formula.Subscript(F.Id("K"), system), Open, value, Close);
        Formula appliesTo(Formula transformation, Formula source, Formula target) =>
            Seq(applies, Open, transformation, Comma, source, Comma, target, Close);
        Formula compilerType(Formula overhead) =>
            Call("TransformationCompiler", objects, transformations, objects, applies, overhead);
        Formula maximum(Formula left, Formula right) => Call("max", left, right);
        Formula objectComplexityX = complexityOf(objects, x);
        Formula objectComplexityY = complexityOf(objects, y);
        Formula forwardComplexity = complexityOf(transformations, forwardTransformation);
        Formula reverseComplexity = complexityOf(transformations, reverseTransformation);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, objectType, Comma, Sp, transformationType, Comma, Sp,
            objectCode, Comma, Sp, transformationCode, Colon, Sp, type,
            Comma, RowBreak, Grp(),
            Forall, Sp, objects, Colon, Sp,
            Call("DescriptionSystem", objectType, objectCode),
            Comma, RowBreak, Grp(),
            Forall, Sp, transformations, Colon, Sp,
            Call("DescriptionSystem", transformationType, transformationCode),
            Comma, RowBreak, Grp(),
            Forall, Sp, applies, Colon, Sp, transformationType, Sp, To, Sp,
            objectType, Sp, To, Sp, objectType, Sp, To, Sp, proposition,
            Comma, RowBreak, Grp(),
            Forall, Sp, forwardOverhead, Comma, Sp, reverseOverhead, Colon, Sp, naturals,
            Comma, RowBreak, Grp(),
            Forall, Sp, forwardCompiler, Colon, Sp, compilerType(forwardOverhead),
            Comma, RowBreak, Grp(),
            Forall, Sp, reverseCompiler, Colon, Sp, compilerType(reverseOverhead),
            Comma, RowBreak, Grp(),
            Forall, Sp, forwardTransformation, Comma, Sp, reverseTransformation,
            Colon, Sp, transformationType,
            Comma, RowBreak, Grp(),
            Forall, Sp, x, Comma, Sp, y, Colon, Sp, objectType,
            Comma, RowBreak, Grp(),
            Open, appliesTo(forwardTransformation, x, y), Sp, Land, Sp,
            appliesTo(reverseTransformation, y, x), Close,
            Sp, Rightarrow, Sp, RowBreak, Grp(),
            Open, objectComplexityY, Sp, Leq, Sp, objectComplexityX, Sp, Plus, Sp,
            forwardComplexity, Sp, Plus, Sp, forwardOverhead, Close,
            Sp, Land, Sp, RowBreak, Grp(),
            Open, objectComplexityX, Sp, Leq, Sp, objectComplexityY, Sp, Plus, Sp,
            reverseComplexity, Sp, Plus, Sp, reverseOverhead, Close,
            Sp, Land, Sp, RowBreak, Grp(),
            Call("dist", objectComplexityX, objectComplexityY), Sp, Leq, Sp,
            maximum(forwardComplexity, reverseComplexity), Sp, Plus, Sp,
            maximum(forwardOverhead, reverseOverhead), Dot,
            End, Grp(F.Id("gathered"))));
    }
}
