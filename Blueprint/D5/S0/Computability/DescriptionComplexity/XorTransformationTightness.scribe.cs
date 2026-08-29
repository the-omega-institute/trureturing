using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Computability.DescriptionComplexity;

internal sealed class XorTransformationTightnessDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Incompressible masks make binary XOR transformation prices tight within a logarithmic gap.",
        H("Binary XOR Transformation Tightness"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("binary-xor-transformation-price-is-logarithmically-tight"),
                DeclarationHandle.Create(
                    "D5/S0/Computability/DescriptionComplexity/XorTransformationTightness"
                    + ".xor_transformation_description_tight"),
                H("An incompressible XOR mask attains the description bound"),
                StatementSource.FromAuthor(TightnessFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The binder M : BinaryDescriptionMachine(c) is the exact Lean interface for "
                        + "one fixed binary description machine. Its object and transformation "
                        + "systems use binary-list code length, object realization is functional, "
                        + "and it supplies concrete XOR, zero-string, and application compilers "
                        + "with the displayed fixed and logarithmic overheads.")),
                    Paragraph(Text(
                        "There are 2^l length-l binary strings but only 2^l - 1 binary programs "
                        + "shorter than l. Functionality therefore leaves a mask r with object "
                        + "description complexity at least l. This is a counting construction, not "
                        + "an incompressibility premise.")),
                    Paragraph(Text(
                        "Pointwise addition in Fin 2 is the canonical bitwise XOR. It is involutive "
                        + "and sends the zero string to r. The concrete zero compiler bounds K(0^l) "
                        + "by 2 log_2(l+1)+c, giving the public information-difference lower bound.")),
                    Paragraph(Text(
                        "The concrete XOR compiler gives K_transform(xor_r) <= l+c. Applying the "
                        + "existing transformation-description compiler to xor_r(0)=r yields the "
                        + "opposite lower bound l-[2 log_2(l+1)+2c]. Thus the witness name price "
                        + "is squeezed to within the source's logarithmic gap.")),
                    Paragraph(Text(
                        "Pinned Mathlib supplies finite binary carriers and arithmetic but no "
                        + "Kolmogorov-complexity or incompressible-XOR theorem. The repository search "
                        + "found only the imported general transformation bound, whose own projection "
                        + "marks this tightness construction as residual."))),
                DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create(
            "D5/S0/Computability/DescriptionComplexity/TransformationDescriptionBound"))]));

    private static Formula TightnessFormula()
    {
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));
        Formula overhead = F.Id("c"), machine = F.Id("M"), length = F.Id("l");
        Formula mask = F.Id("r"), zero = D(0);
        Formula bitString = Seq(Call("Fin", length), Sp, To, Sp, Call("Fin", D(2)));
        Formula xor = Call("pointwiseXor", mask);
        Formula objectK = Seq(F.Id("K"), Underscore, Grp(machine, Comma, length));
        Formula transformK =
            Seq(F.Id("Ktransform"), Underscore, Grp(machine, Comma, length));
        Formula ObjectComplexity(Formula value) => Seq(objectK, Open, value, Close);
        Formula TransformComplexity(Formula value) => Seq(transformK, Open, value, Close);
        Formula logTerm = Seq(D(2), Sp, F.Id("log"), Underscore, D(2),
            Open, length, Sp, Plus, Sp, D(1), Close);
        Formula informationGap = Seq(logTerm, Sp, Plus, Sp, overhead);
        Formula transformationGap =
            Seq(logTerm, Sp, Plus, Sp, overhead, Sp, Plus, Sp, overhead);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, overhead, Colon, Sp, naturals, Comma, Sp,
            machine, Colon, Sp, Call("BinaryDescriptionMachine", overhead), Comma, Sp,
            length, Colon, Sp, naturals, Comma, RowBreak, Grp(),
            Exists, Sp, mask, Colon, Sp, bitString, Comma, RowBreak, Grp(),
            length, Sp, Leq, Sp, ObjectComplexity(mask), Sp, Land, RowBreak, Grp(),
            Call("Involutive", xor), Sp, Land, RowBreak, Grp(),
            Call("pointwiseXor", mask, zero), Sp, Eq, Sp, mask, Sp, Land, RowBreak, Grp(),
            length, Sp, Minus, Sp, Grp(informationGap), Sp, Leq, Sp,
            ObjectComplexity(mask), Sp, Minus, Sp, ObjectComplexity(zero), Sp, Land,
            RowBreak, Grp(),
            TransformComplexity(xor), Sp, Leq, Sp,
            length, Sp, Plus, Sp, overhead, Sp, Land, RowBreak, Grp(),
            length, Sp, Minus, Sp, Grp(transformationGap), Sp, Leq, Sp,
            TransformComplexity(xor), Dot,
            End, Grp(F.Id("gathered"))));
    }
}
