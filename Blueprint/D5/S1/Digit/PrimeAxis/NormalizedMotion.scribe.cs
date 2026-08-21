using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Digit.PrimeAxis;

internal sealed class NormalizedMotionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        var t = Id("t");

        var step = Equal(
            Call("motion", Add(t, Num(1))),
            Call("normalize", Add(Call("motion", t), Id("u"))));

        var decoded = Equal(
            Call("decode", Call("motion", t)),
            Multiply(Call("decode", Id("z")),
                new Formula.Power(Call("decode", Id("u")), t)));

        const string declarationPrefix = "D5/S1/Digit/PrimeAxis/NormalizedMotion.";

        return DocumentDefinition.Create(ScribeNode.Create(
            "Iterated normalized motion stays canonical and decodes to a product of steps.",
            H("Normalized Motion"),
            Blocks(
                Paragraph(Text(
                    "The clause reads the motion as a state step: an accumulator advances by "
                        + "the control, and the encoding advances by adding the control's code "
                        + "and renormalizing, so motion never produces an illegal encoding.")),
                Paragraph(Text(
                    "One step of that already existed, together with its uniqueness and the "
                        + "multiplicativity of its decoder. What did not exist is the "
                        + "iteration: a trajectory of states, and the decoder's behaviour along "
                        + "it. Legality along the trajectory is structural, since the state "
                        + "type carries canonicity as a field; the content is that the decoder "
                        + "turns the whole trajectory into a power.")),
                Describe.Lean(
                    DescribeId.Create("motion-never-leaves-the-canonical-encodings"),
                    DeclarationHandle.Create(declarationPrefix + "motion_canonical"),
                    H("Motion never leaves the canonical encodings"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(step)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "Every reachable state is a table, and a table is canonical on every "
                            + "axis by construction, so no step can produce adjacent ones, a "
                            + "carry, or a repeated activation."))),
                    DescribeRole.Lemma),
                Describe.Lean(
                    DescribeId.Create("one-step-multiplies-the-decoded-value"),
                    DeclarationHandle.Create(declarationPrefix + "decode_motion_succ"),
                    H("One step multiplies the decoded value"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(
                        Equal(Call("decode", Call("motion", Add(t, Num(1)))),
                            Multiply(Call("decode", Call("motion", t)),
                                Call("decode", Id("u")))))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "Addition of codes followed by normalization is multiplication of the "
                            + "decoded values, which is the existing one-step result applied "
                            + "along the trajectory."))),
                    DescribeRole.Lemma),
                Describe.Lean(
                    DescribeId.Create("the-trajectory-decodes-to-a-power-of-the-control"),
                    DeclarationHandle.Create(declarationPrefix + "decode_motion"),
                    H("The trajectory decodes to a power of the control"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(decoded)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "Motion in the encoding is multiplication in the value: after any "
                            + "number of steps the decoded state is the initial value times "
                            + "that many copies of the control."))),
                    DescribeRole.Theorem))));
    }
}
