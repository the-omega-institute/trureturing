using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Faithfulness;

internal sealed class JointFaithfulnessLeibnizCriterionDocument : IScribeDocumentDefinition
{
    private const string DeclarationPrefix =
        "D5/S3/ConceptDynamics/Faithfulness/JointFaithfulnessLeibnizCriterion.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Joint faithfulness is exactly state separation by an indexed concept family, and "
            + "constant readouts show that the condition is substantive.",
        H("Joint Faithfulness and the Leibniz Criterion"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("joint-faithfulness-leibniz-criterion"),
                DeclarationHandle.Create(DeclarationPrefix + "joint_faithfulness_tfae"),
                H("Joint faithfulness, point separation, and diagonal kernels coincide"),
                StatementSource.FromAuthor(JointFaithfulnessFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For an indexed family of readouts q_i : X -> V_i, the joint readout "
                            + "records every component value at once. It is injective exactly "
                            + "when equality of all component readings forces equality of the "
                            + "underlying states.")),
                    Paragraph(Text(
                        "The kernel of the family is the intersection of the component kernels. "
                            + "A pair lies in this intersection precisely when every readout "
                            + "assigns the pair equal values, so point separation says that this "
                            + "intersection contains no pairs beyond the equality diagonal.")),
                    Paragraph(Text(
                        "Equality of two dependent joint outputs is componentwise equality. "
                            + "This identifies joint-readout injectivity with point separation; "
                            + "the same componentwise condition identifies point separation with "
                            + "equality between the joint kernel and the diagonal."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("constant-concept-family-is-not-jointly-faithful"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "constant_concept_family_not_jointly_faithful"),
                H("A constant concept family is not jointly faithful"),
                StatementSource.FromAuthor(ConstantFamilyFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Take the family indexed by the singleton type whose only readout maps "
                            + "both Boolean states to the unique element of Unit. The distinct "
                            + "states false and true therefore have equal readings in every "
                            + "component and equal joint outputs.")),
                    Paragraph(Text(
                        "Consequently the joint readout is not injective and the point-separation "
                            + "condition fails. The pair (false, true) also belongs to every "
                            + "component kernel while lying off the Boolean diagonal, so the "
                            + "joint kernel is not the diagonal."))),
                DescribeRole.Theorem))));

    private static Formula Read(Formula index, Formula state) =>
        Call("q", index, state);

    private static Formula SeparationFormula(
        Formula index,
        Formula indexDomain,
        Formula state,
        Formula left,
        Formula right) =>
        Seq(
            Forall, Sp, left, Comma, Sp, right, Colon, Sp, state, Comma, Sp,
            Open, Forall, Sp, index, Colon, Sp, indexDomain, Comma, Sp,
            Equal(Read(index, left), Read(index, right)), Close,
            Sp, Rightarrow, Sp, Equal(left, right));

    private static Formula JointFaithfulnessFormula()
    {
        Formula indexType = F.Id("I");
        Formula state = F.Id("X");
        Formula valueFamily = F.Id("V");
        Formula index = F.Id("i");
        Formula readouts = F.Id("q");
        Formula left = F.Id("x");
        Formula right = F.Id("y");
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));

        return Disp(new Formula.Aligned([
            Seq(
                Forall, Sp, indexType, Comma, Sp, state, Colon, Sp, type, Comma, Sp,
                valueFamily, Colon, Sp, indexType, Sp, To, Sp, type, Comma),
            Seq(
                readouts, Colon, Sp, Forall, Sp, index, Colon, Sp, indexType, Comma, Sp,
                state, Sp, To, Sp, Call("V", index), Comma),
            Seq(
                Call("Injective", Call("jointReadout", readouts)),
                Sp, Iff, Sp,
                Open, SeparationFormula(index, indexType, state, left, right), Close,
                Sp, Iff, Sp,
                Equal(Call("jointKernel", readouts), Call("diagonal", state)), Dot),
        ]));
    }

    private static Formula ConstantFamilyFormula()
    {
        Formula unit = F.Id("Unit");
        Formula boolean = F.Id("Bool");
        Formula readouts = F.Id("q");
        Formula index = F.Id("i");
        Formula left = F.Id("x");
        Formula right = F.Id("y");
        Formula distinctIndistinguishableStates = Seq(
            Exists, Sp, left, Comma, Sp, right, Colon, Sp, boolean, Comma, Sp,
            left, Sp, Neq, Sp, right, Sp, Land, Sp,
            Forall, Sp, index, Comma, Sp,
            Equal(Read(index, left), Read(index, right)));

        return Disp(new Formula.Aligned([
            Seq(
                Exists, Sp, readouts, Colon, Sp, Open,
                Forall, Sp, index, Colon, Sp, unit, Comma, Sp,
                boolean, Sp, To, Sp, unit, Close, Comma),
            Seq(Open, distinctIndistinguishableStates, Close),
            Seq(
                Land, Sp, Neg, Sp,
                Call("Injective", Call("jointReadout", readouts))),
            Seq(
                Land, Sp, Neg, Sp, Open,
                SeparationFormula(index, unit, boolean, left, right), Close),
            Seq(
                Land, Sp,
                NotEqual(Call("jointKernel", readouts), Call("diagonal", boolean)), Dot),
        ]));
    }
}
