using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Dialectics;

internal sealed class OneStepClosureFivefoldEquivalenceDocument
    : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "One-step kernel closure is equivalent to complete behavioral closure, exact descent, "
            + "and absence of carry.",
        H("One-Step Closure Fivefold Equivalence"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("one-step-closure-fivefold-equivalence"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/Dialectics/OneStepClosureFivefoldEquivalence."
                        + "one_step_closure_fivefold_equivalence"),
                H("Five closure criteria are equivalent"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For any state type, readout, and deterministic update, equality of the "
                            + "depth-zero and depth-one kernels is equivalent to forward fiber "
                            + "invariance, equality with the complete-itinerary kernel, unique "
                            + "effective descent on the realized image, and absence of carry.")),
                    Paragraph(Text(
                        "The final clause identifies the complementary event: a carry witness "
                            + "exists exactly when the depth-one kernel is a strict refinement "
                            + "of the depth-zero kernel. No finiteness or nonemptiness assumption "
                            + "is used."))),
                DescribeRole.Theorem))));

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula Typed(Formula value, Formula type) =>
        Seq(value, Colon, Sp, type);

    private static Formula TheoremFormula()
    {
        Formula stateType = F.Id("X");
        Formula readoutType = F.Id("B");
        Formula readout = F.Id("q");
        Formula update = F.Id("F");
        Formula left = F.Id("x");
        Formula right = F.Id("y");
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula carry = Call(
            "IsCarryWitness", readout, update, readout, left, right);
        Formula noCarry = Seq(
            Forall, Sp, Typed(Seq(left, Comma, Sp, right), stateType),
            Comma, Sp, Neg, Sp, carry);
        Formula complete = Call("completeItinerary", update, readout);
        Formula currentKernel = Seq(
            F.Id("Setoid"), Dot, F.Id("ker"), Sp, readout);
        Formula completeKernel = Seq(
            F.Id("Setoid"), Dot, F.Id("ker"), Sp, Open, complete, Close);
        Formula zeroKernel = Call("depthZeroKernel", readout);
        Formula oneKernel = Call("depthOneKernel", readout, update);
        Formula conditions = Grp(
            OpenBracket,
            Seq(zeroKernel, Sp, Eq, Sp, oneKernel), Comma, Sp,
            Call("InterfaceCongruence", readout, update), Comma, Sp,
            Seq(currentKernel, Sp, Eq, Sp, completeKernel), Comma, Sp,
            Call("EffectiveDescent", readout, update), Comma, Sp,
            noCarry,
            CloseBracket);
        Formula carryExists = Seq(
            Exists, Sp, Typed(Seq(left, Comma, Sp, right), stateType),
            Comma, Sp, carry);
        Formula strictRefinement = Seq(oneKernel, Sp, Lt, Sp, zeroKernel);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, Typed(Seq(stateType, Comma, Sp, readoutType), type),
            Comma, RowBreak, Grp(),
            Typed(readout, Arrow(stateType, readoutType)), Comma, Sp,
            Typed(update, Arrow(stateType, stateType)), Comma,
            RowBreak, Grp(),
            Call("ListTFAE", conditions), Sp, Land,
            RowBreak, Grp(),
            Open, Open, carryExists, Close, Sp, Iff, Sp,
            strictRefinement, Close, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
