using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.ObservationOrder;

internal sealed class MutualNondisturbanceOrderIndependenceDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/ObservationOrder/"
            + "MutualNondisturbanceOrderIndependence."
            + "mutual_nondisturbance_order_independence";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Mutual readout nondisturbance removes observation-order effects.",
        H("Mutual Nondisturbance and Observation Order"),
        Blocks(Describe.Lean(
            DescribeId.Create("mutual-nondisturbance-order-independence"),
            DeclarationHandle.Create(Declaration),
            H("Mutual nondisturbance removes order effects"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The ordered joint readouts are the canonical forwardJoint and "
                        + "reverseJoint constructions from the ObservationOrder family.")),
                Paragraph(Text(
                    "Each update preserves the other instrument's readout. These two "
                        + "independent equations identify the two joint readout functions.")),
                Paragraph(Text(
                    "Under the additional commutation equation, the public second clause "
                        + "compares the complete paired result at every state: its first "
                        + "coordinate is the joint readout and its second is the final state."))),
            DescribeRole.Theorem))));

    private static Formula Apply(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);

    private static Formula Compose(Formula outer, Formula inner) =>
        Seq(outer, Sp, Circ, Sp, inner);

    private static Formula TheoremFormula()
    {
        Formula stateType = F.Id("X");
        Formula leftType = F.Id("C");
        Formula rightType = F.Id("D");
        Formula leftReadout = new Formula.Subscript(F.Id("o"), leftType);
        Formula rightReadout = new Formula.Subscript(F.Id("o"), rightType);
        Formula leftUpdate = new Formula.Subscript(F.Id("p"), leftType);
        Formula rightUpdate = new Formula.Subscript(F.Id("p"), rightType);
        Formula state = F.Id("x");
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula stateEndomap = new Formula.TypeArrow(stateType, stateType);
        Formula leftReadoutType = new Formula.TypeArrow(stateType, leftType);
        Formula rightReadoutType = new Formula.TypeArrow(stateType, rightType);
        Formula forward = Call(
            "forwardJoint", leftReadout, rightReadout, leftUpdate);
        Formula reverse = Call(
            "reverseJoint", leftReadout, rightReadout, rightUpdate);
        Formula forwardAt = Call(
            "forwardJoint", leftReadout, rightReadout, leftUpdate, state);
        Formula reverseAt = Call(
            "reverseJoint", leftReadout, rightReadout, rightUpdate, state);
        Formula finalForward = Apply(rightUpdate, Apply(leftUpdate, state));
        Formula finalReverse = Apply(leftUpdate, Apply(rightUpdate, state));
        Formula nondisturbance = Seq(
            Compose(rightReadout, leftUpdate), Sp, Eq, Sp, rightReadout,
            Sp, Land, Sp,
            Compose(leftReadout, rightUpdate), Sp, Eq, Sp, leftReadout);
        Formula updateCommutation = Seq(
            Compose(rightUpdate, leftUpdate), Sp, Eq, Sp,
            Compose(leftUpdate, rightUpdate));
        Formula completeExecutionEquality = Seq(
            Open, forwardAt, Comma, Sp, finalForward, Close,
            Sp, Eq, Sp,
            Open, reverseAt, Comma, Sp, finalReverse, Close);

        return Disp(new Formula.Aligned([
            Seq(
                Forall, Sp, stateType, Comma, Sp, leftType, Comma, Sp,
                rightType, Colon, Sp, type, Comma),
            Seq(
                leftReadout, Colon, Sp, leftReadoutType, Comma, Sp,
                rightReadout, Colon, Sp, rightReadoutType, Comma),
            Seq(
                leftUpdate, Comma, Sp, rightUpdate, Colon, Sp,
                stateEndomap, Comma),
            Seq(Open, nondisturbance, Close, Sp, Rightarrow),
            Seq(
                Open, forward, Sp, Eq, Sp, reverse, Close,
                Sp, Land, Sp),
            Seq(
                Open, Open, updateCommutation, Close, Sp, Rightarrow, Sp,
                Forall, Sp, state, Colon, Sp, stateType, Comma, Sp,
                completeExecutionEquality, Close, Dot),
        ]));
    }
}
