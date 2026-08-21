using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.ObservationOrder;

internal sealed class PureReadoutOrderIndependenceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Identity observation updates exclude order effects from two static readouts.",
        H("Pure Readouts and Observation Order"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("pure-readout-order-independence"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/ObservationOrder/PureReadoutOrderIndependence."
                        + "pure_readout_order_independence"),
                H("Pure readouts have no order effect"),
                StatementSource.FromAuthor(IndependenceFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The forward joint readout observes C, applies its state update, and then "
                            + "observes D. The reverse joint readout observes D first and returns "
                            + "the coordinates in the same C,D order.")),
                    Paragraph(Text(
                        "An order effect is witnessed by a state where those two paired results "
                            + "differ. Identity updates reduce both constructions to the canonical "
                            + "join of the two static concept readouts.")),
                    Paragraph(Text(
                        "The public application domain contains quantum measurement, survey order, "
                            + "judicial inquiry, medical diagnosis, psychological priming, and "
                            + "institutional classification. Any reported effect witnessed by the "
                            + "source joint readouts forces at least one nonidentity update."))),
                DescribeRole.Theorem))));

    private static Formula Apply(Formula function, params Formula[] arguments)
    {
        var items = new List<Formula> { function, Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula Arrow(Formula domain, Formula codomain) =>
        Seq(domain, Sp, To, Sp, codomain);

    private static Formula IndependenceFormula()
    {
        Formula stateType = F.Id("X");
        Formula leftType = F.Id("C");
        Formula rightType = F.Id("D");
        Formula leftReadout = new Formula.Subscript(F.Id("o"), leftType);
        Formula rightReadout = new Formula.Subscript(F.Id("o"), rightType);
        Formula leftUpdate = new Formula.Subscript(F.Id("p"), leftType);
        Formula rightUpdate = new Formula.Subscript(F.Id("p"), rightType);
        Formula application = F.Id("a");
        Formula reported = F.Id("E");
        Formula forward = Apply(
            Seq(Operatorname, Grp(F.Id("forwardJoint"))),
            leftReadout, rightReadout, leftUpdate);
        Formula reverse = Apply(
            Seq(Operatorname, Grp(F.Id("reverseJoint"))),
            leftReadout, rightReadout, rightUpdate);
        Formula effect = Apply(
            Seq(Operatorname, Grp(F.Id("hasOrderEffect"))), forward, reverse);
        Formula identityPremise = Seq(
            leftUpdate, Sp, Eq, Sp, F.Id("id"), Sp, Land, Sp,
            rightUpdate, Sp, Eq, Sp, F.Id("id"));
        Formula noPureEffect = Seq(
            Open, identityPremise, Close, Sp, Rightarrow, Sp, Neg, Sp, effect);
        Formula updateNecessary = Seq(
            Forall, Sp, application, Colon, Sp, F.Id("ApplicationDomain"), Comma, Sp,
            Apply(reported, application), Sp, Rightarrow, Sp,
            leftUpdate, Sp, Neq, Sp, F.Id("id"), Sp, Lor, Sp,
            rightUpdate, Sp, Neq, Sp, F.Id("id"));
        Formula observationBridge = Seq(
            Forall, Sp, application, Colon, Sp, F.Id("ApplicationDomain"), Comma, Sp,
            Apply(reported, application), Sp, Rightarrow, Sp, effect);
        Formula types = Seq(
            stateType, Comma, Sp, leftType, Comma, Sp, rightType, Colon, Sp,
            Operatorname, Grp(F.Id("Type")));
        Formula stateEndomap = Arrow(stateType, stateType);

        return Disp(Seq(
            Forall, Sp, types, Comma, Sp,
            leftReadout, Colon, Sp, Arrow(stateType, leftType), Comma, Sp,
            rightReadout, Colon, Sp, Arrow(stateType, rightType), Comma, Sp,
            leftUpdate, Comma, Sp, rightUpdate, Colon, Sp, stateEndomap, Comma, Sp,
            reported, Colon, Sp,
            Arrow(F.Id("ApplicationDomain"),
                Seq(Operatorname, Grp(F.Id("Prop")))),
            Comma, Sp, Open, observationBridge, Close, Sp, Rightarrow, Esc,
            Open, noPureEffect, Close, Sp, Land, Esc,
            Open, updateNecessary, Close, Dot));
    }
}
