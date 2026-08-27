using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Fibers;

internal sealed class ObserverConceptReadoutCorrespondenceDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/Fibers/ObserverConceptReadoutCorrespondence."
            + "observer_concept_readout_correspondence";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Concepts embed as singleton observers and observer identity descends to a quotient.",
        H("Observer and Concept Readout Correspondence"),
        Blocks(Describe.Lean(
            DescribeId.Create("observer-concept-readout-correspondence"),
            DeclarationHandle.Create(Declaration),
            H("Embedding, forgetting, and relative identity"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The singleton observer is public through its computation rules: its sole "
                        + "readout is the supplied concept, its admission predicate is universally "
                        + "true, and its anchor is the supplied state.")),
                Paragraph(Text(
                    "For an arbitrary dependent readout family, forgetting forms the canonical "
                        + "quotient projection by the kernel of the joint readout. Equality in that "
                        + "quotient is exactly observer-relative identity.")),
                Paragraph(Text(
                    "Three explicit Boolean countermodels show that equal readout kernels do not "
                        + "retain admission, anchor, or the coordinate decomposition of the joint "
                        + "readout."))),
            DescribeRole.Theorem))));

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula Typed(Formula value, Formula type) =>
        Seq(value, Colon, Sp, type);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Iff, right);

    private static Formula TheoremFormula()
    {
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula state = F.Id("X");
        Formula conceptValue = F.Id("C");
        Formula index = F.Id("I");
        Formula value = F.Id("B");
        Formula concept = F.Id("q");
        Formula anchor = F.Id("a");
        Formula observer = F.Id("O");
        Formula embedded = F.Id("E");
        Formula joint = F.Id("J");
        Formula projection = F.Id("p");
        Formula left = F.Id("x");
        Formula right = F.Id("y");
        Formula observerType = Call("ObserverStructure", state, index, value);
        Formula embeddedReadout = Call("readout", embedded);
        Formula observerReadout = Call("readout", observer);
        Formula observerJoint = Call("jointReadout", observerReadout);
        Formula embeddedRules = And(
            Equal(Apply(embeddedReadout, F.Id("unit")), concept),
            And(
                Equal(Call("admissible", embedded),
                    Grp(Lambda, Sp, F.Id("k"), Comma, Sp, F.Id("True"))),
                Equal(Call("anchor", embedded), anchor)));
        Formula embeddedIdentity = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                new Formula.BoundVariable(FormulaIdentifier.Create("x"), state),
                new Formula.BoundVariable(FormulaIdentifier.Create("y"), state),
            ],
            Iff(
                Equal(Apply(Call("jointReadout", embeddedReadout), left),
                    Apply(Call("jointReadout", embeddedReadout), right)),
                Equal(Apply(concept, left), Apply(concept, right))));
        Formula forgottenIdentity = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                new Formula.BoundVariable(FormulaIdentifier.Create("x"), state),
                new Formula.BoundVariable(FormulaIdentifier.Create("y"), state),
            ],
            Iff(
                Equal(Apply(projection, left), Apply(projection, right)),
                Equal(Apply(observerJoint, left), Apply(observerJoint, right))));
        Formula firstObserver = F.Id("O1");
        Formula secondObserver = F.Id("O2");
        Formula boolObserverType = Call(
            "ObserverStructure",
            F.Id("Bool"),
            F.Id("Unit"),
            Grp(Lambda, Sp, F.Id("k"), Comma, Sp, F.Id("Bool")));
        Formula unitObserverType = Call(
            "ObserverStructure",
            F.Id("Bool"),
            F.Id("Unit"),
            Grp(Lambda, Sp, F.Id("k"), Comma, Sp, F.Id("Unit")));
        Formula firstKernel = Call(
            "ker",
            Call("jointReadout", Call("readout", firstObserver)));
        Formula secondKernel = Call(
            "ker",
            Call("jointReadout", Call("readout", secondObserver)));
        Formula admissionLoss = Seq(
            Exists, Sp,
            Typed(
                Seq(firstObserver, Comma, Sp, secondObserver),
                boolObserverType),
            Comma, Sp,
            NotEqual(
                Call("admissible", firstObserver),
                Call("admissible", secondObserver)),
            Sp, Land, Sp,
            Equal(firstKernel, secondKernel));
        Formula anchorLoss = Seq(
            Exists, Sp,
            Typed(
                Seq(firstObserver, Comma, Sp, secondObserver),
                unitObserverType),
            Comma, Sp,
            NotEqual(
                Call("anchor", firstObserver),
                Call("anchor", secondObserver)),
            Sp, Land, Sp,
            Equal(firstKernel, secondKernel));
        Formula firstFamilyKernel = Call(
            "ker", Call("jointReadout", F.Id("r")));
        Formula secondFamilyKernel = Call(
            "ker", Call("jointReadout", F.Id("s")));
        Formula decompositionLoss = Seq(
            Exists, Sp,
            Typed(
                Seq(F.Id("r"), Comma, Sp, F.Id("s")),
                Arrow(F.Id("Bool"), Arrow(F.Id("Bool"), F.Id("Bool")))),
            Comma, Sp,
            NotEqual(F.Id("r"), F.Id("s")), Sp, Land, Sp,
            Equal(firstFamilyKernel, secondFamilyKernel));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp,
            Typed(
                Seq(state, Comma, Sp, conceptValue, Comma, Sp, index),
                type),
            Comma, RowBreak, Grp(),
            Typed(value, Arrow(index, type)), Comma, Sp,
            Typed(concept, Arrow(state, conceptValue)), Comma, Sp,
            Typed(anchor, state), Comma, RowBreak, Grp(),
            Typed(observer, observerType), Comma, RowBreak, Grp(),
            embedded, Sp, Colon, Eq, Sp,
            Call("conceptObserver", concept, anchor), Comma, RowBreak, Grp(),
            joint, Sp, Colon, Eq, Sp, observerJoint, Comma, Sp,
            projection, Sp, Colon, Eq, Sp,
            Call("quotientClassMap", joint), Comma, RowBreak, Grp(),
            OpenBracket,
            Open, embeddedRules, Close, Sp, Land, RowBreak, Grp(),
            Open, embeddedIdentity, Close, Sp, Land, RowBreak, Grp(),
            Open, forgottenIdentity, Close, Sp, Land, RowBreak, Grp(),
            Open, admissionLoss, Close, Sp, Land, RowBreak, Grp(),
            Open, anchorLoss, Close, Sp, Land, RowBreak, Grp(),
            Open, decompositionLoss, Close,
            CloseBracket, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
