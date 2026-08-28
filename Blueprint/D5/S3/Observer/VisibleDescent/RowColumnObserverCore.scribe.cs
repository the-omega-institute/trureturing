using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.VisibleDescent;

internal sealed class RowColumnObserverCoreDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Observer/VisibleDescent/RowColumnObserverCore."
            + "row_column_observer_core";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Quotienting equal evaluation rows and columns produces a canonical observer "
            + "core that separates both state and protocol classes.",
        H("Biextensional Observer Core"),
        Blocks(Describe.Lean(
            DescribeId.Create("biextensional-observer-core"),
            DeclarationHandle.Create(Declaration),
            H("The double quotient evaluation separates both carriers"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The state relation is the kernel of the curried evaluation, while the "
                        + "protocol relation is the kernel after swapping its two inputs. Thus "
                        + "the two quotients identify exactly duplicate rows and columns.")),
                Paragraph(Text(
                    "The displayed descended evaluation is Mathlib's canonical two-quotient "
                        + "lift. The representative-invariance clause supplies its defining "
                        + "compatibility and the lift retains the original evaluation on "
                        + "representative classes by construction.")),
                Paragraph(Text(
                    "If two state classes were not separated by any protocol class, their "
                        + "representative rows would agree and the classes would be equal. The "
                        + "same argument with the inputs exchanged separates distinct protocol "
                        + "classes. No finiteness or inhabitation assumption is required."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula stateType = F.Id("X");
        Formula protocolType = F.Id("P");
        Formula valueType = F.Id("Lambda");
        Formula evaluate = F.Id("e");
        Formula stateRelation = F.Id("rhoX");
        Formula protocolRelation = F.Id("rhoP");
        Formula descended = F.Id("eBar");
        Formula firstState = F.Id("x");
        Formula secondState = F.Id("y");
        Formula firstProtocol = F.Id("pi");
        Formula secondProtocol = F.Id("sigma");
        Formula firstClass = F.Id("u");
        Formula secondClass = F.Id("v");
        Formula protocolClass = F.Id("pBar");
        Formula stateClass = F.Id("xBar");
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula stateQuotient = Call("Quotient", stateRelation);
        Formula protocolQuotient = Call("Quotient", protocolRelation);

        Formula representativeInvariance = Seq(
            Forall, Sp,
            Typed(firstState, stateType), Comma, Sp,
            Typed(secondState, stateType), Comma, Sp,
            Typed(firstProtocol, protocolType), Comma, Sp,
            Typed(secondProtocol, protocolType), Comma, Sp,
            Apply(stateRelation, firstState, secondState), Sp, Rightarrow, Sp,
            Apply(protocolRelation, firstProtocol, secondProtocol), Sp, Rightarrow, Sp,
            Apply(evaluate, firstState, firstProtocol), Sp, Eq, Sp,
            Apply(evaluate, secondState, secondProtocol));
        Formula stateSeparation = Seq(
            Forall, Sp,
            Typed(firstClass, stateQuotient), Comma, Sp,
            Typed(secondClass, stateQuotient), Comma, Sp,
            firstClass, Sp, Neq, Sp, secondClass, Sp, Rightarrow, Sp,
            Exists, Sp, Typed(protocolClass, protocolQuotient), Comma, Sp,
            Apply(descended, firstClass, protocolClass), Sp, Neq, Sp,
            Apply(descended, secondClass, protocolClass));
        Formula protocolSeparation = Seq(
            Forall, Sp,
            Typed(firstClass, protocolQuotient), Comma, Sp,
            Typed(secondClass, protocolQuotient), Comma, Sp,
            firstClass, Sp, Neq, Sp, secondClass, Sp, Rightarrow, Sp,
            Exists, Sp, Typed(stateClass, stateQuotient), Comma, Sp,
            Apply(descended, stateClass, firstClass), Sp, Neq, Sp,
            Apply(descended, stateClass, secondClass));

        return Disp(new Formula.Aligned([
            Seq(
                Forall, Sp,
                Typed(Seq(stateType, Comma, Sp, protocolType, Comma, Sp, valueType),
                    type), Comma),
            Seq(
                Typed(evaluate,
                    Arrow(stateType, Arrow(protocolType, valueType))), Comma),
            Seq(
                Operatorname, Grp(F.Id("let")), Sp,
                stateRelation, Sp, Colon, Eq, Sp, Call("ker", evaluate), Comma),
            Seq(
                protocolRelation, Sp, Colon, Eq, Sp,
                Call("ker", Call("swap", evaluate)), Comma),
            Seq(
                descended, Sp, Colon, Eq, Sp,
                Call("QuotientLift2", evaluate, stateRelation, protocolRelation), Sp,
                Operatorname, Grp(F.Id("in"))),
            Seq(Open, representativeInvariance, Close, Sp, Land),
            Seq(Open, stateSeparation, Close, Sp, Land),
            Seq(Open, protocolSeparation, Close, Dot),
        ]));
    }

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula Typed(Formula value, Formula type) =>
        Seq(value, Colon, Sp, type);

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula Call(string name, params Formula[] arguments) =>
        Apply(Seq(Operatorname, Grp(F.Id(name))), arguments);
}
