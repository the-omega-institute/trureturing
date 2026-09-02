using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Dialectics;

internal sealed class ConstantObserverClosureContrastDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A constant observer can be dynamically closed while losing state and target distinctions.",
        H("Constant Observer Closure Contrast"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("constant-observer-closure-can-be-coarse"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/Dialectics/ConstantObserverClosureContrast."
                        + "constant_observer_closure_can_be_coarse"),
                H("Constant closure can be coarse"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The state carrier is arbitrary but nontrivial, and the dynamics is an "
                            + "arbitrary self-map. The observer is the actual constant map into "
                            + "the one-point type.")),
                    Paragraph(Text(
                        "The first two public clauses apply the frozen deterministic-interface "
                            + "equivalence to give effective descent and absence of every carry "
                            + "witness for the same observer and dynamics.")),
                    Paragraph(Text(
                        "The remaining public clauses report the other dimensions separately: "
                            + "the observer is noninjective, and every target that distinguishes "
                            + "a state pair is not sufficient through this observer."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/ConceptDynamics/Dialectics/DeterministicInterfaceEquivalence")),
        ]));

    private static Formula Call(string name, params Formula[] arguments) =>
        DefinitionDsl.Call(name, arguments);

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula Apply(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);

    private static Formula Typed(Formula value, Formula type) =>
        Seq(value, Colon, Sp, type);

    private static Formula Lambda(Formula binder, Formula body) =>
        Seq(Open, binder, Sp, Mapsto, Sp, body, Close);

    private static Formula TheoremFormula()
    {
        Formula stateType = F.Id("X");
        Formula targetType = F.Id("Target");
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula unitValue = Seq(Open, Close);
        Formula dynamics = F.Id("F");
        Formula target = F.Id("T");
        Formula left = F.Id("x");
        Formula right = F.Id("y");
        Formula observer = Lambda(left, unitValue);

        Formula closure = Call("EffectiveDescent", observer, dynamics);
        Formula carry = Call("IsCarryWitness", observer, dynamics, observer, left, right);
        Formula noCarry = Seq(
            Forall, Sp, Typed(Seq(left, Comma, Sp, right), stateType), Comma, Sp,
            Neg, Sp, carry);
        Formula notInjective = Seq(Neg, Sp, Call("Injective", observer));
        Formula targetSeparated = Seq(
            Exists, Sp, Typed(Seq(left, Comma, Sp, right), stateType), Comma, Sp,
            Apply(target, left), Sp, Neq, Sp, Apply(target, right));
        Formula targetInsufficient = Seq(
            Forall, Sp, Typed(targetType, type), Comma, Sp,
            Typed(target, Arrow(stateType, targetType)), Comma, Sp,
            Open, targetSeparated, Close, Sp, Rightarrow, Sp,
            Neg, Sp, Call("FactorsThrough", target, observer));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, Typed(stateType, type), Comma, Sp,
            OpenBracket, Call("Nontrivial", stateType), CloseBracket, Sp, Rightarrow,
            RowBreak, Grp(),
            Forall, Sp, Typed(dynamics, Arrow(stateType, stateType)), Comma,
            RowBreak, Grp(),
            closure, Sp, Land,
            RowBreak, Grp(),
            Open, noCarry, Close, Sp, Land,
            RowBreak, Grp(),
            notInjective, Sp, Land,
            RowBreak, Grp(),
            Open, targetInsufficient, Close, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
