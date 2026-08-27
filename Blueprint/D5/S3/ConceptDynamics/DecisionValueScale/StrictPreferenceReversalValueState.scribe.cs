using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.DecisionValueScale;

internal sealed class StrictPreferenceReversalValueStateDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/DecisionValueScale/StrictPreferenceReversalValueState."
            + "strict_preference_reversal_changes_value_state";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Opposite strict rankings on one option carrier require distinct temporal value states.",
        H("Strict Preference Reversal Separates Value States"),
        Blocks(Describe.Lean(
            DescribeId.Create("strict-preference-reversal-changes-value-state"),
            DeclarationHandle.Create(Declaration),
            H("A strict reversal excludes one time-invariant scalar value"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Both moments use the same option carrier and the same two options. "
                        + "Each moment has a real-valued function that faithfully represents "
                        + "its observed strict ranking.")),
                Paragraph(Text(
                    "The first function ranks a above b, while the second ranks b above a. "
                        + "If the functions were equal, asymmetry of the real strict order "
                        + "would give an immediate contradiction.")),
                Paragraph(Text(
                    "Their public inequality is exactly the value-state change forced by the "
                        + "source assumptions, and rules out a single time-invariant scalar "
                        + "representation of both moments."))),
            DescribeRole.Theorem))));

    private static Formula Apply(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula TheoremFormula()
    {
        Formula choice = F.Id("U");
        Formula firstOption = F.Id("a");
        Formula secondOption = F.Id("b");
        Formula valueAtFirst = new Formula.Subscript(F.Id("V"), D(0));
        Formula valueAtSecond = new Formula.Subscript(F.Id("V"), D(1));
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula valueType = Arrow(choice, real);
        Formula reversal = Seq(
            Apply(valueAtFirst, firstOption), Sp, Gt, Sp,
            Apply(valueAtFirst, secondOption), Sp, Land, Sp,
            Apply(valueAtSecond, secondOption), Sp, Gt, Sp,
            Apply(valueAtSecond, firstOption));

        return Disp(Seq(
            Forall, Sp, choice, Colon, Sp, type, Comma, Sp,
            firstOption, Comma, Sp, secondOption, Colon, Sp, choice, Comma, Sp,
            valueAtFirst, Comma, Sp, valueAtSecond, Colon, Sp, valueType, Comma, Sp,
            Open, reversal, Close, Sp, Rightarrow, Sp,
            valueAtFirst, Sp, Neq, Sp, valueAtSecond, Dot));
    }
}
