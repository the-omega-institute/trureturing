using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.DecisionValue;

internal sealed class CompleteInputDeterminismDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Deterministic disagreement exposes a difference in at least one complete input.",
        H("Complete Inputs Exclude Deterministic Disagreement"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("complete-inputs-exclude-deterministic-disagreement"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/DecisionValue/CompleteInputDeterminism."
                        + "complete_input_agreement_excludes_deterministic_disagreement"),
                H("Complete input agreement excludes deterministic disagreement"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Each decision input is constructed from the evidence concept and value, "
                            + "admission predicate, inference relation, value channel, action set, "
                            + "random seed, and actual anchor supplied by the source.")),
                    Paragraph(Text(
                        "The decisioner is a relation whose right uniqueness is a public premise. "
                            + "Thus determinism is not installed by defining the decisioner as a "
                            + "function or by defining its inputs through the conclusion.")),
                    Paragraph(Text(
                        "Right uniqueness proves agreement when all eight components coincide. "
                            + "The second public conjunct is its componentwise contrapositive: "
                            + "unequal related decisions identify at least one unequal input layer.")),
                    Paragraph(Text(
                        "The qualitative remark about ease of resolving disagreement has no "
                            + "source predicate and is not asserted as a universal theorem."))),
                DescribeRole.Theorem))));

    private static Formula Apply(Formula function, Formula first, Formula second) =>
        Seq(function, Open, first, Comma, Sp, second, Close);

    private static Formula Component(Formula component, Formula side) =>
        Seq(component, Underscore, Grp(side));

    private static Formula Input(Formula side) =>
        Seq(Open,
            Component(F.Id("C"), side), Comma, Sp,
            Component(F.Id("b"), side), Comma, Sp,
            Component(F.Id("A"), side), Comma, Sp,
            Component(Beta, side), Comma, Sp,
            Component(F.Id("V"), side), Comma, Sp,
            Component(F.Id("U"), side), Comma, Sp,
            Component(F.Id("s"), side), Comma, Sp,
            Component(F.Id("x"), side), Close);

    private static Formula SameComponents(Formula left, Formula right) =>
        Seq(
            Component(F.Id("C"), left), Sp, Eq, Sp, Component(F.Id("C"), right),
            Sp, Land, Sp,
            Component(F.Id("b"), left), Sp, Eq, Sp, Component(F.Id("b"), right),
            Sp, Land, Sp,
            Component(F.Id("A"), left), Sp, Eq, Sp, Component(F.Id("A"), right),
            Sp, Land, Sp,
            Component(Beta, left), Sp, Eq, Sp, Component(Beta, right),
            Sp, Land, Sp,
            Component(F.Id("V"), left), Sp, Eq, Sp, Component(F.Id("V"), right),
            Sp, Land, Sp,
            Component(F.Id("U"), left), Sp, Eq, Sp, Component(F.Id("U"), right),
            Sp, Land, Sp,
            Component(F.Id("s"), left), Sp, Eq, Sp, Component(F.Id("s"), right),
            Sp, Land, Sp,
            Component(F.Id("x"), left), Sp, Eq, Sp, Component(F.Id("x"), right));

    private static Formula DifferentComponents(Formula left, Formula right) =>
        Seq(
            Component(F.Id("C"), left), Sp, Neq, Sp, Component(F.Id("C"), right),
            Sp, Lor, Sp,
            Component(F.Id("b"), left), Sp, Neq, Sp, Component(F.Id("b"), right),
            Sp, Lor, Sp,
            Component(F.Id("A"), left), Sp, Neq, Sp, Component(F.Id("A"), right),
            Sp, Lor, Sp,
            Component(Beta, left), Sp, Neq, Sp, Component(Beta, right),
            Sp, Lor, Sp,
            Component(F.Id("V"), left), Sp, Neq, Sp, Component(F.Id("V"), right),
            Sp, Lor, Sp,
            Component(F.Id("U"), left), Sp, Neq, Sp, Component(F.Id("U"), right),
            Sp, Lor, Sp,
            Component(F.Id("s"), left), Sp, Neq, Sp, Component(F.Id("s"), right),
            Sp, Lor, Sp,
            Component(F.Id("x"), left), Sp, Neq, Sp, Component(F.Id("x"), right));

    private static Formula TheoremFormula()
    {
        Formula relation = F.Id("D");
        Formula left = F.Id("l");
        Formula right = F.Id("r");
        Formula arbitraryInput = F.Id("I");
        Formula firstOutput = F.Id("u");
        Formula secondOutput = F.Id("v");
        Formula leftOutput = Component(F.Id("u"), left);
        Formula rightOutput = Component(F.Id("u"), right);

        Formula rightUnique = Seq(
            Forall, Sp, arbitraryInput, Comma, Sp, firstOutput, Comma, Sp,
            secondOutput, Comma, Sp,
            Open, Apply(relation, arbitraryInput, firstOutput), Sp, Land, Sp,
            Apply(relation, arbitraryInput, secondOutput), Close, Sp,
            Rightarrow, Sp, firstOutput, Sp, Eq, Sp, secondOutput);

        return Disp(Seq(
            Component(arbitraryInput, left), Sp, Eq, Sp, Input(left), Comma,
            RowBreak, Grp(),
            Component(arbitraryInput, right), Sp, Eq, Sp, Input(right), Comma,
            RowBreak, Grp(),
            rightUnique, Comma, RowBreak, Grp(),
            Apply(relation, Component(arbitraryInput, left), leftOutput), Sp,
            Land, Sp,
            Apply(relation, Component(arbitraryInput, right), rightOutput),
            RowBreak, Grp(),
            Rightarrow, Sp, OpenBracket,
            Open, Open, SameComponents(left, right), Close, Sp,
            Rightarrow, Sp, leftOutput, Sp, Eq, Sp, rightOutput, Close,
            RowBreak, Grp(),
            Land, Sp,
            Open, leftOutput, Sp, Neq, Sp, rightOutput, Sp,
            Rightarrow, Sp, DifferentComponents(left, right), Close,
            CloseBracket, Dot));
    }
}
