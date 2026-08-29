using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.SensorFamilies;

internal sealed class SensorFamilyExtensionStrictRefinementDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ConceptDynamics/SensorFamilies/SensorFamilyExtensionStrictRefinement.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Adding a separating sensor strictly refines a sensor-family kernel.",
        H("Sensor Family Extension Strict Refinement"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("the-extended-family-refines-the-original-family"),
                DeclarationHandle.Create(Prefix + "extension_kernel_refines_original"),
                H("The extended family refines the original family"),
                StatementSource.FromAuthor(RefinementStatement()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Assume x and y agree under every coordinate of the family extended by "
                            + "one extra sensor.")),
                    Paragraph(Text(
                        "Evaluating that agreement at each original-coordinate injection proves "
                            + "that x and y agree under the original family."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("a-separating-extra-sensor-witnesses-strict-refinement"),
                DeclarationHandle.Create(
                    Prefix + "separating_extension_witnesses_strict_refinement"),
                H("A separating extra sensor witnesses strict refinement"),
                StatementSource.FromAuthor(StrictStatement()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Now assume x and y agree under every old sensor but receive distinct "
                            + "values from the extra sensor.")),
                    Paragraph(Text(
                        "The pair remains in the old family kernel and is excluded from the "
                            + "extended family kernel, giving the stated witness-level split."))),
                DescribeRole.Theorem))));

    private static Formula Arrow(Formula source, Formula target) =>
        new Formula.TypeArrow(source, target);

    private static Formula PrefixFormula(Formula antecedent, Formula conclusion) =>
        Disp(Seq(
            Forall, Sp, F.Id("sensor"), Colon, Sp,
            Arrow(F.Id("I"), Arrow(F.Id("X"), F.Id("O"))), Comma, Sp,
            F.Id("extra"), Colon, Sp, Arrow(F.Id("X"), F.Id("O")), Comma, Sp,
            F.Id("x"), Comma, Sp, F.Id("y"), Colon, Sp, F.Id("X"), Comma,
            RowBreak, Grp(),
            antecedent, Sp, Rightarrow, Sp, conclusion, Dot));

    private static Formula RefinementStatement()
    {
        Formula extended = Call("FamilyKernel",
            Call("extendedSensor", F.Id("sensor"), F.Id("extra")),
            F.Id("x"), F.Id("y"));
        Formula original = Call("FamilyKernel", F.Id("sensor"), F.Id("x"), F.Id("y"));
        return PrefixFormula(extended, original);
    }

    private static Formula StrictStatement()
    {
        Formula original = Call("FamilyKernel", F.Id("sensor"), F.Id("x"), F.Id("y"));
        Formula extended = Call("FamilyKernel",
            Call("extendedSensor", F.Id("sensor"), F.Id("extra")),
            F.Id("x"), F.Id("y"));
        Formula separates = Seq(
            Call("extra", F.Id("x")), Sp, Neq, Sp, Call("extra", F.Id("y")));
        Formula antecedent = Seq(Open, original, Sp, Land, Sp, separates, Close);
        Formula consequence = Seq(Open, original, Sp, Land, Sp, Neg, extended, Close);
        return PrefixFormula(antecedent, consequence);
    }
}
