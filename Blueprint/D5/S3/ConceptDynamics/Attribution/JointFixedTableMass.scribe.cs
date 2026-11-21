using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Attribution;

internal sealed class JointFixedTableMassDocument : IScribeDocumentDefinition
{
    private const string Result =
        "D5/S3/ConceptDynamics/Attribution/JointFixedTableMass.two_table_masses_attain_row_minima_iff";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "One scalar inequality characterizes simultaneous attainment of two fixed-table masses.",
        H("Two invariant output events"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("two-table-masses-attain-row-minima"),
                DeclarationHandle.Create(Result),
                H("When one table law attains both row bounds"),
                StatementSource.FromAuthor(Statement()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Let a monoid act on a finite output set Y. Let a finite "
                        + "set X index normalized nonnegative output laws invariant under the action. "
                        + "Each output carries two Boolean flags, both invariant under the action. "
                        + "The action on tables X to Y acts on each output coordinate.")),
                    Paragraph(Text("Let a and b be the least row masses of the first and second "
                        + "flags. Let i and u be the least row masses of the intersection and "
                        + "the union. Each minimum is attained by a row, and the minimizing rows may "
                        + "differ. Let F assert the existence of a normalized, nonnegative and invariant table law. "
                        + "It has the specified row marginals. Its mass of tables with the first "
                        + "flag true at every input is a, and the analogous second mass is b.")),
                    Paragraph(Text("The inequality follows by adding the masses of the union and "
                        + "intersection of the two all-input table events and bounding each by "
                        + "its corresponding least row mass. Conversely, take a common law of "
                        + "two flags with coordinate masses a and b and intersection mass "
                        + "max(0, a + b minus u). The four nontrivial upper sets of the Boolean "
                        + "square give the inequalities for ordered coupling to each row. "
                        + "Use the finite ordered coupling theorem, lift each coupling to the row "
                        + "outputs, and take the conditionally independent product across rows. "
                        + "The minimizing row for each flag makes the corresponding lower "
                        + "bound exact."))),
                DescribeRole.Theorem))));

    private static Formula Statement() =>
        Disp(Seq(F.Id("F"), Sp, Iff, Sp,
            F.Id("a"), Sp, Plus, Sp, F.Id("b"), Sp, Leq, Sp,
            F.Id("i"), Sp, Plus, Sp, F.Id("u")));
}
