using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Axis;

internal sealed class AxisOrbitMapDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The two trace recurrences are exactly one orbit of a four-dimensional polynomial map.",
        H("Axis Orbit Map"),
        Blocks(
            Paragraph(Text(
                "The weight recurrence and the partial-sum recurrence were proved separately. "
                    + "Read together they are not two laws but one: the state holding the two "
                    + "latest partial sums and the two latest weights advances by a single "
                    + "polynomial map, and each recurrence supplies one of its coordinates "
                    + "while the remaining two are shifts.")),
            Paragraph(Text(
                "Stating this is what rules out a third law hiding in the pair. Without the "
                    + "orbit form the two recurrences merely coexist; with it, every depth is "
                    + "an iterate of one map from one base state.")),
            Describe.Lean(
                DescribeId.Create("trace-recurrences-are-one-orbit"),
                DeclarationHandle.Create(
                    "D5/S3/Axis/AxisOrbitMap.trace_recurrences_are_one_orbit"),
                H("The trace recurrences are one orbit"),
                StatementSource.FromAuthor(OrbitFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The displayed conjunct is the single step; the package also carries that "
                        + "the state at every depth is the corresponding iterate."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Axis/AxisPartialSum")),
        ]));

    private static Formula State(Formula index) =>
        Seq(F.Id("S"), Underscore, Grp(index));

    private static Formula OrbitFormula()
    {
        Formula k = F.Id("K");
        return Disp(Seq(
            Forall, Sp, k, InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, Esc,
            F.Id("F"), Open, State(k), Close, Sp, Eq, Sp,
            State(Seq(k, Plus, D(1))), Dot));
    }
}
