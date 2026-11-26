using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Analysis.RefinedBMV.Tracial;

internal sealed class ArithmeticProgressionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The continuum refined BMV comparison on four equally spaced log knots",
        H("The continuum refined BMV comparison on four equally spaced log knots"),
        Blocks(Describe.Lean(
            DescribeId.Create("refined-bmv-continuum-arithmetic-progression"),
            DeclarationHandle.Create(
                "D5/S3/Quantum/Analysis/RefinedBMV/Tracial/ArithmeticProgression.simplexGap_lt_matching"),
            H("Strict comparison at every positive spacing"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(
                LibraryNoteRef.Create("D5/L/HilbertOperators/hagele2026refinedbmv")),
            Blocks(Paragraph(Text(
                "The normalized exponential integral over four simplex weights gives the scalar " +
                "deficit at the knots 3t, t, −t, −3t. For every t > 0, its two matching roots " +
                "strictly dominate the central deficit. Confluent divided differences evaluate the " +
                "repeated-knot integrals. A finite differential recurrence with exact integer initial " +
                "values proves the discriminant sign on the entire positive half-line."))),
            DescribeRole.Theorem))));
}
