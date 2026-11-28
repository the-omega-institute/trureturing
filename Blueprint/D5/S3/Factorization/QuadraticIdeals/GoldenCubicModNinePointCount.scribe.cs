using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Factorization.QuadraticIdeals;

internal sealed class GoldenCubicModNinePointCountDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Factorization/QuadraticIdeals/GoldenCubicModNinePointCount.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Kernel-checked Euler character counts for the native cubic at primes 109 and 379.",
        H("Euler's criterion computes the exact number of affine solutions"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("wss-mod9-count-eq-fast"),
                DeclarationHandle.Create(Module + "count_eq_fast"),
                H("Euler's criterion computes the exact number of affine solutions"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The point count splits by the x-coordinate and the quadratic-character square-root formula gives each fiber size."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("wss-mod9-count109a"),
                DeclarationHandle.Create(Module + "count109a"),
                H("The 43-state at prime 109 has 105 points"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Closed interval-free finite sum, checked in small exact Euler blocks."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("wss-mod9-count109b"),
                DeclarationHandle.Create(Module + "count109b"),
                H("The 66-state at prime 109 has 105 points"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The two cycling native phases have the same count."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("wss-mod9-count379a"),
                DeclarationHandle.Create(Module + "count379a"),
                H("The 4-state at prime 379 has 376 points"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The exact affine enumeration includes the point at infinity."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("wss-mod9-count379b"),
                DeclarationHandle.Create(Module + "count379b"),
                H("The 76-state at prime 379 has 384 points"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The exact Euler sum supplies the second transient witness."))),
                DescribeRole.Theorem))));
}
