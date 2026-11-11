using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Dynamics.Symbolic;

internal sealed class KhetanThreePointRootDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S1/Dynamics/Symbolic/KhetanThreePointRoot.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Unit-circle rigidity for a three-term Fourier mask.",
        H("The three-point Fourier root obstruction"),
        Blocks(
            Paragraph(Text(
                "This is the algebraic bottleneck in the one-dimensional three-point tiling route "
                + "toward the six-cell Nivat boundary. Two unit-modulus phases whose sum with one is "
                + "zero must be cubic roots of unity; the result is conditional input for the later "
                + "Fourier/Newman rigidity argument.")),
            Describe.Lean(
                DescribeId.Create("unit-circle-three-term-root"),
                DeclarationHandle.Create(Owner + "unit_circle_three_term_root"),
                H("Unit-circle root rigidity"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For complex u and v of norm one, if 1 + u + v = 0 then both satisfy "
                    + "z^2 + z + 1 = 0."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("unit-circle-three-term-root-cubed"),
                DeclarationHandle.Create(Owner + "unit_circle_three_term_root_cubed"),
                H("Cubic phase consequence"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The same hypotheses imply u^3 = v^3 = 1, isolating the cubic character "
                    + "constraint used by the six-cell section argument."))),
                DescribeRole.Theorem)
        )));
}
