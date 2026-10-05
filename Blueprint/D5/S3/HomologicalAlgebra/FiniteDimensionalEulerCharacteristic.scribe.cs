using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.HomologicalAlgebra;

internal sealed class FiniteDimensionalEulerCharacteristicDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/HomologicalAlgebra/FiniteDimensionalEulerCharacteristic.";

    private static readonly LibraryNoteRef WeibelSource =
        LibraryNoteRef.Create("D5/L/HomologicalAlgebra/weibel1994homologicalalgebra");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finite-dimensional three-term chain complex satisfies an explicit Euler characteristic identity.",
        H("Euler Characteristic of a Three-Term Finite-Dimensional Complex"),
        Blocks(Describe.Lean(
            DescribeId.Create("finite-dimensional-three-term-euler"),
            DeclarationHandle.Create(Prefix + "finrank_three_term_euler"),
            H("Three-term Euler identity"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(WeibelSource),
            Blocks(
                Paragraph(Text(
                    "Let f : U to V and g : V to W be maps of finite-dimensional "
                        + "vector spaces over a field with g composed with f equal to zero. "
                        + "The map f is codomain-restricted to ker(g), so its range is a "
                        + "submodule of ker(g). The dimensions of U and W together with "
                        + "the middle quotient ker(g) / range(f) equal the dimension of V "
                        + "together with the endpoint quotient W / range(g) and ker(f).")),
                Paragraph(Text(
                    "The proof is a rank-nullity calculation for f, g, and the "
                        + "codomain-restricted map, followed by the quotient rank formula. "
                        + "It is stated as an additive equality in natural dimensions, "
                        + "so no subtraction convention is needed.")),
                Paragraph(Text(
                    "Weibel's Chapter 1 supplies the standard finite-dimensional "
                        + "Euler-characteristic context. The explicit Lean quotient "
                        + "types and the machine-checked equality are repository-derived; "
                        + "no splitting or infinite-dimensional statement is asserted."))),
            DescribeRole.Theorem))));
}
