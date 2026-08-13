using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Eigenstructure;

internal sealed class GoldenPowerCoordinatesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The second and third golden powers have unique nonnegative coordinates.",
        H("Unique Golden-Power Coordinates"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("golden-power-coordinates-are-unique"),
                DeclarationHandle.Create(
                    "D5/S1/Eigenstructure/GoldenPowerCoordinates.golden_power_coordinates_unique"),
                H("The second and third golden powers have unique coordinates"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("a"), Comma, F.Id("b"), Comma,
                    F.Id("c"), Comma, F.Id("d"), Sp, InMacro, Sp,
                    Mathbb, Grp(F.Id("N")), Comma, Esc,
                    F.Id("a"), Sp, Varphi, Caret, Grp(D(2)), Sp, Plus, Sp,
                    F.Id("b"), Sp, Varphi, Caret, Grp(D(3)), Sp, Eq, Sp,
                    F.Id("c"), Sp, Varphi, Caret, Grp(D(2)), Sp, Plus, Sp,
                    F.Id("d"), Sp, Varphi, Caret, Grp(D(3)), Sp,
                    Rightarrow, Sp, F.Id("a"), Eq, F.Id("c"), Sp, Land, Sp,
                    F.Id("b"), Eq, F.Id("d"), Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Equality of the two real power combinations is transported to the "
                        + "repository's injective real embedding of integral golden coordinates. "
                        + "The two carrier coordinates then determine both natural coefficients.")),
                    Paragraph(Text(
                        "The proof is a thin corollary of the existing embedding injectivity theorem, "
                        + "whose kernel argument uses Mathlib's irrationality of the golden ratio.")),
                    Paragraph(Text(
                        "This is an honest partial closure of only the leading uniqueness clause in "
                        + "source theorem 6.38. The bivariate power series, factorization, inversion, "
                        + "coefficient table, truncation audit, and all claims through total degree "
                        + "sixteen remain unresolved."))),
                DescribeRole.Theorem))));
}
