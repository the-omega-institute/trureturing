using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaBridge;

internal sealed class FiniteReflectionCompatibleWeilInterpolationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every finite reflection-compatible assignment on actual zero indices is realized by a smooth compact even Weil test.",
        H("Finite Reflection-Compatible Weil Interpolation"),
        Blocks(Describe.Lean(
            DescribeId.Create("finite-reflection-compatible-weil-interpolation"),
            DeclarationHandle.Create("D5/S3/Weil/ZetaBridge/FiniteReflectionCompatibleWeilInterpolation.even_weil_interpolation_on_finite_indices"),
            H("Compatible finite data has an actual interpolant"),
            StatementSource.FromAuthor(Disp(F.Id("a(reflection j)=a(j) implies exists g with FT(g)(gamma j)=a(j) on E"))),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("The proof descends the data through the existing reflection representative, applies the frozen sign-separated even interpolation theorem, and transports the values back to every selected index. It works for arbitrary finite E and imposes no artificial independence on a point and its negative."))),
            DescribeRole.Theorem)), []));
}
