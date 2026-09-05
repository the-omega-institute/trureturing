using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.TestFunctions;

internal sealed class EvenTestFunctionFiniteInterpolationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Weil/TestFunctions/EvenTestFunctionFiniteInterpolation.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Sign-separated finite data admit actual even smooth compact interpolation, with a specified support radius from a bound on the nodes.",
        H("Finite Even Weil Interpolation"),
        Blocks(
            Describe.Lean(DescribeId.Create("even-weil-finite-interpolation"),
                DeclarationHandle.Create(Prefix + "even_weilTestFunction_finite_interpolation"),
                H("Exact finite interpolation"),
                StatementSource.FromAuthor(Disp(F.Id("For a finite complex set without distinct opposite nodes and arbitrary complex values, an even smooth compact Weil test realizes every value."))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Square the sign-separated nodes, use Mathlib Lagrange interpolation and apply the resulting polynomial differential operator to an even seed. The original proof and public statement are preserved."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("even-weil-quantitative-radius-interpolation"),
                DeclarationHandle.Create(Prefix + "even_weilTestFunction_finite_interpolation_with_radius"),
                H("A specified interpolation radius"),
                StatementSource.FromAuthor(Disp(F.Id("If all nodes have norm at most R>=0, the actual interpolating test can be supported in [-h,h], h=1/(4(R+1))."))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Use the explicit normalized seed whose transform norm is at least one half at every node. The existing polynomial differential constructor is reused. Every derivative has topological support within the seed support, so the complete interpolant has the specified radius."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("even-weil-unit-support-interpolation"),
                DeclarationHandle.Create(Prefix + "even_weilTestFunction_finite_interpolation_unit_support"),
                H("Fixed support for every finite node family"),
                StatementSource.FromAuthor(Disp(F.Id("Every finite sign-separated assignment is realized by an actual test supported in [-1,1]."))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Bound the finite node norms by their sum and apply the explicit-radius construction. The radius is at most one. This does not give a norm or derivative bound uniform over colliding nodes and does not assert negativity of the full Weil form in this small window."))), DescribeRole.Theorem)), []));
}
