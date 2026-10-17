using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.Hyperideal;

internal sealed class LinearNonposOnHullDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A linear support inequality on generators extends across their convex hull.",
        H("A linear nonpositive bound is preserved by convexification"),
        Blocks(
            Paragraph(Text("Let s be a set of points in the four-coordinate real space and let L be a real linear functional. "
                + "If L is nonpositive at every generator in s, then it is nonpositive at every point of the convex hull of s.")),
            Describe.Lean(
                DescribeId.Create("linear-nonpos-on-hull"),
                DeclarationHandle.Create(
                    "D5/S3/Geometry/Hyperideal/LinearNonposOnHull.linear_nonpos_on_hull"),
                H("Linear support inequalities survive convexification"),
                StatementSource.FromAuthor(F.Disp(F.Id("linearNonposOnHull"))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The convex hull is the smallest convex set containing the generators. "
                        + "Linearity evaluates a two-point convex combination as the corresponding weighted sum, "
                        + "and nonnegative weights preserve the nonpositive bounds."))),
                DescribeRole.Theorem))));
}
