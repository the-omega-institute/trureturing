using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.Hyperideal;

internal sealed class SupportRatioExitDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finite family of affine-linear supports admits a maximal-ratio exit point.",
        H("Finite support ratio exit"),
        Blocks(
            Paragraph(Text("Let S be a finite index set and let each L_r be affine-linear "
                + "along the ray from a to x. Assume every support in S is strictly negative "
                + "at a, supports outside S vanish at a, and all supports are nonpositive at x. "
                + "If at least one support increases strictly from a to x, choose a maximal "
                + "increase ratio. The resulting t is positive and at most one; the rescaled "
                + "point remains in every support halfspace and lies on a supporting trace.")),
            Describe.Lean(
                DescribeId.Create("support-ratio-exit"),
                DeclarationHandle.Create(
                    "D5/S3/Geometry/Hyperideal/SupportRatioExit.support_ratio_exit"),
                H("A maximal support ratio reaches a boundary"),
                StatementSource.FromAuthor(F.Disp(Statement())),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The theorem is a finite-dimensional ratio-maximization "
                        + "lemma. It supplies a reusable exit construction for polytope and "
                        + "support-ray arguments; no particular geometric body or subdivision "
                        + "is assumed."))),
                DescribeRole.Theorem))));

    private static Formula Statement()
    {
        var S = F.Id("S");
        var L = F.Id("L");
        var a = F.Id("a");
        var x = F.Id("x");
        var r = F.Id("r");
        return Seq(
            Forall, Sp, r, Sp, InMacro, Sp, Call("S"), Comma, Sp,
            Call("L", r, a), Sp, Lt, Sp, D(0), Sp, Rightarrow, Sp,
            Call("ratioExit", S, L, a, x), Dot);
    }

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(F.Id(name), [.. args]);
}
