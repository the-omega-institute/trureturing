using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Lattices.Counting;

internal sealed class ShiftedBallCountDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The normalized integer grid count in a closed three-dimensional ball tends to its unit volume for every fixed center.",
        H("Integer grid counts in shifted balls"),
        Blocks(Describe.Lean(
            DescribeId.Create("shifted-ball-grid-count-limit"),
            DeclarationHandle.Create("D5/S3/Arith/Lattices/Counting/ShiftedBallCount.shifted_limit"),
            H("The normalized count at a fixed center"),
            StatementSource.FromAuthor(Limit()), AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("For a fixed center c in Euclidean three-space, C(c,r) counts the points of the integer coordinate grid in the closed ball of radius r with center c.")),
                Paragraph(Text("The standard coordinate map preserves volume. The centered unit ball is bounded and measurable, its frontier is a sphere of volume zero, and its volume is 4π/3. Dilations are nested for positive radii. These facts give the centered limit by Mathlib's tendsto_card_div_pow_atTop_volume'.")),
                Paragraph(Text("Write d for the distance from c to the origin. The centered balls of radii r−d and r+d enclose the shifted count from below and above. For either fixed shift the cubed ratio of the shifted radius to r tends to one, so the two normalized bounds have the same limit."))),
            DescribeRole.Theorem))));

    private static Formula Limit()
    {
        Formula r = F.Id("r"), c = F.Id("c");
        return Disp(Seq(Lim, Underscore, Grp(r, Sp, To, Sp, Infty), Sp,
            new Formula.Fraction(new Formula.Apply(F.Id("C"), [c, r]), new Formula.Power(r, D(3))),
            Sp, Eq, Sp, new Formula.Fraction(Seq(D(4), Pi), D(3))));
    }
}
