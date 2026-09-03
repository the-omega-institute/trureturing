using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros;

internal sealed class PeakLipschitzZeroFreeDiskDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Zeros/PeakLipschitzZeroFreeDisk.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A strict peak-versus-displacement budget certifies a zero-free disk, and an affine "
            + "function places a zero exactly at the limiting radius.",
        H("Peak-Lipschitz Zero-Free Disk"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("strict-peak-lipschitz-zero-free-disk"),
                DeclarationHandle.Create(Prefix + "strict_peak_lipschitz_zero_free_disk"),
                H("Strict displacement budget excludes zeros"),
                StatementSource.FromAuthor(ZeroFreeFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The positive radius and nonnegative slope make Lr nonnegative, so the "
                            + "strict budget Lr < A also proves A is positive. The center norm is "
                            + "at least A, while every displacement in the radius-r "
                            + "disk changes the value by at most L times the distance. The strict "
                            + "budget Lr < A makes a zero impossible throughout the disk.")),
                    Paragraph(Text(
                        "This is the formal core of the Bernstein and peak-height chain in source "
                            + "Theorem 6.180. The source's polynomial-specific Bernstein estimate "
                            + "and numerical Bragg data supply A and L; they are not silently assumed "
                            + "or reproduced by this abstract disk lemma.")),
                    Paragraph(Text(
                        "Repository and pinned-Mathlib searches found nearby analytic-ball tools but "
                            + "no packaged strict peak-budget theorem."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("peak-lipschitz-radius-is-sharp"),
                DeclarationHandle.Create(Prefix + "peak_lipschitz_radius_is_sharp"),
                H("The limiting radius is sharp"),
                StatementSource.FromAuthor(SharpFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For A,L > 0, the affine model f(z)=A-Lz has center norm A, exact "
                        + "Lipschitz slope L, and a zero at distance A/L. This constructive boundary "
                        + "witness shows why the zero-free conclusion uses a strict disk."))),
                DescribeRole.Theorem))));

    private static Formula ZeroFreeFormula() => Disp(Seq(
        F.Id("r"), Gt, Sp, D(0), Comma, Sp, F.Id("L"), Geq, Sp, D(0), Comma, Sp,
        F.Id("Lr"), Lt, Sp, F.Id("A"), Comma, Quad, Sp,
        Vert, Sp, F.Id("f"), Open, F.Id("w"), Close, Sp, Vert,
        Geq, Sp, F.Id("A"), Comma, Quad, Sp,
        Vert, Sp, F.Id("f"), Open, F.Id("z"), Close, Minus,
        F.Id("f"), Open, F.Id("w"), Close, Sp, Vert, Leq, Sp,
        F.Id("L"), Operatorname, Grp(F.Id("dist")), Open, F.Id("z"), Comma, Sp, F.Id("w"), Close,
        Quad, Sp, Rightarrow, Quad, Sp,
        Operatorname, Grp(F.Id("dist")), Open, F.Id("z"), Comma, Sp, F.Id("w"), Close,
        Lt, Sp, F.Id("r"), Quad, Sp, Rightarrow, Quad, Sp,
        F.Id("f"), Open, F.Id("z"), Close, Neq, Sp, D(0)));

    private static Formula SharpFormula() => Disp(Seq(
        F.Id("A"), Gt, Sp, D(0), Comma, Sp, F.Id("L"), Gt, Sp, D(0), Quad, Sp,
        Rightarrow, Quad, Sp,
        F.Id("f"), Open, F.Id("z"), Close, Eq, F.Id("A"), Minus, F.Id("Lz"), Comma, Quad, Sp,
        Vert, Sp, F.Id("f"), Open, D(0), Close, Sp, Vert, Eq, F.Id("A"), Comma, Quad, Sp,
        F.Id("f"), Open, Frac, Grp(F.Id("A")), Grp(F.Id("L")), Close, Eq, D(0)));
}
