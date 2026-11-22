using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.StaticExchange;

internal sealed class IsotropicShellInversionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/StaticExchange/IsotropicShellInversion.";
    private static readonly Formula R = F.Id("r"), T = F.Id("t");
    private static Formula At(string name, Formula x) => Seq(F.Id(name), Open, x, Close);
    private static Formula Integral(Formula lo, Formula fx) =>
        Seq(Int, Underscore, Grp(lo), Caret, Grp(Infty), Sp, fx, Thin, Sp, F.Id("dr"));

    private static Formula Projection() => Disp(Seq(At("P", T), Eq,
        Integral(T, Seq(Frac, Grp(At("h", R)), Grp(D(2), R)))));
    private static Formula Reconstructed() => Disp(Seq(At("h", R), Eq, Minus, D(2), R, At("d", R)));
    private static Formula Mass() => Disp(Seq(Begin, Grp(F.Id("aligned")),
        Amp, Forall, Sp, R, Sp, Ge, Sp, D(0), Comma, At("h", R), Sp, Ge, Sp, D(0), RowBreak,
        Amp, Forall, Sp, T, Sp, Ge, Sp, D(0), Comma, At("P", T), Eq, At("f", T), RowBreak,
        Amp, Integral(D(0), At("h", R)), Eq, D(2), Integral(D(0), At("f", R)),
        End, Grp(F.Id("aligned"))));
    private static Formula Unique() => Disp(Seq(Forall, Sp, R, Gt, D(0), Comma, At("h", R), Eq,
        Minus, D(2), R, F.Id("f"), Apos, Open, R, Close));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The uniform coordinate kernel of a positive-radius shell gives a density transform. If the shell density is continuous and its projection tails are absolutely integrable, differentiation recovers it at every positive radius.",
        H("Recovering an isotropic shell density from one coordinate"),
        Blocks(
            Describe.Lean(DescribeId.Create("projection"), DeclarationHandle.Create(Prefix + "projection"),
                H("Coordinate density of a shell mixture"), StatementSource.FromAuthor(Projection()),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("For t≥0, mix the uniform coordinate density on (−r,r) against the radius density h(r). The lower limit t restricts the integral to shells reaching that coordinate."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("shell"), DeclarationHandle.Create(Prefix + "shell"),
                H("Shell density from a derivative"), StatementSource.FromAuthor(Reconstructed()),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Here d is the derivative of the coordinate density at positive radii. The reconstructed density at zero equals zero for every choice of d(0)."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("projection-mass"), DeclarationHandle.Create(Prefix + "shell_projection_mass"),
                H("Projection and mass of the reconstructed density"), StatementSource.FromAuthor(Mass()),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Assume f is right-continuous at zero and absolutely integrable on the positive half-line, with derivative d(r)≤0 at every positive radius. Monotonicity bounds r f(r) by integrals of |f| on tails and yields its decay. Applying the improper fundamental theorem to r f(r) minus an antiderivative of f gives absolute integrability of r d(r). For h(r)=−2r d(r), the tail integrand is −d(r) for r>0. Integrating the derivative recovers f(t), and integration by parts against r gives the total mass of the even extension of f."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("unique-density"), DeclarationHandle.Create(Prefix + "shell_density_unique"),
                H("Pointwise recovery on positive radii"), StatementSource.FromAuthor(Unique()),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Assume h is continuous on positive radii, h(r)/(2r) is absolutely integrable on every positive tail, and its tail integral equals f(t) at every t>0. Subtracting two tails gives the integral on their intervening interval. The fundamental theorem of calculus then gives f′(r)=−h(r)/(2r) at every positive r."))), DescribeRole.Theorem))));
}
