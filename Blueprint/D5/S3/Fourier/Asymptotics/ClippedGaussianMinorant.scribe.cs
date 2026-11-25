using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Fourier.Asymptotics;

internal sealed class ClippedGaussianMinorantDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Fourier/Asymptotics/ClippedGaussianMinorant";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The rescaled clipped power integral approximates the Gaussian integral uniformly over oriented windows.",
        H("Gaussian limit of the variance minorant"),
        Blocks(
            Paragraph(Text(
                "Let V and A be arbitrary real sequences indexed by natural n, with V(n)>0 eventually. " +
                "Set s(n)=sqrt(n V(n)), R(n)=A(n)s(n), and let I(n) be s(n) times the integral " +
                "of max(0,1-V(n)t²/2)^(2n) from -A(n) to A(n). " +
                "Write G(r) for the oriented integral of exp(-u²) from -r to r.")),
            Describe.Lean(DescribeId.Create("window-error"),
                DeclarationHandle.Create(Owner + ".clipped_gaussian_window_error"),
                H("Uniform approximation on moving windows"),
                StatementSource.FromAuthor(WindowError()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The substitution u=s(n)t gives the profile q_n(u)=max(0,1-u²/(2n))^(2n) for n>0. " +
                    "The inequality 1-x≤exp(-x) bounds this nonnegative profile by exp(-u²) everywhere. " +
                    "At each fixed u the clipping is eventually inactive and the elementary power limit gives " +
                    "q_n(u)→exp(-u²). Dominated convergence bounds every oriented interval error by the same " +
                    "whole-line integral of |q_n(u)-exp(-u²)|, which tends to zero."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("full-limit"),
                DeclarationHandle.Create(Owner + ".clipped_gaussian_full_limit_iff"),
                H("Characterization of the full Gaussian limit"),
                StatementSource.FromAuthor(FullLimit()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "When R(n) tends to positive infinity, the Gaussian window integral tends to its whole-line " +
                    "value sqrt(pi). Conversely, G is monotone on the whole real line, including negative oriented " +
                    "radii. For every finite r, G(r)<sqrt(pi), since a further nonempty interval contributes " +
                    "strictly positive Gaussian mass. If I(n) tends to sqrt(pi), the uniform error implies the same " +
                    "limit for G(R(n)). This forces R(n)>r eventually, for each real r. No convergence assumption " +
                    "on V or A separately is needed.")),
                    Paragraph(Text(
                        "For fixed V,h>0 take A(n)=pi/h. Then R(n) tends to positive infinity and the " +
                        "coefficient h I(n)/(2 pi) tends to h/(2 sqrt(pi)). For finite nonnegative weights " +
                        "w on affine lattice frequencies g(j)=b+h a(j), integer a(j), total mass W, and " +
                        "a center c with sum w(j)(g(j)-c)^2 <= V W, the finite Fourier variance bound " +
                        "gives E_p(eta) >= h W^(2p)/(2 pi) times the unscaled clipped integral for eta>=0. " +
                        "Consequently, for every epsilon>0 and all sufficiently large p, " +
                        "(h/(2 sqrt(pi))-epsilon) W^(2p) <= sqrt(p V) E_p(eta). " +
                        "Here E_p(eta) is the weighted ordered-pair collision mass of degree-p frequency sums " +
                        "at resolution eta. The resulting coefficient is a lower bound, and additional phase " +
                        "peaks can contribute to the collision mass when the lattice spacing is nonmaximal."))),
                DescribeRole.Theorem))));

    private static Formula Limit(Formula body) =>
        F.Seq(F.Lim, F.Underscore, F.Grp(F.Id("n"), F.Sp, F.To, F.Sp, F.Infty), F.Sp, body);

    private static Formula WindowError() =>
        F.Disp(Equal(Limit(F.Grp(Subtract(Call("I", F.Id("n")), Call("G", Call("R", F.Id("n")))))), F.D(0)));

    private static Formula FullLimit() =>
        F.Disp(new Formula.Logic(
            Equal(Limit(Call("I", F.Id("n"))), F.Seq(F.Sqrt, F.Grp(F.Pi))),
            FormulaLogicOperator.Iff,
            Equal(Limit(Call("R", F.Id("n"))), F.Infty)));
}
