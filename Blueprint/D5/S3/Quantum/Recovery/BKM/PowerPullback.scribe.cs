using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Recovery.BKM;

internal sealed class PowerPullbackDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Cubic pullback of the actual BKM integral.",
        H("Cubic pullback of the actual BKM integral"),
        Blocks(Describe.Lean(
            DescribeId.Create("omega-cube"),
            DeclarationHandle.Create("D5/S3/Quantum/Recovery/BKM/PowerPullback.omega_cube"),
            H("The BKM integral at a positive definite cube"),
            StatementSource.FromAuthor(CubeIdentity()),
            AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/SpinModels/wu2026sharp")),
            Blocks(
                Paragraph(Text(
                    "Let B be a positive definite complex matrix on any finite index type and " +
                    "let X be any complex matrix of the same size. Ω is the actual integral " +
                    "BKMRelativeDensity.omega, also used in PetzRotatedBKM. Its integrand at " +
                    "reference B is B to the power s, times X, times B to the power 1 − s, " +
                    "integrated from 0 to 1. The square and cube in the identity are ordinary " +
                    "matrix powers and 1/3 is a real scalar.")),
                Paragraph(Text(
                    "Rescale the integral at B³ by t = 3s and split [0, 3] into three unit " +
                    "intervals. Translating each interval back to [0, 1] factors out the " +
                    "ordered left and right powers of B.")),
                Paragraph(Text(
                    "In the quadratic entropy calculation for Wu’s Remark 3.15, equation " +
                    "(3.54), write U = Ω_B(V) for the Hermitian input tangent and A = B²U + " +
                    "BUB + UB² for its cube tangent. At Z = Tr(B³) > 0 and ρ = B³/Z, the " +
                    "normalized tangent is (A − ρ Tr(A))/Z. The cube identity, scalar homogeneity, " +
                    "and Ω_ρ(I) = ρ give its inverse BKM image 3V − (Tr(A)/Z)I. This " +
                    "supplies the tangent metric contribution. The full physical Hessian " +
                    "still requires differentiating the semigroup deficit along the physical path."))),
            DescribeRole.Theorem))));

    private static Formula CubeIdentity()
    {
        var b = Id("B");
        var x = Id("X");
        var bSquared = F.Seq(b, F.Caret, F.Grp(Num(2)));
        var bCubed = F.Seq(b, F.Caret, F.Grp(Num(3)));
        var omegaAtB = OmegaAt(b, x);
        var sum = Add(Add(Multiply(bSquared, omegaAtB), Multiply(Multiply(b, omegaAtB), b)),
            Multiply(omegaAtB, bSquared));
        var average = F.Seq(new Formula.Fraction(Num(1), Num(3)), F.Cdot,
            F.Left, F.Open, sum, F.Right, F.Close);
        return F.Disp(Equal(OmegaAt(bCubed, x), average));
    }

    private static Formula OmegaAt(Formula reference, Formula direction) =>
        new Formula.Apply(new Formula.Subscript(F.Omega, reference), [direction]);
}
