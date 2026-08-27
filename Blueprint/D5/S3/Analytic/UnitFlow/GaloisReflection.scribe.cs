using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.UnitFlow;

internal sealed class GaloisReflectionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Galois conjugation reflects the Golden unit-flow principal zeta and completes its regulator periodicity to a faithful infinite-dihedral symmetry.",
        H("Galois Reflection of the Golden Unit Flow"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("golden-unit-flow-galois-reflection"),
                DeclarationHandle.Create(
                    "D5/S3/Analytic/UnitFlow/GaloisReflection.galois_reflection"),
                H("Galois reflection and infinite-dihedral invariance"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let K be a number field with real embeddings sigmaPlus and sigmaMinus, "
                        + "and let tau be the Q-algebra automorphism giving Galois conjugation. "
                        + "For a nonzero algebraic integer alpha, the Lean definitions set "
                        + "a(alpha) = |sigmaPlus(alpha)|^2, b(alpha) = |sigmaMinus(alpha)|^2, "
                        + "Q_eta(alpha) = exp(eta)a(alpha) + exp(-eta)b(alpha), and define Z_s(eta) "
                        + "as the complex-power tsum of Q_eta(alpha)^(-s) over the actual subtype "
                        + "of nonzero elements of the ring of integers.")),
                    Paragraph(Text(
                        "The hypotheses shown in the formula are exactly the public Lean premises: "
                        + "the two a/b exchange equations, Re(s) > 1 from the source domain, "
                        + "and period p = 2 log(phi) from the immediately preceding regulator theorem. "
                        + "Restricting tau with Mathlib's RingOfIntegers.mapAlgEquiv gives an equivalence "
                        + "of the nonzero summation index, and Equiv.tsum_eq reindexes the series after "
                        + "Q_eta(tau(alpha)) = Q_(-eta)(alpha).")),
                    Paragraph(Text(
                        "Here A_p is the displayed Lean monoid homomorphism from Mathlib's "
                        + "DihedralGroup 0 to permutations of the real parameter line: "
                        + "A_p(r_k)(eta) = eta + k p and A_p(sr_k)(eta) = -eta - k p. "
                        + "The theorem concludes all three conjuncts shown below: global reflection, "
                        + "injectivity of A_p, and invariance under every group element. The injectivity "
                        + "uses p != 0, proved from phi > 1, so the infinite-dihedral structure does not "
                        + "collapse to a one-point or nonfaithful action."))),
                DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula k = F.Id("K");
        Formula alpha = F.Id("alpha");
        Formula s = F.Id("s");
        Formula eta = F.Id("eta");
        Formula g = F.Id("g");
        Formula sigmaPlus = F.Id("sigmaPlus");
        Formula sigmaMinus = F.Id("sigmaMinus");
        Formula tau = F.Id("tau");
        Formula z = F.Id("Zs");
        Formula p = F.Id("p");
        Formula action = F.Id("Ap");
        Formula a = F.Id("a");
        Formula b = F.Id("b");
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula complex = Seq(Mathbb, Grp(F.Id("C")));
        Formula dinfinity = Seq(F.Id("DihedralGroup"), Open, D(0), Close);

        return Disp(Seq(
            p, Sp, Eq, Sp, D(2), Sp, Log, Open, Varphi, Close, Comma, RowBreak,
            Forall, Sp, k, Comma, Sp,
            F.Id("NumberField"), Open, k, Close, Comma, Sp,
            Forall, Sp, sigmaPlus, Comma, Sp, sigmaMinus, Sp, InMacro, Sp,
            F.Id("Emb"), Open, k, Comma, Sp, real, Close, Comma, Sp,
            Forall, Sp, tau, Sp, InMacro, Sp,
            F.Id("AutQ"), Open, k, Close, Comma, Sp,
            Forall, Sp, s, Sp, InMacro, Sp, complex, Comma, RowBreak, Grp(),
            OpenBracket,
            Forall, Sp, alpha, Sp, InMacro, Sp,
            F.Id("RingOfIntegers"), Open, k, Close, Comma, Sp,
            a, Open, tau, Open, alpha, Close, Close, Sp, Eq, Sp,
            b, Open, alpha, Close, Sp, Land, Sp,
            b, Open, tau, Open, alpha, Close, Close, Sp, Eq, Sp,
            a, Open, alpha, Close, CloseBracket, Sp, Land, RowBreak,
            D(1), Sp, Lt, Sp, Re, Open, s, Close, Sp, Land, Sp,
            F.Id("Periodic"), Open, z, Comma, Sp, p, Close, RowBreak,
            Longrightarrow, RowBreak, Grp(),
            OpenBracket,
            Forall, Sp, eta, Sp, InMacro, Sp, real, Comma, Sp,
            z, Open, eta, Close, Sp, Eq, Sp,
            z, Open, Minus, eta, Close, CloseBracket, Sp, Land, RowBreak,
            Operatorname, Grp(F.Id("Injective")), Open,
            action, Colon, Sp, dinfinity, Sp, To, Sp,
            F.Id("Perm"), Open, real, Close, Close, Sp, Land, RowBreak, Grp(),
            OpenBracket,
            Forall, Sp, g, Sp, InMacro, Sp, dinfinity, Comma, Sp,
            Forall, Sp, eta, Sp, InMacro, Sp, real, Comma, Sp,
            z, Open, action, Open, g, Close, Open, eta, Close, Close,
            Sp, Eq, Sp, z, Open, eta, Close, CloseBracket, Dot));
    }
}
