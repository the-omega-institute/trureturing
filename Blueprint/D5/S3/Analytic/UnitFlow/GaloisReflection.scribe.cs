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
                        "Lean fixes the source field itself as the Mathlib quadratic algebra "
                        + "K_phi = QuadraticAlgebra(Q, 1, 1), whose generator satisfies "
                        + "omega^2 = omega + 1. The two algebra embeddings send omega to the "
                        + "golden ratio phi and its real conjugate psi. The star involution is the "
                        + "nonidentity Galois automorphism and exchanges these distinct embeddings.")),
                    Paragraph(Text(
                        "For nonzero algebraic integers alpha, the definitions set a(alpha) and "
                        + "b(alpha) to the squared absolute values under those fixed embeddings, "
                        + "Q_eta(alpha) = exp(eta)a(alpha) + exp(-eta)b(alpha), and Z_s(eta) to the "
                        + "complex-power sum. The public premises include Re(s) > 1, summability at "
                        + "every eta, regulator periodicity, and a nonconstancy certificate exhibiting "
                        + "two parameter points with different zeta values.")),
                    Paragraph(Text(
                        "Restricting the fixed star automorphism with Mathlib's "
                        + "RingOfIntegers.mapAlgEquiv reindexes a genuinely summable series after "
                        + "Q_eta(tau(alpha)) = Q_(-eta)(alpha). Here A_p is the displayed Lean "
                        + "monoid homomorphism from Mathlib's "
                        + "DihedralGroup 0 to permutations of the real parameter line: "
                        + "A_p(r_k)(eta) = eta + k p and A_p(sr_k)(eta) = -eta - k p. "
                        + "The theorem concludes all three conjuncts shown below: global reflection, "
                        + "injectivity of A_p, and invariance under every group element. The injectivity "
                        + "uses p != 0, proved from phi > 1, so the infinite-dihedral structure does not "
                        + "collapse to a one-point or nonfaithful action."))),
                DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula s = F.Id("s");
        Formula eta = F.Id("eta");
        Formula etaOne = F.Id("eta1");
        Formula etaTwo = F.Id("eta2");
        Formula g = F.Id("g");
        Formula z = F.Id("Zs");
        Formula p = F.Id("p");
        Formula goldenField = F.Id("Kphi");
        Formula action = F.Id("Ap");
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula complex = Seq(Mathbb, Grp(F.Id("C")));
        Formula dinfinity = Seq(F.Id("DihedralGroup"), Open, D(0), Close);
        Formula summable = Grp(Seq(
            Forall, Sp, eta, Sp, InMacro, Sp, real, Comma, Sp,
            Operatorname, Grp(F.Id("Summable")), Open, F.Id("term"),
            Open, s, Comma, Sp, eta, Close, Close));

        return Disp(Seq(
            goldenField, Sp, Eq, Sp, F.Id("QuadraticAlgebra"),
            Open, Mathbb, Grp(F.Id("Q")), Comma, Sp, D(1), Comma, Sp, D(1), Close,
            Comma, RowBreak,
            p, Sp, Eq, Sp, D(2), Sp, Log, Open, Varphi, Close, Comma, RowBreak,
            Forall, Sp, s, Sp, InMacro, Sp, complex, Comma, RowBreak, Grp(),
            OpenBracket,
            D(1), Sp, Lt, Sp, Re, Open, s, Close, Sp, Land, RowBreak,
            summable, Sp, Land, RowBreak,
            F.Id("Periodic"), Open, z, Comma, Sp, p, Close, Sp, Land, RowBreak,
            Exists, Sp, etaOne, Comma, Sp, etaTwo, Sp, InMacro, Sp, real, Comma, Sp,
            z, Open, etaOne, Close, Sp, Neq, Sp, z, Open, etaTwo, Close,
            CloseBracket, RowBreak,
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
