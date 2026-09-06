using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuantumChannels;

internal sealed class UnitaryKrausMixingInvarianceDocument : IScribeDocumentDefinition
{
    private const string DeclarationPrefix =
        "D5/S3/QuantumChannels/UnitaryKrausMixingInvariance.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A column-orthogonal change of finite Kraus generators leaves the induced channel "
            + "independent of the branch labels used to present it.",
        H("Unitary Kraus Mixing Invariance"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("kraus-generators-are-mixed-by-a-complex-coefficient-matrix"),
                DeclarationHandle.Create(DeclarationPrefix + "unitaryKrausMixing"),
                H("Kraus generators are mixed by a complex coefficient matrix"),
                StatementSource.FromAuthor(MixingFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For finite old-label set iota and new-label set kappa, the generator with "
                        + "new label k is the finite complex linear combination of the original "
                        + "generators whose coefficients are the k-th row of U."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("column-orthogonal-kraus-mixing-preserves-the-channel"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "unitary_kraus_mixing_invariance"),
                H("Column-orthogonal Kraus mixing preserves the channel"),
                StatementSource.FromAuthor(InvarianceFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let iota, kappa, and n be finite types, let U be a complex coefficient "
                            + "matrix, let S be an iota-indexed family of complex n-by-n matrices, "
                            + "and let X be any complex n-by-n matrix. Assume the columns of U are "
                            + "orthonormal in the displayed component convention. Then mixing S by "
                            + "U leaves the sum of Kraus sandwiches exactly unchanged.")),
                    Paragraph(Text(
                        "The coefficient convention sums U(k,i) times the conjugate of U(k,j). "
                            + "It is the complex conjugate of the usual column-inner-product "
                            + "identity with i and j exchanged, and hence has precisely the same "
                            + "content. Rectangular isometries are allowed, so the theorem also "
                            + "covers presentations with redundant new branch labels.")),
                    Paragraph(Text(
                        "The proof distributes the adjoint through the finite linear combination, "
                            + "expands both finite sums, commutes their order, and uses column "
                            + "orthogonality to eliminate every cross term. The remaining diagonal "
                            + "terms are exactly the original Kraus sandwich sum.")),
                    Paragraph(Text(
                        "This is the finite-dimensional matrix content of observer-gauge "
                            + "invariance. It does not assert that Clark bases exist, that arbitrary "
                            + "phase observers are related by such a matrix, or that an inner naming "
                            + "map has any further interpretation; those notions are not defined by "
                            + "the source atom as formal premises."))),
                DescribeRole.Theorem))));

    private static Formula Indexed(Formula value, params Formula[] indices) =>
        Seq(value, Underscore, Grp(Seq(indices)));

    private static Formula Starred(Formula value) =>
        Seq(Operatorname, Grp(F.Id("star")), Open, value, Close);

    private static Formula MixingFormula()
    {
        Formula k = F.Id("k"), j = F.Id("j");
        Formula t = F.Id("T"), u = F.Id("U"), s = F.Id("S");

        return Disp(Seq(
            Forall, Sp, k, Sp, InMacro, Sp, Kappa, Comma, Esc,
            Indexed(t, k), Sp, Eq, Sp,
            Sum, Underscore, Grp(j, Sp, InMacro, Sp, Iota), Sp,
            Indexed(u, k, j), Sp, Indexed(s, j), Dot));
    }

    private static Formula InvarianceFormula()
    {
        Formula i = F.Id("i"), j = F.Id("j"), k = F.Id("k");
        Formula u = F.Id("U"), s = F.Id("S"), t = F.Id("T"), x = F.Id("X");
        Formula delta = DeltaLower;

        Formula orthogonality = Seq(
            Forall, Sp, i, Comma, Sp, j, Sp, InMacro, Sp, Iota, Comma, Esc,
            Sum, Underscore, Grp(k, Sp, InMacro, Sp, Kappa), Sp,
            Indexed(u, k, i), Sp, Starred(Indexed(u, k, j)),
            Sp, Eq, Sp, Indexed(delta, i, j));
        Formula mixedSum = Seq(
            Sum, Underscore, Grp(k, Sp, InMacro, Sp, Kappa), Sp,
            Indexed(t, k), Sp, x, Sp, Starred(Indexed(t, k)));
        Formula originalSum = Seq(
            Sum, Underscore, Grp(j, Sp, InMacro, Sp, Iota), Sp,
            Indexed(s, j), Sp, x, Sp, Starred(Indexed(s, j)));

        return Disp(Seq(
            Forall, Sp, Iota, Comma, Sp, Kappa, Comma, Sp, F.Id("n"), Comma, Sp,
            u, Comma, Sp, s, Comma, Sp, x, Comma, Esc,
            Open, orthogonality, Close, Sp, Rightarrow, Sp,
            mixedSum, Sp, Eq, Sp, originalSum, Dot));
    }
}
