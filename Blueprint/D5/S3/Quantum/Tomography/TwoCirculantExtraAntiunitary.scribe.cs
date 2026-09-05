using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Tomography;

internal sealed class TwoCirculantExtraAntiunitaryDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A conjugate-block matrix preserves skew-conjugate orthogonal partners of common-unbiased vectors.",
        H("Extra Antiunitary Partners on a Two-Circulant Stratum"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("conjugate-block-common-unbiased-orthogonal-partner"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Tomography/TwoCirculantExtraAntiunitary."
                    + "conjugate_block_common_unbiased_orthogonal_partner"),
                H("The explicit skew-conjugate partner preserves both flatness conditions"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For H=[A B; conjugate(B) -conjugate(A)], split a vector v into equal "
                        + "channels vL,vR and define w=(-conjugate(vR),conjugate(vL)). "
                        + "The theorem proves coordinate flatness of w, the same squared-modulus "
                        + "condition for H* w as for H* v, and the exact orthogonality v* w=0.")),
                    Paragraph(Text(
                        "The proof uses the existing Mathlib block-matrix, matrix-vector product, "
                        + "dot-product, finite-sum, and complex conjugation APIs. The identity "
                        + "H* w=-Theta(H* v) supplies the second flatness condition. Skewness "
                        + "cancels the two channel contributions to v* w.")),
                    Paragraph(Text(
                        "On the symmetric-block real-parameter stratum of the order-six "
                        + "two-circulant family, this partner can interchange the nontrivial "
                        + "Fourier modes. It is therefore unsafe to infer modewise orthogonality "
                        + "from global orthogonality. The separate rational-interval certificate "
                        + "encloses a concrete counterexample and verifies a twelve-ray induced "
                        + "orthogonality graph. That analytic enclosure and exhaustive completion "
                        + "classification are not conclusions of this Lean declaration."))),
                DescribeRole.Theorem))));

    private static Formula Apply(string name, params Formula[] arguments)
    {
        var parts = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var i = 0; i < arguments.Length; i++)
        {
            if (i > 0) { parts.Add(Comma); parts.Add(Sp); }
            parts.Add(arguments[i]);
        }
        parts.Add(Close);
        return Seq([.. parts]);
    }

    private static Formula TheoremFormula() => Disp(Seq(
        Apply("ConjugateBlock", F.Id("H"), F.Id("A"), F.Id("B")), Sp, Land, Sp,
        Apply("CoordinateUnitAndImageFlat", F.Id("H"), F.Id("v"), F.Id("rho")),
        Sp, Rightarrow, RowBreak,
        Apply("CoordinateUnitAndImageFlat", F.Id("H"), F.Id("w"), F.Id("rho")),
        Sp, Land, Sp, Apply("Orthogonal", F.Id("v"), F.Id("w")), Dot));
}
