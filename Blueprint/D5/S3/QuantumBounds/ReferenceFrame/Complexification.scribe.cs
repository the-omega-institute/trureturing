using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuantumBounds.ReferenceFrame;

internal sealed class ComplexificationDocument : IScribeDocumentDefinition
{
    private const string LeanPrefix =
        "D5/S3/QuantumBounds/ReferenceFrame/Complexification.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The finite exchange-channel fidelity, sharp optimum, and paired top eigenspace extend from real to complex reference amplitudes.",
        H("Complex Reference-Frame Machinery"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("complex-fidelity-is-the-nearest-neighbour-quadratic"),
                DeclarationHandle.Create(
                    LeanPrefix + "complex_entanglement_fidelity_eq_nearest_neighbor_quadratic"),
                H("Complex fidelity is the nearest-neighbour quadratic"),
                StatementSource.FromAuthor(F.Disp(F.Seq(
                    F.Forall, F.Sp, F.Id("c"), F.Sp, F.InMacro, F.Sp,
                    F.Mathbb, F.Grp(F.Id("C")), F.Caret, F.Grp(F.Id("N")),
                    F.Comma, F.Quad, F.Sp,
                    F.Id("F"), F.Underscore, F.Grp(F.Id("e")),
                    F.Open, F.Id("c"), F.Close, F.Sp, F.Eq, F.Sp,
                    F.Lvert, F.Sp, F.Id("J"), F.Id("c"), F.Rvert,
                    F.Underscore, F.Grp(F.D(2)), F.Caret, F.Grp(F.D(2))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The finite Kraus trace expression is evaluated with complex reference "
                    + "amplitudes. Its two surviving off-diagonal entries give exactly the "
                    + "squared complex norm of zero-boundary nearest-neighbour averaging."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("the-complex-optimum-equals-the-real-optimum"),
                DeclarationHandle.Create(
                    LeanPrefix + "complex_tax_optimum_eq_real_optimum"),
                H("The complex optimum equals the real optimum"),
                StatementSource.FromAuthor(F.Disp(F.Seq(
                    F.D(1), F.Leq, F.Sp, F.Id("N"), F.Sp, F.Longrightarrow, F.Sp,
                    F.Operatorname, F.Grp(F.Id("max")), F.Underscore,
                    F.Grp(F.Id("c"), F.InMacro, F.Mathbb, F.Grp(F.Id("C")),
                        F.Caret, F.Grp(F.Id("N")), F.Comma, F.Sp,
                        F.Lvert, F.Sp, F.Id("c"), F.Rvert, F.Underscore, F.Grp(F.D(2)),
                        F.Eq, F.D(1)), F.Sp,
                    F.Id("F"), F.Underscore, F.Grp(F.Id("e")),
                    F.Open, F.Id("c"), F.Close, F.Sp, F.Eq, F.Sp,
                    F.Operatorname, F.Grp(F.Id("cos")), F.Open,
                    F.Frac, F.Grp(F.Pi), F.Grp(F.Id("N"), F.Plus, F.D(1)),
                    F.Close, F.Caret, F.Grp(F.D(2))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Writing each amplitude as a real part plus I times an imaginary part "
                    + "splits both the unit norm and the averaging quadratic into two real "
                    + "summands. The frozen real upper bound applies to both summands, and a "
                    + "real sine witness attains the same value in the complex domain."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("the-complex-top-eigenspace-has-dimension-two"),
                DeclarationHandle.Create(LeanPrefix + "complex_top_eigenspace_finrank"),
                H("The complex top eigenspace has dimension two"),
                StatementSource.FromAuthor(F.Disp(F.Seq(
                    F.D(2), F.Leq, F.Sp, F.Id("N"), F.Sp, F.Longrightarrow, F.Sp,
                    F.Operatorname, F.Grp(F.Id("finrank")), F.Underscore,
                    F.Grp(F.Mathbb, F.Grp(F.Id("C"))), F.Sp,
                    F.Operatorname, F.Grp(F.Id("eigenspace")), F.Open,
                    F.Id("J"), F.Caret, F.Grp(F.D(2)), F.Comma, F.Sp,
                    F.Operatorname, F.Grp(F.Id("cos")), F.Open,
                    F.Frac, F.Grp(F.Pi), F.Grp(F.Id("N"), F.Plus, F.D(1)),
                    F.Close, F.Caret, F.Grp(F.D(2)), F.Close,
                    F.Sp, F.Eq, F.Sp, F.D(2)))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Real and imaginary parts of a complex squared-top eigenvector lie in the "
                    + "frozen real paired-mode space. Scalar extension preserves independence "
                    + "of the low and high modes, so the full complex eigenspace has complex "
                    + "dimension two for N at least two."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("the-complex-flat-vector-has-the-exact-tax"),
                DeclarationHandle.Create(LeanPrefix + "flat_tax_complex"),
                H("The complex flat vector has the exact tax"),
                StatementSource.FromAuthor(F.Disp(F.Seq(
                    F.D(2), F.Leq, F.Sp, F.Id("N"), F.Sp, F.Longrightarrow, F.Sp,
                    F.D(1), F.Sp, F.Minus, F.Sp,
                    F.Id("F"), F.Underscore, F.Grp(F.Id("e")),
                    F.Open, F.Id("m"), F.Sp, F.Mapsto, F.Sp,
                    F.D(1), F.Slash, F.Sqrt, F.Grp(F.Id("N")), F.Close,
                    F.Sp, F.Eq, F.Sp,
                    F.Frac, F.Grp(F.D(3)), F.Grp(F.D(2), F.Id("N"))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The flat complex vector is the real flat vector under the canonical "
                    + "embedding. Its tax is therefore 3/(2N) when N is at least two. The "
                    + "restriction is necessary: the frozen one-level calculation has tax "
                    + "one rather than three halves."))),
                DescribeRole.Theorem))));
}
