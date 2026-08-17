using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuantumBounds.ReferenceFrame;

internal sealed class TopEigenspaceDocument : IScribeDocumentDefinition
{
    private const string LeanPrefix =
        "D5/S3/QuantumBounds/ReferenceFrame/TopEigenspace.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Squaring finite zero-boundary path averaging pairs the low and high sine modes and makes their span the full two-dimensional top eigenspace.",
        H("Paired Top Eigenspace of Path Averaging"),
        Blocks(
            Paragraph(Text(
                "For a real vector on Fin N, J averages the left and right neighbours and "
                + "uses zero beyond the two endpoints. Its sine modes have eigenvalues "
                + "cos(k pi/(N+1)). Replacing k by N+1-k negates that eigenvalue, so the two "
                + "edge modes become degenerate after J is squared.")),
            Describe.Lean(
                DescribeId.Create("paired-sine-modes-have-the-same-squared-eigenvalue"),
                DeclarationHandle.Create(LeanPrefix + "paired_mode_cos_sq"),
                H("Paired sine modes have the same squared eigenvalue"),
                StatementSource.FromAuthor(F.Disp(F.Seq(
                    F.Operatorname, F.Grp(F.Id("cos")), F.Open,
                    F.Id("theta"), F.Underscore, F.Grp(F.Id("k")),
                    F.Close, F.Caret, F.Grp(F.D(2)), F.Sp, F.Eq, F.Sp,
                    F.Operatorname, F.Grp(F.Id("cos")), F.Open,
                    F.Id("theta"), F.Underscore,
                    F.Grp(F.Id("N"), F.Plus, F.D(1), F.Minus, F.Id("k")),
                    F.Close, F.Caret, F.Grp(F.D(2))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The paired angle is pi minus the original angle. Mathlib's cosine "
                    + "reflection identity changes its sign, and squaring removes that sign. "
                    + "At the spectral edge this pairs mode one with mode N."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("the-edge-quadratic-value-is-sharp"),
                DeclarationHandle.Create(
                    LeanPrefix + "nearest_neighbor_quadratic_edge_is_sharp"),
                H("The edge quadratic value is sharp"),
                StatementSource.FromAuthor(F.Disp(F.Seq(
                    F.Operatorname, F.Grp(F.Id("max")), F.Underscore,
                    F.Grp(F.Lvert, F.Sp, F.Id("c"), F.Rvert, F.Underscore,
                        F.Grp(F.D(2)), F.Eq, F.D(1)), F.Sp,
                    F.Id("Q"), F.Underscore, F.Grp(F.Id("N")),
                    F.Open, F.Id("c"), F.Close, F.Sp, F.Eq, F.Sp,
                    F.Operatorname, F.Grp(F.Id("cos")), F.Open,
                    F.Frac, F.Grp(F.Pi), F.Grp(F.Id("N"), F.Plus, F.D(1)),
                    F.Close, F.Caret, F.Grp(F.D(2))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The proof applies the existing universal quadratic upper bound and the "
                    + "existing normalized sine witness. It packages those two imported facts "
                    + "without re-proving either one."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("the-top-mode-space-is-exactly-two-dimensional"),
                DeclarationHandle.Create(LeanPrefix + "top_mode_space_finrank"),
                H("The top-mode space is exactly two-dimensional"),
                StatementSource.FromAuthor(F.Disp(F.Seq(
                    F.Operatorname, F.Grp(F.Id("finrank")), F.Open,
                    F.Operatorname, F.Grp(F.Id("span")), F.Open,
                    F.OpenBrace, F.Id("v"), F.Underscore, F.Grp(F.D(1)), F.Comma,
                    F.Sp, F.Id("v"), F.Underscore, F.Grp(F.Id("N")), F.CloseBrace,
                    F.Close, F.Close, F.Sp, F.Eq, F.Sp, F.D(2)))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For N at least two, the low and high modes are linearly independent. The "
                    + "first two coordinates separate their coefficients because the high mode "
                    + "alternates the signs of the strictly positive low-mode entries."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("the-full-squared-top-eigenspace-is-the-paired-mode-span"),
                DeclarationHandle.Create(
                    LeanPrefix + "squared_top_eigenspace_eq_top_mode_space"),
                H("The full squared top eigenspace is the paired-mode span"),
                StatementSource.FromAuthor(F.Disp(F.Seq(
                    F.Operatorname, F.Grp(F.Id("eigenspace")), F.Open,
                    F.Id("J"), F.Caret, F.Grp(F.D(2)), F.Comma, F.Sp,
                    F.Operatorname, F.Grp(F.Id("cos")), F.Open,
                    F.Frac, F.Grp(F.Pi), F.Grp(F.Id("N"), F.Plus, F.D(1)),
                    F.Close, F.Caret, F.Grp(F.D(2)), F.Close,
                    F.Sp, F.Eq, F.Sp,
                    F.Operatorname, F.Grp(F.Id("span")), F.Open,
                    F.OpenBrace, F.Id("v"), F.Underscore, F.Grp(F.D(1)), F.Comma,
                    F.Sp, F.Id("v"), F.Underscore, F.Grp(F.Id("N")), F.CloseBrace,
                    F.Close))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Both edge modes have the displayed squared eigenvalue, so their span "
                        + "lies in the squared eigenspace. Conversely, the squared recurrence "
                        + "determines every coordinate from the first two, bounding the full "
                        + "eigenspace dimension by two. Equality of the two subspaces follows.")),
                    Paragraph(Text(
                        "This theorem characterizes only the finite Dirichlet path operator and "
                        + "its squared spectrum. It introduces no infinite-dimensional or "
                        + "probabilistic spectral claim."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("the-full-squared-top-eigenspace-has-dimension-two"),
                DeclarationHandle.Create(
                    LeanPrefix + "squared_top_eigenspace_finrank"),
                H("The full squared top eigenspace has dimension two"),
                StatementSource.FromAuthor(F.Disp(F.Seq(
                    F.Operatorname, F.Grp(F.Id("finrank")), F.Open,
                    F.Operatorname, F.Grp(F.Id("eigenspace")), F.Open,
                    F.Id("J"), F.Caret, F.Grp(F.D(2)), F.Comma, F.Sp,
                    F.Operatorname, F.Grp(F.Id("cos")), F.Open,
                    F.Frac, F.Grp(F.Pi), F.Grp(F.Id("N"), F.Plus, F.D(1)),
                    F.Close, F.Caret, F.Grp(F.D(2)), F.Close, F.Close,
                    F.Sp, F.Eq, F.Sp, F.D(2)))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Substituting the paired-span characterization into its independent "
                    + "two-generator dimension theorem gives the exact dimension for every "
                    + "N at least two."))),
                DescribeRole.Theorem))));
}
