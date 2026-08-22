using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Tomography;

internal sealed class ResidualControlsNaturalityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Orthogonal residual norms control visible compression defects.",
        H("Residual Control of Visible Compression"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("centered-density-coordinate"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Tomography/ResidualControlsNaturality.densityCoordinate"),
                H("Centered density coordinate"),
                StatementSource.FromAuthor(DensityCoordinateFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A positive semidefinite trace-one matrix is centered at the maximally "
                        + "mixed matrix. Hermiticity and trace normalization place the result "
                        + "in the canonical real trace-zero Hermitian carrier."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("visible-compressed-dynamics"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Tomography/ResidualControlsNaturality.visibleDynamics"),
                H("Visible compressed dynamics"),
                StatementSource.FromAuthor(VisibleDynamicsFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The visible dynamics is constructed from the ambient map and the named "
                        + "orthogonal projection: apply the ambient dynamics, then project its "
                        + "output back to the visible subspace."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("orthogonal-residual-controls-naturality-defect"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Tomography/ResidualControlsNaturality."
                        + "residual_controls_naturality"),
                H("Orthogonal residual controls the visible compression defect"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let S be a closed subspace of the real trace-zero Hermitian carrier, "
                            + "let F be L-Lipschitz, and let its visible dynamics be the "
                            + "orthogonal compression constructed above.")),
                    Paragraph(Text(
                        "The public statement contains both source clauses. For every named "
                            + "coordinate X, the compression defect is at most L times the norm "
                            + "of its orthogonal residual. For the centered density coordinate, "
                            + "the same defect is at most L times the square root of the canonical "
                            + "residual mass.")),
                    Paragraph(Text(
                        "Mathlib's exact nonexpansiveness theorem for orthogonal projection is "
                            + "composed with the Lipschitz bound for F. Its orthogonal-complement "
                            + "identity identifies the input distance, and the real square-root "
                            + "identity converts the squared residual mass back to its norm."))),
                DescribeRole.Theorem))));

    private static Formula Carrier(Formula dimension) =>
        Call("HermitianTraceZero", dimension);

    private static Formula MatrixType(Formula dimension) =>
        Call("Matrix", dimension, dimension, Seq(Mathbb, Grp(F.Id("C"))));

    private static Formula ProjectionMap(Formula visible) =>
        Seq(F.Id("P"), Underscore, Grp(visible));

    private static Formula Apply(Formula function, Formula value) =>
        Seq(function, Open, value, Close);

    private static Formula Projection(Formula visible, Formula value) =>
        Apply(ProjectionMap(visible), value);

    private static Formula ResidualProjection(Formula visible, Formula value) =>
        Seq(F.Id("P"), Underscore, Grp(Seq(visible, Caret, Grp(Perp))), Open,
            value, Close);

    private static Formula CompressionDefect(
        Formula visible, Formula dynamics, Formula value) =>
        Call("naturalityDefect", ProjectionMap(visible), ProjectionMap(visible),
            dynamics, Call("visibleDynamics", visible, dynamics), value);

    private static Formula DensityCoordinateFormula()
    {
        Formula d = F.Id("d");
        Formula density = Call("Density", Rho);
        Formula centered = Seq(
            Rho, Sp, Minus, Sp, Frac, Grp(D(1)), Grp(d), Sp, F.Id("I"));

        return Disp(Seq(
            Forall, Sp, d, Comma, Sp, Rho, Colon, Sp, MatrixType(d), Comma,
            RowBreak, Grp(), density, Sp, Rightarrow, Sp,
            Call("densityCoordinate", Rho), Sp, Eq, Sp, centered, Sp,
            InMacro, Sp, Carrier(d), Dot));
    }

    private static Formula VisibleDynamicsFormula()
    {
        Formula d = F.Id("d");
        Formula visible = F.Id("S");
        Formula dynamics = F.Id("F");
        Formula x = F.Id("X");
        Formula carrier = Carrier(d);

        return Disp(Seq(
            Forall, Sp, d, Comma, Sp, visible, Colon, Sp,
            Call("Submodule", Seq(Mathbb, Grp(F.Id("R"))), carrier), Comma,
            RowBreak, Grp(), dynamics, Colon, Sp,
            new Formula.TypeArrow(carrier, carrier), Comma, Sp,
            x, Colon, Sp, carrier, Comma, RowBreak, Grp(),
            Call("visibleDynamics", visible, dynamics), Open, x, Close,
            Sp, Eq, Sp, Projection(visible, Apply(dynamics, x)), Dot));
    }

    private static Formula TheoremFormula()
    {
        Formula d = F.Id("d");
        Formula visible = F.Id("S");
        Formula dynamics = F.Id("F");
        Formula lipschitz = F.Id("L");
        Formula x = F.Id("X");
        Formula carrier = Carrier(d);
        Formula xRho = Call("densityCoordinate", Rho);
        Formula defectX = CompressionDefect(visible, dynamics, x);
        Formula defectRho = CompressionDefect(visible, dynamics, xRho);
        Formula residualNorm = new Formula.Norm(ResidualProjection(visible, x));
        Formula residualMass = Call("residualMass", visible, xRho);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, d, Comma, Sp, Rho, Colon, Sp, MatrixType(d), Comma,
            RowBreak, Grp(), visible, Colon, Sp,
            Call("Submodule", Seq(Mathbb, Grp(F.Id("R"))), carrier), Comma, Sp,
            dynamics, Colon, Sp, new Formula.TypeArrow(carrier, carrier), Comma,
            RowBreak, Grp(), lipschitz, Colon, Sp,
            Operatorname, Grp(F.Id("NNReal")), Comma, Sp,
            x, Colon, Sp, carrier, Comma, RowBreak, Grp(),
            Call("Density", Rho), Sp, Land, Sp, Call("IsClosed", visible), Sp,
            Land, Sp, Call("LipschitzWith", lipschitz, dynamics), Sp,
            Rightarrow, RowBreak, Grp(),
            defectX, Sp, Leq, Sp, lipschitz, Sp, residualNorm, Sp,
            Land, RowBreak, Grp(),
            defectRho, Sp, Leq, Sp, lipschitz, Sp, Sqrt, Grp(residualMass), Dot,
            End, Grp(F.Id("gathered"))));
    }
}
