using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.SpectralTopology;

internal sealed class LocalPositiveSquareCompletionDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/SpectralTopology/LocalPositiveSquareCompletion.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An observer outside a finite real spectrum gives a positive inverse-square determinant completion.",
        H("Local Positive-Square Completion"),
        Blocks(
            Definition(
                "shifted-inverse-square-eigenvalue",
                "shiftedInverseSquareEigenvalue",
                "Shifted inverse-square eigenvalue",
                "The weight at spectral value h(j) is the reciprocal of the square of h(j) minus the observer coordinate."),
            Definition(
                "local-positive-square",
                "localPositiveSquare",
                "Local positive square",
                "The local completion is the diagonal complex matrix formed from the shifted inverse-square weights."),
            Describe.Lean(
                DescribeId.Create("local-positive-square-completion"),
                DeclarationHandle.Create(Prefix + "local_positive_square_completion"),
                H("Off-spectrum shifts give positive determinant completions"),
                StatementSource.FromAuthor(CompletionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let h list the finite real spectrum and let a avoid every spectral value. Each difference h(j)-a is nonzero, so its squared reciprocal is strictly positive. The diagonal matrix A formed from these weights is therefore positive definite.")),
                    Paragraph(Text(
                        "Mathlib's diagonal determinant identity gives the displayed factorization of det(I+wA). If the determinant vanishes, one positive factor weight forces w to be its negative reciprocal; hence every zero is real and strictly negative.")),
                    Paragraph(Text(
                        "The off-spectrum premise is essential. The companion collision theorem records that Lean's total inverse sends a zero spectral difference to zero rather than to a positive weight."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("spectral-collision-collapses-inverse-square"),
                DeclarationHandle.Create(
                    Prefix + "spectral_collision_collapses_inverse_square"),
                H("A spectral collision collapses the inverse-square weight"),
                StatementSource.FromAuthor(CollisionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For a one-point spectrum equal to the observer coordinate, the shifted difference is zero and the totalized real inverse-square weight is exactly zero. This is the concrete degeneracy excluded by the main theorem."))),
                DescribeRole.Theorem)),
        []));

    private static DocumentBlock.Describe Definition(
        string id, string declaration, string heading, string paragraph) =>
        Describe.Lean(
            DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration),
            H(heading),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(paragraph))),
            DescribeRole.Definition);

    private static Formula CompletionFormula()
    {
        Formula rank = F.Id("r");
        Formula spectrum = F.Id("h");
        Formula observer = F.Id("a");
        Formula index = F.Id("j");
        Formula argument = F.Id("w");
        Formula matrix = F.Id("A");
        Formula naturals = F.Seq(F.Mathbb, F.Grp(F.Id("N")));
        Formula reals = F.Seq(F.Mathbb, F.Grp(F.Id("R")));
        Formula complexes = F.Seq(F.Mathbb, F.Grp(F.Id("C")));
        Formula finiteIndex = Call(F.Id("Fin"), rank);
        Formula spectrumAt = Call(spectrum, index);
        Formula eigenvalueAt = Call(F.Id("lambda"), index);
        Formula determinant = Call(
            F.Id("det"),
            F.Seq(F.D(1), F.Sp, F.Plus, F.Sp,
                argument, F.Sp, F.Cdot, F.Sp, matrix));
        Formula factor = F.Grp(F.Seq(
            F.D(1), F.Sp, F.Plus, F.Sp,
            argument, F.Sp, F.Cdot, F.Sp, eigenvalueAt));
        Formula product = F.Seq(
            F.Prod, F.Underscore,
            F.Grp(index, F.InMacro, F.Sp, finiteIndex), F.Sp, factor);
        Formula offSpectrum = F.Seq(
            F.Forall, F.Sp, index, F.InMacro, F.Sp, finiteIndex,
            F.Comma, F.Sp, spectrumAt, F.Sp, F.Neq, F.Sp, observer);
        Formula positiveWeights = F.Seq(
            F.Forall, F.Sp, index, F.InMacro, F.Sp, finiteIndex,
            F.Comma, F.Sp, F.D(0), F.Sp, F.Lt, F.Sp, eigenvalueAt);
        Formula factorization = F.Seq(
            F.Forall, F.Sp, argument, F.InMacro, F.Sp, complexes,
            F.Comma, F.Sp, determinant, F.Sp, F.Eq, F.Sp, product);
        Formula zeroLocus = F.Seq(
            F.Forall, F.Sp, argument, F.InMacro, F.Sp, complexes,
            F.Comma, F.Sp,
            determinant, F.Sp, F.Eq, F.Sp, F.D(0),
            F.Sp, F.Rightarrow, F.Sp,
            F.Grp(F.Seq(
                Call(F.Id("Im"), argument), F.Sp, F.Eq, F.Sp, F.D(0),
                F.Sp, F.Land, F.Sp,
                Call(F.Id("Re"), argument), F.Sp, F.Lt, F.Sp, F.D(0))));

        return F.Disp(F.Seq(
            F.Forall, F.Sp,
            rank, F.InMacro, F.Sp, naturals,
            F.Comma, F.Sp,
            spectrum, F.Colon, F.Sp, finiteIndex, F.Sp, F.To, F.Sp, reals,
            F.Comma, F.Sp,
            observer, F.InMacro, F.Sp, reals,
            F.Comma, F.Sp, RowBreak, F.Grp(),
            F.Grp(offSpectrum), F.Sp, F.Rightarrow, F.Sp, RowBreak, F.Grp(),
            F.Grp(F.Seq(
                F.Grp(positiveWeights), F.Sp, F.Land, F.Sp,
                Call(F.Id("PosDef"), matrix), F.Sp, F.Land, F.Sp,
                F.Grp(factorization), F.Sp, F.Land, F.Sp,
                F.Grp(zeroLocus))), F.Dot));
    }

    private static Formula CollisionFormula() => F.Disp(F.Seq(
        F.Forall, F.Sp, F.Id("a"), F.InMacro, F.Sp,
        F.Seq(F.Mathbb, F.Grp(F.Id("R"))),
        F.Comma, F.Sp,
        Call(F.Id("lambda"), F.Id("a"), F.Id("a")),
        F.Sp, F.Eq, F.Sp, F.D(0), F.Dot));

    private static Formula Call(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);
}
