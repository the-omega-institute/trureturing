using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Tomography;

internal sealed class PurityPythagorasDecompositionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Pairwise orthogonal basis measurements split density-matrix purity excess into "
            + "visible probability energy and orthogonal residual mass.",
        H("Purity Pythagoras Decomposition"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("visible-measurements-are-orthogonal-to-the-residual"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Tomography/PurityPythagorasDecomposition."
                        + "measurement_inner_residualVector"),
                H("Every visible measurement is orthogonal to the residual"),
                StatementSource.FromAuthor(ResidualOrthogonalityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let C be a finite family of complete rank-one record measurements on "
                            + "the trace-zero Hermitian space. Assume the ranges of the "
                            + "corresponding real orthogonal projections are pairwise "
                            + "orthogonal.")),
                    Paragraph(Text(
                        "For any chosen context, projected test vector, and state, the real "
                            + "Hilbert--Schmidt inner product of that visible component with "
                            + "the state minus the sum of all visible components is zero. Thus "
                            + "the defined residual lies in the orthogonal complement of every "
                            + "visible measurement image.")),
                    Paragraph(Text(
                        "Symmetry and idempotence identify the selected context's contribution "
                            + "with its pairing against the original state, while pairwise "
                            + "orthogonality removes every cross-context contribution."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("purity-excess-splits-into-visible-and-residual-mass"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Tomography/PurityPythagorasDecomposition."
                        + "purity_pythagoras_decomposition"),
                H("Purity excess splits into visible and residual mass"),
                StatementSource.FromAuthor(PurityDecompositionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let rho be a positive semidefinite complex matrix of trace one in "
                            + "dimension d. Centering it by the maximally mixed state produces "
                            + "a trace-zero Hermitian vector whose squared Hilbert--Schmidt norm "
                            + "is the real trace purity minus the inverse dimension.")),
                    Paragraph(Text(
                        "For each complete rank-one record context, the squared norm of its "
                            + "visible projection is the sum over outcomes of the squared Born "
                            + "probability deviations from the uniform value. Pairwise "
                            + "orthogonality makes these visible energies add without cross "
                            + "terms.")),
                    Paragraph(Text(
                        "The preceding residual-orthogonality result then gives an exact "
                            + "Pythagorean split: purity excess equals the double sum of visible "
                            + "probability energies plus the squared norm of the remaining "
                            + "component. The family need not be tomographically complete; any "
                            + "unseen mass is retained by the nonnegative residual term."))),
                DescribeRole.Theorem))));

    private static Formula ResidualOrthogonalityFormula()
    {
        Formula dimension = F.Id("d");
        Formula family = F.Id("C");
        Formula index = F.Id("l");
        Formula test = F.Id("x");
        Formula state = F.Id("s");
        Formula context = Call("context", family, index);
        Formula projection = Call("traceZeroBasisMeasurement", context, test);
        Formula residual = Call("residualVector", family, state);

        return Disp(Seq(
            Call("RankOneContextFamily", family, dimension), Sp, Land, Sp,
            Call("RecordMeasurements", family), Sp, Land, Sp,
            Call("PairwiseOrthogonalMeasurements", family), Sp, Rightarrow, RowBreak, Grp(),
            Forall, Sp, index, Comma, Sp,
            test, Comma, Sp, state, Colon, Sp,
            Call("traceZeroHermitian", dimension), Comma, Sp,
            Call("innerR", projection, residual), Sp, Eq, Sp, D(0), Dot));
    }

    private static Formula PurityDecompositionFormula()
    {
        Formula dimension = F.Id("d");
        Formula family = F.Id("C");
        Formula index = F.Id("l");
        Formula outcome = F.Id("j");
        Formula rho = Rho;
        Formula inverseDimension = new Formula.Fraction(D(1), dimension);
        Formula probability = Call(
            "basisProbability", rho, Call("context", family, index), outcome);
        Formula squaredDeviation = Seq(
            Grp(probability, Sp, Minus, Sp, inverseDimension), Caret, Grp(D(2)));
        Formula centeredState = Call("centeredDensity", rho);

        return Disp(Seq(
            Call("NormalizedDensity", rho, dimension), Sp, Land, Sp,
            Call("RecordMeasurements", family), Sp, Land, Sp,
            Call("PairwiseOrthogonalMeasurements", family), Sp, Rightarrow, RowBreak, Grp(),
            Call("ReTr", Seq(rho, Caret, Grp(D(2)))), Sp, Minus, Sp,
            inverseDimension, Sp, Eq, RowBreak, Grp(),
            Sum, Underscore, Grp(index), Sp,
            Sum, Underscore, Grp(outcome), Sp,
            squaredDeviation, Sp, Plus, Sp,
            Call("purityResidual", family, centeredState), Dot));
    }
}
