using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Tomography;

internal sealed class ComplementaryContextProbabilityPythagorasDocument
    : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Orthogonal context coordinates split matrix purity excess into observed probability "
            + "deviations and complementary residual mass.",
        H("Complementary Context Probability Pythagoras"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("probability-deviations-and-residual-mass-split-purity"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Tomography/ComplementaryContextProbabilityPythagoras."
                        + "complementary_context_probability_pythagoras"),
                H("Probability deviations and residual mass split purity"),
                StatementSource.FromAuthor(PythagorasFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let rho be a finite complex matrix, let its centered Hermitian part be "
                            + "represented by a vector in a real Hilbert space, let p(l,j) be "
                            + "real probability coordinates, and let S be the visible coordinate "
                            + "subspace. Assume the squared norm of the centered state is the "
                            + "real trace purity excess and the squared "
                            + "norm of its projection to S is the double sum of squared centered "
                            + "probabilities.")),
                    Paragraph(Text(
                        "The residual mass is defined as the squared norm of the projection to "
                            + "the orthogonal complement of S. Mathlib's exact orthogonal-"
                            + "projection Pythagoras theorem then gives the displayed equality "
                            + "without expanding matrix entries.")),
                    Paragraph(Text(
                        "For pairwise mutually unbiased basis contexts, the two bridge "
                            + "assumptions are precisely the preceding centered-state and "
                            + "orthogonal-coordinate calculations. The result retains every "
                            + "context and outcome in the double sum; it does not specialize the "
                            + "identity to a single basis or a fixed matrix dimension."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments)
    {
        var content = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0)
            {
                content.Add(Comma);
                content.Add(Sp);
            }
            content.Add(arguments[index]);
        }
        content.Add(Close);
        return Seq([.. content]);
    }

    private static Formula PythagorasFormula()
    {
        Formula rho = Rho;
        Formula dimension = F.Id("d");
        Formula context = F.Id("l");
        Formula outcome = F.Id("j");
        Formula probability = Seq(F.Id("p"), Underscore, Grp(context, outcome));
        Formula inverseDimension = Seq(Frac, Grp(D(1)), Grp(dimension));
        Formula squaredDeviation = Seq(
            Grp(probability, Minus, inverseDimension), Caret, Grp(D(2)));
        Formula residual = Seq(F.Id("r"), Underscore, F.Id("S"),
            Caret, Grp(D(2)), Open, rho, Close);

        return Disp(Seq(
            Call("ProjectionCoordinates", rho, F.Id("p"), F.Id("S")), Sp,
            Rightarrow, RowBreak,
            Operatorname, Grp(F.Id("ReTr")), Open, rho, Caret, Grp(D(2)), Close,
            Sp, Minus, Sp, inverseDimension, Sp, Eq, RowBreak,
            Sum, Underscore, Grp(context), Sp,
            Sum, Underscore, Grp(outcome), Sp, squaredDeviation, Sp,
            Plus, Sp, residual, Dot));
    }
}
