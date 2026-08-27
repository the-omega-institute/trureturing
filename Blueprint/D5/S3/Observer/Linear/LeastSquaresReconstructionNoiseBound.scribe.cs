using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Linear;

internal sealed class LeastSquaresReconstructionNoiseBoundDocument
    : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Full-column-rank least-squares reconstruction is stable under additive noise.",
        H("Least-Squares Reconstruction Noise Bound"),
        Blocks(Describe.Lean(
            DescribeId.Create("least-squares-reconstruction-noise-bound"),
            DeclarationHandle.Create(
                "D5/S3/Observer/Linear/LeastSquaresReconstructionNoiseBound."
                    + "least_squares_reconstruction_noise_bound"),
            H("A lower frame bound controls reconstruction error"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The measurement operator is defined on arbitrary finite-dimensional "
                        + "real inner-product spaces. A positive lower frame bound makes it "
                        + "injective and supplies the smallest-singular-value scale.")),
                Paragraph(Text(
                    "The reconstructed state is characterized publicly by the exact "
                        + "least-squares normal equation. Under the lower frame premise this "
                        + "is the full-column-rank Moore--Penrose reconstruction.")),
                Paragraph(Text(
                    "Normal-equation orthogonality bounds the measured reconstruction error "
                        + "by the noise norm. The lower frame inequality then gives the sharp "
                        + "inverse-square-root stability factor."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula state = F.Id("State");
        Formula observation = F.Id("Observation");
        Formula measurement = F.Id("measurement");
        Formula alpha = Alpha;
        Formula difference = F.Id("difference");
        Formula trueState = F.Id("trueState");
        Formula reconstructed = F.Id("reconstructed");
        Formula data = F.Id("data");
        Formula noise = F.Id("noise");
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula measurementType = Call("LinearMap", real, state, observation);
        Formula differenceNormSq = Seq(
            new Formula.Norm(difference), Caret, Grp(D(2)));
        Formula measuredDifferenceNormSq = Seq(
            new Formula.Norm(Call(measurement, difference)), Caret, Grp(D(2)));
        Formula lowerFrame = Seq(
            Forall, Sp, Typed(difference, state), Comma, Sp,
            alpha, Sp, differenceNormSq, Sp, Leq, Sp, measuredDifferenceNormSq);
        Formula observationModel = Seq(
            data, Sp, Eq, Sp, Call(measurement, trueState), Sp, Plus, Sp, noise);
        Formula normalEquation = Seq(
            Call("adjoint", measurement), Open,
            Call(measurement, reconstructed), Sp, Minus, Sp, data, Close,
            Sp, Eq, Sp, D(0));
        Formula reconstructionBound = Seq(
            new Formula.Norm(Seq(reconstructed, Sp, Minus, Sp, trueState)),
            Sp, Leq, Sp,
            Frac, Grp(new Formula.Norm(noise)), Grp(Sqrt, Grp(alpha)), Dot);

        return Disp(new Formula.Aligned([
            Seq(
                Forall, Sp, Typed(Seq(state, Comma, Sp, observation), type), Comma),
            Seq(
                Grp(), Typeclass("NormedAddCommGroup", state), Comma, Sp,
                Typeclass("InnerProductSpace", real, state), Comma, Sp,
                Typeclass("FiniteDimensional", real, state), Comma),
            Seq(
                Grp(), Typeclass("NormedAddCommGroup", observation), Comma, Sp,
                Typeclass("InnerProductSpace", real, observation), Comma, Sp,
                Typeclass("FiniteDimensional", real, observation), Comma),
            Seq(
                Forall, Sp, Typed(measurement, measurementType), Comma, Sp,
                Typed(alpha, real), Comma),
            Seq(
                Grp(), D(0), Sp, Lt, Sp, alpha, Sp, Rightarrow),
            Seq(
                Grp(), lowerFrame, Sp, Rightarrow),
            Seq(
                Grp(), Forall, Sp,
                Typed(Seq(trueState, Comma, Sp, reconstructed), state), Comma, Sp,
                Typed(Seq(data, Comma, Sp, noise), observation), Comma),
            Seq(
                Grp(), observationModel, Sp, Rightarrow),
            Seq(
                Grp(), normalEquation, Sp, Rightarrow),
            Seq(
                Grp(), reconstructionBound),
        ]));
    }

    private static Formula Typed(Formula value, Formula type) =>
        Seq(value, Colon, Sp, type);

    private static Formula Typeclass(string name, params Formula[] arguments) =>
        Seq(OpenBracket, Call(name, arguments), CloseBracket);

    private static Formula Call(Formula name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(name), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }

        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula Call(string name, params Formula[] arguments) =>
        Call(F.Id(name), arguments);
}
