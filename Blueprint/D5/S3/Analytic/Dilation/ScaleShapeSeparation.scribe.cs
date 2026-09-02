using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Dilation;

internal sealed class ScaleShapeSeparationDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Analytic/Dilation/ScaleShapeSeparation.scale_shape_separation";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Positive overall scaling preserves spectral-zeta zeros; only shape can change them.",
        H("Scale-Shape Separation"),
        Blocks(Describe.Lean(
            DescribeId.Create("positive-spectral-scale-shape-separation"),
            DeclarationHandle.Create(Declaration),
            H("Overall scale does not move spectral-zeta zeros"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "A positive spectrum is represented by a positive real sequence lambda. "
                        + "Its overall scale a produces the spectrum n maps to a lambda(n), "
                        + "and its raw Dirichlet zero set contains exactly those complex s where "
                        + "the spectral terms are summable and spectralZeta(lambda,s) vanishes.")),
                Paragraph(Text(
                    "The first conjunct identifies the zero set after positive scaling with "
                        + "the original zero set. The second conjunct states the corresponding "
                        + "only-if direction: if two positively scaled spectra have different "
                        + "zero sets, their dimensionless shape sequences are different.")),
                Paragraph(Text(
                    "The factorization Z_(a lambda)(s)=a^(-s) Z_lambda(s) follows termwise "
                        + "from complex powers. Positivity makes the scale factor nonzero, so it "
                        + "preserves both summability of the terms and vanishing of their sum."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula natural = Seq(Mathbb, Grp(F.Id("N")));
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula a = F.Id("a"), b = F.Id("b"), n = F.Id("n");
        Formula lambda = F.Id("lambda"), mu = F.Id("mu");
        Formula shapeType = Seq(natural, To, real);
        Formula scaledA = Call("scaleSpectrum", a, lambda);
        Formula scaledB = Call("scaleSpectrum", b, mu);
        Formula zerosScaledA = Call("spectralZeroSet", scaledA);
        Formula zerosLambda = Call("spectralZeroSet", lambda);
        Formula zerosScaledB = Call("spectralZeroSet", scaledB);
        Formula lambdaPositive = Seq(
            Forall, Sp, Typed(n, natural), Comma, Sp,
            D(0), Sp, Lt, Sp, Apply(lambda, n));
        Formula muPositive = Seq(
            Forall, Sp, Typed(n, natural), Comma, Sp,
            D(0), Sp, Lt, Sp, Apply(mu, n));
        Formula scaleInvariant = Equal(zerosScaledA, zerosLambda);
        Formula shapeNecessary = Seq(
            Forall, Sp, Typed(b, real), Comma, Sp,
            D(0), Sp, Lt, Sp, b, Sp, Rightarrow, Sp,
            Forall, Sp, Typed(mu, shapeType), Comma, Sp,
            Open, muPositive, Close, Sp, Rightarrow, Sp,
            NotEqual(zerosScaledA, zerosScaledB), Sp, Rightarrow, Sp,
            NotEqual(lambda, mu));

        return Disp(new Formula.Aligned([
            Seq(Forall, Sp, Typed(a, real), Comma, Sp,
                D(0), Sp, Lt, Sp, a, Sp, Rightarrow),
            Seq(Forall, Sp, Typed(lambda, shapeType), Comma, Sp,
                Open, lambdaPositive, Close, Sp, Rightarrow),
            Seq(Grp(), scaleInvariant, Sp, Land),
            Seq(Grp(), shapeNecessary, Dot),
        ]));
    }

    private static Formula Typed(Formula value, Formula type) =>
        Seq(value, Colon, Sp, type);

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula NotEqual(Formula left, Formula right) =>
        new Formula.Not(Equal(left, right));
}
