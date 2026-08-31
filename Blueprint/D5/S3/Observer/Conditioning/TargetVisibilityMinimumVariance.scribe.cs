using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Conditioning;

internal sealed class TargetVisibilityMinimumVarianceDocument
    : IScribeDocumentDefinition
{
    private const string Module =
        "D5/S3/Observer/Conditioning/TargetVisibilityMinimumVariance.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact target visibility gives the minimum-variance isotropic-noise estimator.",
        H("Target Visibility and Minimum Variance"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("target-visibility-minimum-variance"),
                DeclarationHandle.Create(Module + "target_visibility_minimum_variance"),
                H("The visible target coefficient minimizes isotropic-noise variance"),
                StatementSource.FromAuthor(MinimumVarianceFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For a linear measurement between finite-dimensional real or complex "
                            + "inner-product spaces, exact target visibility supplies the unique "
                            + "minimum-norm unbiased coefficient from the condition-cost "
                            + "theorem.")),
                    Paragraph(Text(
                        "If the observation covariance is sigma squared times the identity, the "
                            + "variance of every coefficient is sigma squared times its squared "
                            + "norm. The minimum-norm coefficient therefore also has minimum "
                            + "variance, including when sigma is zero.")),
                    Paragraph(Text(
                        "Its variance is sigma squared times the target inner product with the "
                            + "canonical visible Gram preimage, recovering the second conclusion "
                            + "of Theorem 214.2 from the existing first conclusion."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("target-visibility-is-necessary"),
                DeclarationHandle.Create(Module + "target_visibility_is_necessary"),
                H("Target visibility is necessary"),
                StatementSource.FromAuthor(VisibilityNecessaryFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For the zero real measurement and the nonzero target one, every adjoint "
                            + "coefficient is zero. Hence no unbiased coefficient exists and no "
                            + "minimum-variance certificate can be formed."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("isotropic-covariance-is-necessary"),
                DeclarationHandle.Create(Module + "isotropic_covariance_is_necessary"),
                H("Isotropic covariance is necessary"),
                StatementSource.FromAuthor(IsotropyNecessaryFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "A concrete two-coordinate real example uses measurement direction "
                            + "(1,0) and rank-one covariance in direction (1,1). The canonical "
                            + "coefficient (1,0) has positive variance, while the unbiased "
                            + "competitor (1,-1) has zero variance.")),
                    Paragraph(Text(
                        "Thus minimum Euclidean norm need not imply minimum variance once the "
                            + "covariance is not isotropic."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("degenerate-inputs-have-witnesses"),
                DeclarationHandle.Create(Module + "degenerate_inputs_have_witnesses"),
                H("Degenerate inputs still have certificates"),
                StatementSource.FromAuthor(DegenerateFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "At zero target and zero noise scale, the zero real measurement has a "
                            + "certificate. The identity measurement on the singleton "
                            + "zero-dimensional Euclidean space has one as well.")),
                    Paragraph(Text(
                        "These witnesses audit constant zero measurement, identity measurement, "
                            + "zero covariance, zero scale, and the Fin 0 index case. An empty "
                            + "carrier is impossible for a normed additive group because it "
                            + "contains zero."))),
                DescribeRole.Theorem))));

    private static Formula MinimumVarianceFormula()
    {
        Formula scalar = F.Id("K");
        Formula state = F.Id("S");
        Formula observation = F.Id("O");
        Formula measurement = F.Id("M");
        Formula target = F.Id("v");
        Formula covariance = F.Id("C");
        Formula scale = Sigma;
        Formula stateCertificate = F.Id("s");
        Formula coefficient = F.Id("a");
        Formula candidate = F.Id("b");
        Formula adjoint = Seq(measurement, Caret, Grp(Star));
        Formula visibility = Seq(
            Forall, Sp, F.Id("x"), Comma, Sp, F.Id("y"), Comma, Sp,
            Apply(measurement, F.Id("x")), Sp, Eq, Sp,
            Apply(measurement, F.Id("y")), Sp, Rightarrow, Sp,
            Inner(target, F.Id("x")), Sp, Eq, Sp, Inner(target, F.Id("y")));
        Formula isotropic = Seq(
            covariance, Sp, Eq, Sp, Square(scale), Sp, F.Id("I"));
        Formula unbiased = Seq(Apply(adjoint, coefficient), Sp, Eq, Sp, target);
        Formula minimum = Seq(
            Forall, Sp, candidate, Comma, Sp,
            Apply(adjoint, candidate), Sp, Eq, Sp, target, Sp, Rightarrow, Sp,
            Variance(covariance, coefficient), Sp, Leq, Sp,
            Variance(covariance, candidate));
        Formula cost = Seq(
            Variance(covariance, coefficient), Sp, Eq, Sp, Square(scale), Sp,
            Inner(target, stateCertificate));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, scalar, Comma, Sp, state, Comma, Sp, observation,
            Colon, Sp, F.Id("Type"), Comma, RowBreak, Grp(),
            Apply(F.Id("RCLike"), scalar), Sp, Land, Sp,
            Apply(F.Id("NormedAddCommGroup"), state), Sp, Land, Sp,
            Apply(F.Id("InnerProductSpace"), scalar, state), Sp, Land,
            RowBreak, Grp(),
            Apply(F.Id("FiniteDimensional"), scalar, state), Sp, Land, Sp,
            Apply(F.Id("NormedAddCommGroup"), observation), Sp, Land, Sp,
            Apply(F.Id("InnerProductSpace"), scalar, observation), Sp, Land,
            RowBreak, Grp(),
            Apply(F.Id("FiniteDimensional"), scalar, observation),
            Sp, Rightarrow, RowBreak, Grp(),
            measurement, Colon, Sp, state, Sp, To, Sp, observation,
            Comma, Sp, target, InMacro, Sp, state, Comma, RowBreak, Grp(),
            Open, visibility, Close, Sp, Land, Sp, Open, isotropic, Close,
            Sp, Rightarrow, RowBreak, Grp(),
            Exists, Sp, stateCertificate, InMacro, Sp, state, Comma, Sp,
            coefficient, InMacro, Sp, observation, Comma, RowBreak, Grp(),
            unbiased, Sp, Land, Sp, Open, minimum, Close, Sp, Land, Sp, cost, Dot,
            End, Grp(F.Id("gathered"))));
    }

    private static Formula VisibilityNecessaryFormula()
    {
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula zeroMap = Seq(D(0), Colon, Sp, real, Sp, To, Sp, real);
        Formula x = F.Id("x");
        Formula y = F.Id("y");
        Formula visibility = Seq(
            Forall, Sp, x, Comma, Sp, y, Comma, Sp,
            Apply(zeroMap, x), Sp, Eq, Sp, Apply(zeroMap, y), Sp,
            Rightarrow, Sp, Inner(D(1), x), Sp, Eq, Sp, Inner(D(1), y));

        return Disp(Seq(
            Neg, Sp, Open, visibility, Close, Sp, Land, Sp,
            Apply(F.Id("IsIsotropicCovariance"), zeroMap, D(0)), Sp, Land, Sp,
            Neg, Exists, Sp, F.Id("q"), InMacro, Sp, real, Sp, Times, Sp, real,
            Comma, Sp,
            Apply(F.Id("MinimumVarianceCertificate"), zeroMap, D(1), D(0), D(0),
                F.Id("q")), Dot));
    }

    private static Formula IsotropyNecessaryFormula()
    {
        Formula first = Vector(D(1), D(0));
        Formula correlated = Vector(D(1), D(1));
        Formula measurement = Seq(F.Id("span"), Open, first, Close);
        Formula covariance = Seq(
            F.Id("rankOne"), Open, correlated, Comma, Sp, correlated, Close);
        Formula x = F.Id("x");
        Formula y = F.Id("y");
        Formula visibility = Seq(
            Forall, Sp, x, Comma, Sp, y, Comma, Sp,
            Apply(measurement, x), Sp, Eq, Sp, Apply(measurement, y), Sp,
            Rightarrow, Sp, Inner(D(1), x), Sp, Eq, Sp, Inner(D(1), y));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            visibility, Sp, Land, RowBreak, Grp(),
            Neg, Sp, Apply(F.Id("IsIsotropicCovariance"), covariance, D(1)),
            Sp, Land, RowBreak, Grp(),
            Neg, Sp,
            Apply(F.Id("MinimumVarianceCertificate"), measurement, D(1), covariance,
                D(1), Seq(Open, D(1), Comma, Sp, first, Close)), Dot,
            End, Grp(F.Id("gathered"))));
    }

    private static Formula DegenerateFormula()
    {
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula zeroDimensional = Seq(
            F.Id("EuclideanSpace"), Open, real, Comma, Sp,
            F.Id("Fin"), Open, D(0), Close, Close);
        Formula realWitness = Seq(
            Exists, Sp, F.Id("q"), InMacro, Sp, real, Sp, Times, Sp, real,
            Comma, Sp,
            Apply(F.Id("MinimumVarianceCertificate"), D(0), D(0), D(0), D(0),
                F.Id("q")));
        Formula zeroDimensionalWitness = Seq(
            Exists, Sp, F.Id("q"), InMacro, Sp, zeroDimensional, Sp, Times, Sp,
            zeroDimensional, Comma, Sp,
            Apply(F.Id("MinimumVarianceCertificate"), F.Id("I"), D(0), D(0), D(0),
                F.Id("q")));

        return Disp(Seq(
            Open, realWitness, Close, Sp, Land, Sp,
            Open, zeroDimensionalWitness, Close, Dot));
    }

    private static Formula Apply(Formula function, params Formula[] arguments)
    {
        var items = new List<Formula> { function, Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }

        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula Inner(Formula left, Formula right) =>
        Seq(Langle, Sp, left, Comma, Sp, right, Sp, Rangle);

    private static Formula Square(Formula value) =>
        Seq(value, Caret, Grp(D(2)));

    private static Formula Variance(Formula covariance, Formula coefficient) =>
        Apply(F.Id("Var"), covariance, coefficient);

    private static Formula Vector(Formula first, Formula second) =>
        Seq(Open, first, Comma, Sp, second, Close);
}
