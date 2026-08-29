using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Budget;

internal sealed class CaratheodoryScaleCovarianceDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Weil/Budget/CaratheodoryScaleCovariance.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Even resolvent spectra give covariant Caratheodory functions and budgets.",
        H("Caratheodory Scale Covariance"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("caratheodory-kernel"),
                DeclarationHandle.Create(Prefix + "caratheodoryKernel"),
                H("Caratheodory kernel"),
                StatementSource.FromAuthor(KernelFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The kernel is constructed directly from the two complex variables."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("caratheodory-function"),
                DeclarationHandle.Create(Prefix + "caratheodoryFunction"),
                H("Caratheodory function"),
                StatementSource.FromAuthor(FunctionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The function integrates the kernel against the imported Cayley "
                        + "spectral measure."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("observer-scale-parameter"),
                DeclarationHandle.Create(Prefix + "observerScaleParameter"),
                H("Observer scale parameter"),
                StatementSource.FromAuthor(ScaleParameterFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "This parameter is the observer-side sign convention for the real "
                        + "disk automorphism."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("resolvent-budget"),
                DeclarationHandle.Create(Prefix + "resolventBudget"),
                H("Resolvent budget"),
                StatementSource.FromAuthor(BudgetFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The budget is the real total mass of the resolvent-weighted source "
                        + "measure."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("caratheodory-scale-covariance"),
                DeclarationHandle.Create(Prefix + "caratheodory_scale_covariance"),
                H("Caratheodory scale covariance"),
                StatementSource.FromAuthor(CovarianceFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Evenness cancels the imaginary normalization term after pairing the "
                        + "positive and negative spectral points. Evaluating the same law at "
                        + "zero gives the budget specialization."))),
                DescribeRole.Theorem))));

    private static Formula KernelFormula()
    {
        Formula z = F.Id("z");
        Formula w = F.Id("w");
        return Disp(Seq(
            Forall, Sp, z, Comma, Sp, w, Colon, Sp, ComplexType(), Comma, Sp,
            Kernel(z, w), Sp, Eq, Sp,
            Fraction(
                Seq(z, Sp, Plus, Sp, w),
                Seq(z, Sp, Minus, Sp, w)), Dot));
    }

    private static Formula FunctionFormula()
    {
        Formula source = F.Id("nu");
        Formula scale = F.Id("a");
        Formula w = F.Id("w");
        Formula z = F.Id("z");
        return Disp(Seq(
            Forall, Sp, source, Colon, Sp, MeasureType(RealType()), Comma, Sp,
            scale, Colon, Sp, RealType(), Comma, Sp,
            w, Colon, Sp, ComplexType(), Comma, Sp,
            Caratheodory(scale, source, w), Sp, Eq, Sp,
            Call("integral", SpectralMeasure(scale, source),
                Seq(z, Sp, Mapsto, Sp, Kernel(z, w))), Dot));
    }

    private static Formula ScaleParameterFormula()
    {
        Formula a = F.Id("a");
        Formula b = F.Id("b");
        return Disp(Seq(
            Forall, Sp, a, Comma, Sp, b, Colon, Sp, RealType(), Comma, Sp,
            ScaleParameter(a, b), Sp, Eq, Sp,
            Fraction(
                Seq(b, Sp, Minus, Sp, a),
                Seq(a, Sp, Plus, Sp, b)), Dot));
    }

    private static Formula BudgetFormula()
    {
        Formula source = F.Id("nu");
        Formula scale = F.Id("a");
        return Disp(Seq(
            Forall, Sp, source, Colon, Sp, MeasureType(RealType()), Comma, Sp,
            scale, Colon, Sp, RealType(), Comma, Sp,
            Budget(scale, source), Sp, Eq, Sp,
            Call("toReal", Call("mass", WeightedMeasure(scale, source))), Dot));
    }

    private static Formula CovarianceFormula()
    {
        Formula source = F.Id("nu");
        Formula a = F.Id("a");
        Formula b = F.Id("b");
        Formula w = F.Id("w");
        Formula x = F.Id("x");
        Formula ratio = Call("ofReal", Fraction(a, b));
        Formula transformed = DiskAutomorphism(ScaleParameter(a, b), w);
        Formula evenness = Seq(
            Call("map", Seq(x, Sp, Mapsto, Sp, Minus, Sp, x), source),
            Sp, Eq, Sp, source);
        Formula hypotheses = Seq(
            D(0), Sp, Lt, Sp, a, Sp, Land, Sp,
            D(0), Sp, Lt, Sp, b, Sp, Land, Sp,
            evenness, Sp, Land, RowBreak, Grp(),
            Call("FiniteMeasure", WeightedMeasure(a, source)), Sp, Land, Sp,
            Call("FiniteMeasure", WeightedMeasure(b, source)), Sp, Land, Sp,
            new Formula.Norm(w), Sp, Lt, Sp, D(1));
        Formula covariance = Seq(
            Caratheodory(b, source, w), Sp, Eq, Sp,
            ratio, Sp, Cdot, Sp, Caratheodory(a, source, transformed));
        Formula budget = Seq(
            Call("ofReal", Budget(b, source)), Sp, Eq, Sp,
            ratio, Sp, Cdot, Sp,
            Caratheodory(a, source, Call("ofReal", ScaleParameter(a, b))));
        return Disp(Seq(
            Forall, Sp, source, Colon, Sp, MeasureType(RealType()), Comma, Sp,
            a, Comma, Sp, b, Colon, Sp, RealType(), Comma, Sp,
            w, Colon, Sp, ComplexType(), Comma, RowBreak, Grp(),
            hypotheses, Sp, Rightarrow, RowBreak, Grp(),
            Grp(covariance), Sp, Land, RowBreak, Grp(), Grp(budget), Dot));
    }

    private static Formula Kernel(Formula z, Formula w) => Call("K", z, w);

    private static Formula Caratheodory(
        Formula scale,
        Formula source,
        Formula w) => Apply(new Formula.Subscript(F.Id("F"), scale), source, w);

    private static Formula ScaleParameter(Formula a, Formula b) =>
        new Formula.Subscript(F.Id("s"), Seq(a, Comma, b));

    private static Formula Budget(Formula scale, Formula source) =>
        Apply(new Formula.Subscript(F.Id("R"), scale), source);

    private static Formula WeightedMeasure(Formula scale, Formula source) =>
        Apply(new Formula.Subscript(F.Id("W"), scale), source);

    private static Formula SpectralMeasure(Formula scale, Formula source) =>
        Apply(new Formula.Subscript(F.Id("mu"), scale), source);

    private static Formula DiskAutomorphism(Formula parameter, Formula w) =>
        Apply(new Formula.Subscript(F.Id("Phi"), parameter), w);

    private static Formula RealType() => Seq(Mathbb, Grp(F.Id("R")));

    private static Formula ComplexType() => Seq(Mathbb, Grp(F.Id("C")));

    private static Formula MeasureType(Formula carrier) => Call("Measure", carrier);

    private static Formula Fraction(Formula numerator, Formula denominator) =>
        Seq(Frac, Grp(numerator), Grp(denominator));

    private static Formula Apply(Formula function, params Formula[] arguments)
    {
        var items = new List<Formula> { function, Open };
        for (int i = 0; i < arguments.Length; i++)
        {
            if (i > 0)
            {
                items.Add(Comma);
                items.Add(Sp);
            }

            items.Add(arguments[i]);
        }

        items.Add(Close);
        return Seq(items.ToArray());
    }
}
