using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Resource.LogDet;

internal sealed class LogDetInformationSubmodularityDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Resource/LogDet/LogDetInformationSubmodularity.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Positive matrix contributions make regularized log-determinant information submodular.",
        H("Log-Determinant Information Submodularity"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("information-operator"),
                DeclarationHandle.Create(Prefix + "informationOperator"),
                H("Regularized information operator"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The operator is constructed as lambda times the identity plus the finite "
                        + "sum of the selected protocol contributions."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("log-volume-information"),
                DeclarationHandle.Create(Prefix + "logVolumeInformation"),
                H("Log-volume information"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The selected operator's real log-determinant is normalized by the "
                        + "regularization-only baseline."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("log-det-information-monotone-submodular"),
                DeclarationHandle.Create(Prefix + "log_det_information_monotone_submodular"),
                H("Log-determinant information is monotone and submodular"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For arbitrary positive semidefinite complex matrix contributions and "
                            + "a positive scalar regularizer, enlarging a finite protocol set "
                            + "cannot decrease its log-volume information.")),
                    Paragraph(Text(
                        "The marginal gain from adjoining one protocol decreases when the "
                            + "starting set grows. The statement includes protocols already in "
                            + "the larger set, where the corresponding gain is zero.")),
                    Paragraph(Text(
                        "The proof bundles the raw matrix C-star components locally, applies "
                            + "operator monotonicity of the logarithm and inverse antitonicity, "
                            + "and identifies trace-log with real log-determinant spectrally."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }
        items.Add(Close);
        return Seq([.. items]);
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

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula And(params Formula[] formulas)
    {
        Formula result = formulas[^1];
        for (var index = formulas.Length - 2; index >= 0; index--)
            result = new Formula.Logic(formulas[index], FormulaLogicOperator.And, result);
        return result;
    }

    private static Formula TheoremFormula()
    {
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula complex = Seq(Mathbb, Grp(F.Id("C")));
        Formula protocolType = F.Id("Protocol");
        Formula indexType = F.Id("Index");
        Formula contribution = F.Id("G");
        Formula regularizer = F.Id("lambda");
        Formula protocol = F.Id("p");
        Formula smaller = F.Id("A");
        Formula larger = F.Id("B");
        Formula matrix = Call("Matrix", indexType, indexType, complex);
        Formula selection = Call("Finset", protocolType);
        Formula volume(Formula selected) =>
            Call("logVolumeInformation", contribution, regularizer, selected);
        Formula marginal(Formula selected) => Seq(
            volume(Call("insert", protocol, selected)), Sp, Minus, Sp, volume(selected));

        Formula contributionNonnegative = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("p", protocolType)],
            Call("PosSemidef", Apply(contribution, protocol)));
        Formula premises = And(
            Call("DecidableEq", protocolType),
            Call("Fintype", indexType),
            Call("DecidableEq", indexType),
            Seq(D(0), Sp, Lt, Sp, regularizer),
            contributionNonnegative);
        Formula monotonicity = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("A", selection), Bound("B", selection)],
            new Formula.Logic(
                Seq(smaller, Sp, Subseteq, Sp, larger),
                FormulaLogicOperator.Implies,
                Seq(volume(smaller), Sp, Leq, Sp, volume(larger))));
        Formula diminishingReturns = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("A", selection), Bound("B", selection), Bound("p", protocolType)],
            new Formula.Logic(
                Seq(smaller, Sp, Subseteq, Sp, larger),
                FormulaLogicOperator.Implies,
                Seq(marginal(smaller), Sp, Geq, Sp, marginal(larger))));

        return Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                Bound("Protocol", type),
                Bound("Index", type),
                Bound("G", Arrow(protocolType, matrix)),
                Bound("lambda", real),
            ],
            new Formula.Logic(
                premises,
                FormulaLogicOperator.Implies,
                new Formula.Logic(
                    monotonicity,
                    FormulaLogicOperator.And,
                    diminishingReturns))));
    }
}
