using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.PrimeProducts;

internal sealed class GeometricResidualMemorylessnessDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Analytic/PrimeProducts/GeometricResidualMemorylessness."
            + "geometric_residual_memoryless";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Conditioning a geometric law on a tail preserves its translated residual law.",
        H("Geometric Residual Memorylessness"),
        Blocks(Describe.Lean(
            DescribeId.Create("geometric-residual-memorylessness"),
            DeclarationHandle.Create(Declaration),
            H("A geometric tail has the original residual law"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Let success be a nondegenerate parameter in the unit interval. Mathlib's "
                        + "canonical zero-start geometric measure assigns mass proportional to "
                        + "one minus success raised to the sampled natural value.")),
                Paragraph(Text(
                    "For every natural threshold k, condition this measure on the tail event "
                        + "that the sampled value is at least k, then push the conditional law "
                        + "forward by natural subtraction of k.")),
                Paragraph(Text(
                    "Singleton extensionality reduces equality of the complete laws to the "
                        + "geometric mass factorization. The positive tail mass cancels, leaving "
                        + "the original geometric singleton mass at every residual value."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula success = F.Id("success");
        Formula threshold = F.Id("k");
        Formula value = F.Id("v");
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));
        Formula geometricLaw = Call("geometricMeasure", success);
        Formula tail = Seq(
            OpenBrace, value, Sp, InMacro, Sp, naturals, Sp, Mid, Sp,
            value, Sp, Geq, Sp, threshold, CloseBrace);
        Formula residual = Seq(value, Sp, Mapsto, Sp, value, Sp, Minus, Sp, threshold);
        Formula premise = new Formula.Logic(
            new Formula.Relation(success, FormulaRelationOperator.NotEqual, D(0)),
            FormulaLogicOperator.And,
            new Formula.Relation(success, FormulaRelationOperator.NotEqual, D(1)));
        Formula lawEquality = new Formula.Relation(
            Call("map", residual, Call("cond", geometricLaw, tail)),
            FormulaRelationOperator.Equal,
            geometricLaw);

        return Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                new Formula.BoundVariable(
                    FormulaIdentifier.Create("success"),
                    F.Id("unitInterval")),
                new Formula.BoundVariable(
                    FormulaIdentifier.Create("k"),
                    naturals),
            ],
            new Formula.Logic(premise, FormulaLogicOperator.Implies, lawEquality)));
    }

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(F.Id(name), [.. arguments]);
}
