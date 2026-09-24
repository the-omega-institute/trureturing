using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Dynamics;

internal sealed class ProfiniteFactorialApproximationDocument : IScribeDocumentDefinition
{
    private const string DeclarationPrefix =
        "D5/S1/Dynamics/ProfiniteFactorialApproximation.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Factorial-stage natural representatives converge to each compatible-residue "
            + "profinite integer.",
        H("Factorial Representatives of Profinite Integers"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("factorial-representative"),
                DeclarationHandle.Create(DeclarationPrefix + "factorialRepresentative"),
                H("The factorial-stage representative"),
                StatementSource.FromAuthor(RepresentativeFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "At stage n, the coordinate with modulus n factorial has a unique "
                        + "representative between zero and n factorial minus one. The "
                        + "definition selects that natural number."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("factorial-representatives-converge"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "natEmbedding_factorialRepresentative_tendsto"),
                H("The embedded representatives converge"),
                StatementSource.FromAuthor(ConvergenceFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For a fixed coordinate m, every factorial stage n with n at least "
                            + "m + 1 has m + 1 dividing n factorial. Compatibility therefore "
                            + "reduces the chosen stage representative exactly to the m-th "
                            + "coordinate of x.")),
                    Paragraph(Text(
                        "Each coordinate is consequently equal to its target eventually. "
                            + "Coordinatewise convergence in the product topology, followed "
                            + "by the induced subtype topology, gives convergence to x.")),
                    Paragraph(Text(
                        "The exact representative sequence and convergence statement are "
                            + "repo-derived. They strengthen density by providing a canonical "
                            + "approximating sequence for every compatible residue family."))),
                DescribeRole.Theorem))));

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));

    private static Formula Factorial(Formula value) => Seq(value, Bang);

    private static Formula Representative(Formula point, Formula stage) =>
        Call("factorialRepresentative", point, stage);

    private static Formula Embedding(Formula value) => Call("natEmbedding", value);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(F.Id(name), [.. arguments]);

    private static Formula Lambda(Formula binder, Formula body) =>
        Seq(Open, binder, Sp, Mapsto, Sp, body, Close);

    private static Formula RepresentativeFormula()
    {
        Formula point = F.Id("x");
        Formula stage = F.Id("n");
        Formula index = Seq(Factorial(stage), Sp, Minus, Sp, D(1));
        Formula coordinate = new Formula.Subscript(point, Grp(index));
        Formula equality = new Formula.Relation(
            Representative(point, stage),
            FormulaRelationOperator.Equal,
            Call("val", coordinate));

        return Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                new Formula.BoundVariable(
                    FormulaIdentifier.Create("x"), F.Id("ProfiniteIntegers")),
                new Formula.BoundVariable(FormulaIdentifier.Create("n"), Naturals()),
            ],
            equality));
    }

    private static Formula ConvergenceFormula()
    {
        Formula point = F.Id("x");
        Formula stage = F.Id("n");
        Formula sequence = Lambda(stage, Embedding(Representative(point, stage)));
        Formula convergence = Call(
            "Tendsto", sequence, F.Id("atTop"), Call("nhds", point));

        return Disp(new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("x"),
            F.Id("ProfiniteIntegers"),
            convergence));
    }
}
