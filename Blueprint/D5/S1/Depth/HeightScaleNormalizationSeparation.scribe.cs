using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Depth;

internal sealed class HeightScaleNormalizationSeparationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Depth/HeightScaleNormalizationSeparation.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Polynomial denominator depth and golden continued-fraction depth admit separate but no common positive normalization.",
        H("Height-Scale Normalization Separation"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("denominator-error-scale"),
                DeclarationHandle.Create(Prefix + "denominatorErrorScale"),
                H("Positive-level denominator error scale"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "At level Q this scale is the inverse square of Q plus one. The shift "
                        + "keeps the denominator positive at every natural input and avoids the "
                        + "totalized division-by-zero branch."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("continued-fraction-error-scale"),
                DeclarationHandle.Create(Prefix + "continuedFractionErrorScale"),
                H("Positive-level continued-fraction error scale"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "This is the Q-plus-one power of the inverse golden ratio squared, the "
                        + "exponential error scale supplied by all-one continued-fraction depth."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("height-scale-normalization-separation"),
                DeclarationHandle.Create(Prefix + "height_scale_normalization_separation"),
                H("Separate normalizers exist but a common positive normalizer does not"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Write Normalizes(w,d,L) for convergence of w(Q) times d(Q) to L as "
                            + "Q tends to infinity. Both scales have explicit exact normalizers: "
                            + "the denominator square and the reciprocal exponential scale.")),
                    Paragraph(Text(
                        "For an arbitrary weight, finite convergence on the inverse-square scale "
                            + "forces the exponentially normalized sequence to converge to zero. "
                            + "The proof uses the strict inequalities zero less than the inverse "
                            + "golden square less than one and polynomial-versus-geometric decay.")),
                    Paragraph(Text(
                        "Consequently the same weight cannot give both scales finite positive "
                            + "limits. Positivity is essential: without it the shared zero limit "
                            + "would make the obstruction false."))),
                DescribeRole.Theorem)),
        []));

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula Normalizes(Formula weight, Formula scale, Formula limit) =>
        Call("Normalizes", weight, scale, limit);

    private static Formula TheoremFormula()
    {
        var denominatorScale = Id("d_den");
        var depthScale = Id("d_cf");
        var denominatorWeight = Id("w_den");
        var depthWeight = Id("w_cf");
        var weight = Id("w");
        var denominatorLimit = Id("a");
        var depthLimit = Id("b");
        var weights = Call("Seq", Id("R"));
        var reals = Id("R");

        var denominatorWitness = new Formula.Bind(
            FormulaQuantifier.Exists,
            FormulaIdentifier.Create("w_den"),
            weights,
            Normalizes(denominatorWeight, denominatorScale, Num(1)));
        var depthWitness = new Formula.Bind(
            FormulaQuantifier.Exists,
            FormulaIdentifier.Create("w_cf"),
            weights,
            Normalizes(depthWeight, depthScale, Num(1)));

        var commonObstruction = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                new Formula.BoundVariable(FormulaIdentifier.Create("w"), weights),
                new Formula.BoundVariable(FormulaIdentifier.Create("a"), reals),
                new Formula.BoundVariable(FormulaIdentifier.Create("b"), reals),
            ],
            new Formula.Logic(
                And(
                    new Formula.Relation(
                        Num(0), FormulaRelationOperator.LessThan, denominatorLimit),
                    new Formula.Relation(
                        Num(0), FormulaRelationOperator.LessThan, depthLimit)),
                FormulaLogicOperator.Implies,
                new Formula.Not(And(
                    Normalizes(weight, denominatorScale, denominatorLimit),
                    Normalizes(weight, depthScale, depthLimit)))));

        return And(denominatorWitness, And(depthWitness, commonObstruction));
    }
}
