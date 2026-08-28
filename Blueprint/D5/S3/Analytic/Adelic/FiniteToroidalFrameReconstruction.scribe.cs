using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Adelic;

internal sealed class FiniteToroidalFrameReconstructionDocument
    : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A compact pointwise-nonvanishing twist cover yields finite weighted frames "
            + "that reconstruct the completed-zeta amplitude.",
        H("Finite Toroidal Frame Reconstruction"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("finite-toroidal-frame-reconstruction"),
                DeclarationHandle.Create(
                    "D5/S3/Analytic/Adelic/FiniteToroidalFrameReconstruction."
                        + "finite_toroidal_frame_reconstruction"),
                H("Finite weighted period frames reconstruct xi"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Continuity makes each twist-nonvanishing locus open. Compactness "
                            + "then extracts a finite subcover from the pointwise "
                            + "nonvanishing family.")),
                    Paragraph(Text(
                        "Positive square-root weights construct a nonzero complex "
                            + "Euclidean carrier frame at every point of the window. The "
                            + "period factorization constructs the observed frame as its "
                            + "canonical xi multiple.")),
                    Paragraph(Text(
                        "The displayed inner product is ordered carrier first because "
                            + "Lean is conjugate linear in its first argument. It therefore "
                            + "represents the source convention that is linear in the "
                            + "period-frame argument."))),
                DescribeRole.Theorem))));

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new Formula.BoundVariable(FormulaIdentifier.Create(name), domain);

    private static Formula EqualTo(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula NotEqualTo(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);

    private static Formula LessThan(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula TheoremFormula()
    {
        Formula type = Call("Type");
        Formula real = Call("Real");
        Formula complex = Call("Complex");
        Formula indexType = F.Id("Index");
        Formula window = F.Id("K");
        Formula period = F.Id("P");
        Formula twist = F.Id("T");
        Formula selected = F.Id("I");
        Formula weights = F.Id("w");
        Formula index = F.Id("i");
        Formula point = F.Id("s");
        Formula familyType = Arrow(indexType, Arrow(complex, complex));
        Formula weightType = Arrow(indexType, real);
        Formula windowType = Call("Set", complex);
        Formula periodAtPoint = Apply(Apply(period, index), point);
        Formula twistAtPoint = Apply(Apply(twist, index), point);
        Formula xiAtPoint = Apply(F.Id("xiReading"), point);
        Formula pointInWindow = Call("mem", point, window);
        Formula indexSelected = Call("mem", index, selected);

        Formula twistContinuity = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("i", indexType)],
            Call("Continuous", Apply(twist, index)));
        Formula factorization = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("i", indexType), Bound("s", complex)],
            EqualTo(periodAtPoint, Seq(xiAtPoint, Sp, Times, Sp, twistAtPoint)));
        Formula pointwiseCover = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("s", complex)],
            Implies(
                pointInWindow,
                new Formula.BindMany(
                    FormulaQuantifier.Exists,
                    [Bound("i", indexType)],
                    NotEqualTo(twistAtPoint, D(0)))));
        Formula premises = And(
            twistContinuity,
            And(
                factorization,
                And(Call("IsCompact", window), pointwiseCover)));

        Formula finiteCover = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("s", complex)],
            Implies(
                pointInWindow,
                new Formula.BindMany(
                    FormulaQuantifier.Exists,
                    [Bound("i", indexType)],
                    And(indexSelected, NotEqualTo(twistAtPoint, D(0))))));
        Formula positiveWeights = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("i", indexType)],
            Implies(indexSelected, LessThan(D(0), Apply(weights, index))));
        Formula carrier = Call("weightedFrame", selected, weights, twist, point);
        Formula observed = Call("weightedFrame", selected, weights, period, point);
        Formula denominator = Seq(new Formula.Norm(carrier), Caret, Grp(D(2)));
        Formula reconstruction = EqualTo(
            xiAtPoint,
            new Formula.Fraction(Call("inner", complex, carrier, observed), denominator));
        Formula pointwiseReconstruction = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("s", complex)],
            Implies(
                pointInWindow,
                And(NotEqualTo(carrier, D(0)), reconstruction)));
        Formula allPositiveFrames = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("w", weightType)],
            Implies(positiveWeights, pointwiseReconstruction));
        Formula conclusion = new Formula.BindMany(
            FormulaQuantifier.Exists,
            [Bound("I", Call("Finset", indexType))],
            And(finiteCover, allPositiveFrames));

        return Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                Bound("Index", type),
                Bound("K", windowType),
                Bound("P", familyType),
                Bound("T", familyType),
            ],
            Implies(premises, conclusion)));
    }
}
