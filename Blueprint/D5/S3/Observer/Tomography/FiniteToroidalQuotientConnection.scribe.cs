using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Tomography;

internal sealed class FiniteToroidalQuotientConnectionDocument
    : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finite positive toroidal Gram frame recovers its common two-point factor by a "
            + "local kernel quotient.",
        H("Finite Toroidal Quotient Connection"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("finite-toroidal-frame-quotient-connection"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/Tomography/FiniteToroidalQuotientConnection."
                        + "finite_toroidal_frame_quotient_connection"),
                H("Finite toroidal Gram quotients recover the common factor"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The toric periods, twists, common factor, finite selection, and "
                            + "spectral window are explicit parameters. This isolates the "
                            + "algebraic content from external analytic constructions.")),
                    Paragraph(Text(
                        "Strictly positive real weights and a nonzero selected twist at each "
                            + "window point make the carrier Gram kernel nonzero on the "
                            + "diagonal.")),
                    Paragraph(Text(
                        "Pointwise period factorization pulls the common factor through the "
                            + "finite sum. At every pair where the carrier kernel is nonzero, "
                            + "division then gives the displayed quotient connection."))),
                DescribeRole.Theorem))));

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

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
        Formula selected = F.Id("I");
        Formula weights = F.Id("w");
        Formula period = F.Id("P");
        Formula twist = F.Id("T");
        Formula xi = F.Id("xi");
        Formula index = F.Id("j");
        Formula point = F.Id("u");
        Formula s = F.Id("s");
        Formula t = F.Id("t");
        Formula familyType = Arrow(indexType, Arrow(complex, complex));
        Formula indexSelected = Call("mem", index, selected);
        Formula pointInWindow = Call("mem", point, window);
        Formula twistAtPoint = Apply(Apply(twist, index), point);
        Formula factorization = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("j", indexType), Bound("u", complex)],
            Implies(
                indexSelected,
                EqualTo(
                    Apply(Apply(period, index), point),
                    Seq(Apply(xi, point), Sp, Times, Sp, twistAtPoint))));
        Formula positiveWeights = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("j", indexType)],
            Implies(indexSelected, LessThan(D(0), Apply(weights, index))));
        Formula pointwiseNonvanishing = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("u", complex)],
            Implies(
                pointInWindow,
                new Formula.BindMany(
                    FormulaQuantifier.Exists,
                    [Bound("j", indexType)],
                    And(indexSelected, NotEqualTo(twistAtPoint, D(0))))));
        Formula carrierDiagonal = Call("weightedGramKernel", selected, weights, twist, point, point);
        Formula diagonalNonzero = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("u", complex)],
            Implies(pointInWindow, NotEqualTo(carrierDiagonal, D(0))));
        Formula carrierKernel = Call("weightedGramKernel", selected, weights, twist, s, t);
        Formula quotient = Call("localQuotientKernel", selected, weights, period, twist, s, t);
        Formula quotientValue = Seq(Apply(xi, s), Sp, Times, Sp, Call("conj", Apply(xi, t)));
        Formula localConnection = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("s", complex), Bound("t", complex)],
            Implies(NotEqualTo(carrierKernel, D(0)), EqualTo(quotient, quotientValue)));
        Formula premises = And(positiveWeights, And(factorization, pointwiseNonvanishing));

        return Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                Bound("Index", type),
                Bound("K", Call("Set", complex)),
                Bound("I", Call("Finset", indexType)),
                Bound("w", Arrow(indexType, real)),
                Bound("P", familyType),
                Bound("T", familyType),
                Bound("xi", Arrow(complex, complex)),
            ],
            Implies(premises, And(diagonalNonzero, localConnection))));
    }

    private static Formula Call(string name, params Formula[] arguments) =>
        Apply(Seq(Operatorname, Grp(F.Id(name))), arguments);
}
