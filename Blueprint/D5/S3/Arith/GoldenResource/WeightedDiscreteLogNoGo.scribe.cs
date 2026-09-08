using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.GoldenResource;

internal sealed class WeightedDiscreteLogNoGoDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/GoldenResource/WeightedDiscreteLogNoGo.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Unequal coordinate weights select a unique positive definite integer matrix with unequal diagonal entries.",
        H("Weighted Discrete Logarithmic Selection"),
        Blocks(
            Paragraph(Text("Let M be the set of all two by two integer matrices. For T in M, R(T) is its entrywise real cast, and P(T) means that R(T) is positive definite. Thus P(T) includes symmetry and strict positivity of the quadratic form on every nonzero real vector. The symbol I denotes the two by two real identity matrix.")),
            Entry("price-window", "priceWindow", "The price window",
                ForAll([Bound("p", Reals())], Iff(Call("W", F.Id("p")), Window(F.Id("p")))),
                "The two effective prices are three times p and two times p.", DescribeRole.Definition),
            Entry("weighted-objective", "objective", "The weighted objective",
                ForAll([Bound("p", Reals()), Bound("T", F.Id("M"))],
                    Equal(Score(F.Id("p"), F.Id("T")),
                        Subtract(Log(Det(F.Id("T"))), Multiply(F.Id("p"),
                            Add(Multiply(D(3), Cell(F.Id("T"), 0, 0)),
                                Multiply(D(2), Cell(F.Id("T"), 1, 1))))))),
                "All logarithms and arithmetic in the objective are real valued.", DescribeRole.Definition),
            Entry("selected-matrix", "selectedMatrix", "The selected matrix",
                Equal(F.Id("D"), Call("diag", D(2), D(3))),
                "The off-diagonal entries of D are zero.", DescribeRole.Definition),
            Entry("one-sixth", "one_sixth_mem_priceWindow", "An explicit interior price",
                Window(new Formula.Fraction(D(1), D(6))),
                "For positive x different from one, log(x) is strictly less than x minus one. Applying this bound to three halves and four thirds gives the upper bounds. Applying it to the reciprocals of two and three halves gives the strict lower bounds."),
            Entry("nonempty-window", "priceWindow_nonempty", "The price window is nonempty",
                new Formula.BindMany(FormulaQuantifier.Exists, [Bound("p", Reals())],
                    Call("W", F.Id("p"))),
                "One sixth is a witness."),
            Entry("positive-candidate", "selectedMatrix_posDef", "The candidate is positive definite",
                Positive(F.Id("D")),
                "A real diagonal matrix with diagonal entries two and three is positive definite."),
            Entry("integer-determinant-loss", "off_diagonal_det_loss", "The integral off-diagonal loss",
                ForAll([Bound("T", F.Id("M"))],
                    Implies(And(Positive(F.Id("T")), NotEqual(Cell(F.Id("T"), 0, 1), D(0))),
                        Le(Det(F.Id("T")), Subtract(
                            Multiply(Cell(F.Id("T"), 0, 0), Cell(F.Id("T"), 1, 1)), D(1))))),
                "For a symmetric two by two matrix the determinant is the diagonal product minus the square of the off-diagonal entry. A nonzero integer has square at least one."),
            Entry("unique-maximum", "weighted_unique_maximum", "A unique global maximum",
                MaximumFormula(),
                "The logarithm of the determinant is at most the sum of the diagonal logarithms, and the inequality is strict when the off-diagonal entry is nonzero. On the diagonal, the positive integer logarithmic selector applies at effective price three times p with optimizer two, and at effective price two times p with optimizer three. Any diagonal change gives a strict loss in at least one coordinate."),
            Entry("not-scalar", "selectedMatrix_not_scalar", "The optimizer is not scalar",
                And(NotEqual(Cell(F.Id("D"), 0, 0), Cell(F.Id("D"), 1, 1)),
                    ForAll([Bound("c", Reals())],
                        NotEqual(Call("R", F.Id("D")), Multiply(F.Id("c"), F.Id("I"))))),
                "The two diagonal entries are two and three. A scalar identity matrix has equal diagonal entries."),
            Entry("uniform-selection-assertion", "uniformSelection", "The equal-diagonal assertion",
                Iff(F.Id("A"), UniformFormula()),
                "This assertion would force every strict global optimizer at every price in W to have equal diagonal entries.",
                DescribeRole.Definition),
            Entry("uniformity-refuted", "weighted_selector_refutes_uniformity", "Equal diagonals are not forced",
                Seq(Neg, Sp, F.Id("A")),
                "At price one sixth, D is positive definite and every distinct admissible integer matrix has smaller objective, while its diagonal entries are unequal."))));

    private static DocumentBlock Entry(string id, string declaration, string title,
        Formula statement, string commentary, DescribeRole role = DescribeRole.Theorem) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(Disp(statement)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(commentary))), role);

    private static Formula MaximumFormula()
    {
        Formula p = F.Id("p");
        Formula t = F.Id("T");
        Formula d = F.Id("D");
        return ForAll([Bound("p", Reals()), Bound("T", F.Id("M"))],
            Implies(And(Call("W", p), Positive(t)),
                And(Le(Score(p, t), Score(p, d)),
                    Implies(NotEqual(t, d), Less(Score(p, t), Score(p, d))))));
    }

    private static Formula UniformFormula()
    {
        Formula p = F.Id("p");
        Formula t = F.Id("T");
        Formula u = F.Id("U");
        Formula strictMaximum = ForAll([Bound("U", F.Id("M"))],
            Implies(Positive(u), Implies(NotEqual(u, t), Less(Score(p, u), Score(p, t)))));
        return ForAll([Bound("p", Reals())], Implies(Call("W", p),
            ForAll([Bound("T", F.Id("M"))], Implies(Positive(t),
                Implies(strictMaximum, Equal(Cell(t, 0, 0), Cell(t, 1, 1)))))));
    }

    private static Formula Window(Formula p) =>
        And(And(Less(Log(new Formula.Fraction(D(3), D(2))), Multiply(D(3), p)),
                Less(Multiply(D(3), p), Log(D(2)))),
            And(Less(Log(new Formula.Fraction(D(4), D(3))), Multiply(D(2), p)),
                Less(Multiply(D(2), p), Log(new Formula.Fraction(D(3), D(2))))));

    private static Formula Cell(Formula t, byte i, byte j) =>
        new Formula.Apply(t, [D(i), D(j)]);

    private static Formula Det(Formula t) => Call("det", Call("R", t));
    private static Formula Positive(Formula t) => Call("P", t);
    private static Formula Score(Formula p, Formula t) => Call("f", p, t);
    private static Formula Log(Formula x) => Call("log", x);
    private static Formula Less(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Le(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Implies(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Iff(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula ForAll(Formula.BoundVariable[] variables, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables], body);
    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);
    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
}
