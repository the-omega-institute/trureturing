using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil;

internal sealed class FiniteZeroGramHierarchyDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finite positive-weighted zero-resolvent kernel is a Gram matrix whose determinant "
            + "is one exact nonnegative Cauchy--Binet contribution.",
        H("Finite Zero Gram Hierarchy"),
        Blocks(Describe.Lean(
            DescribeId.Create("finite-zero-gram-hierarchy"),
            DeclarationHandle.Create(
                "D5/S3/Weil/FiniteZeroGramHierarchy.finite_zero_gram_hierarchy"),
            H("Finite zero-resolvent Gram determinants are nonnegative"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The sampling nodes lie in the open upper half-plane, so no real "
                        + "ordinate can make a resolvent denominator zero. Nonnegative real "
                        + "weights define the diagonal middle factor of the Gram matrix.")),
                Paragraph(Text(
                    "Mathlib's positive-semidefinite diagonal and congruence lemmas prove "
                        + "positivity. Multiplicativity of the determinant, the diagonal "
                        + "determinant formula, and conjugate-transpose compatibility give "
                        + "the displayed weighted determinant square.")),
                Paragraph(Text(
                    "The source's infinite subset expansion is not asserted because it omits "
                        + "enumeration and convergence hypotheses. The reverse implication to "
                        + "the Riemann hypothesis is also omitted: a Gram construction is "
                        + "positive for every real ordinate family and therefore cannot locate "
                        + "zeta zeros on the critical line.")),
                Paragraph(Text(
                    "A companion Lean theorem shows sharpness at determinant zero using two "
                        + "distinct ordinates, positive weights, and a repeated upper-half-plane "
                        + "sampling node."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula type = F.Id("Type");
        Formula real = Call("Real");
        Formula complex = Call("Complex");
        Formula indexType = F.Id("I");
        Formula nodes = F.Id("z");
        Formula ordinates = F.Id("gamma");
        Formula weights = F.Id("m");
        Formula a = F.Id("a");
        Formula b = F.Id("b");
        Formula k = F.Id("k");
        Formula nodeMap = new Formula.TypeArrow(indexType, complex);
        Formula realMap = new Formula.TypeArrow(indexType, real);
        Formula resolvent = Call("zeroResolventMatrix", nodes, ordinates);
        Formula gram = Call("finiteZeroGramMatrix", nodes, ordinates, weights);

        Formula NodeAt(Formula index) => Apply(nodes, index);
        Formula OrdinateAt(Formula index) => Apply(ordinates, index);
        Formula WeightAt(Formula index) => Apply(weights, index);
        Formula ResolventAt(Formula row, Formula column) =>
            Apply(resolvent, row, column);
        Formula GramAt(Formula row, Formula column) => Apply(gram, row, column);

        Formula upperHalfPlane = ForAll(
            [Bound("a", indexType)],
            Less(D(0), Call("im", NodeAt(a))));
        Formula nonnegativeWeights = ForAll(
            [Bound("k", indexType)],
            LessEqual(D(0), WeightAt(k)));
        Formula denominatorNonzero = ForAll(
            [Bound("a", indexType), Bound("k", indexType)],
            NotEqual(
                Sub(Call("ofReal", OrdinateAt(k)), NodeAt(a)),
                D(0)));
        Formula summand = Mul(
            Mul(ResolventAt(a, k), Call("ofReal", WeightAt(k))),
            Call("conj", ResolventAt(b, k)));
        Formula entryExpansion = ForAll(
            [Bound("a", indexType), Bound("b", indexType)],
            Equal(GramAt(a, b), Call("sum", k, indexType, summand)));
        Formula determinant = Call("det", gram);
        Formula resolventDeterminant = Call("det", resolvent);
        Formula weightProduct = Call(
            "prod", k, indexType, Call("ofReal", WeightAt(k)));
        Formula determinantExpansion = Equal(
            determinant,
            Mul(
                Mul(weightProduct, resolventDeterminant),
                Call("conj", resolventDeterminant)));
        Formula conclusion = All(
            denominatorNonzero,
            entryExpansion,
            Call("PosSemidef", gram),
            determinantExpansion,
            LessEqual(D(0), determinant));
        Formula assumptions = All(
            Call("Fintype", indexType),
            Call("DecidableEq", indexType),
            upperHalfPlane,
            nonnegativeWeights);

        return Disp(ForAll(
            [
                Bound("I", type),
                Bound("z", nodeMap),
                Bound("gamma", realMap),
                Bound("m", realMap),
            ],
            Implies(assumptions, conclusion)));
    }

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula Mul(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);

    private static Formula Sub(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula NotEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);

    private static Formula Less(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);

    private static Formula LessEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula All(params Formula[] clauses)
    {
        Formula result = clauses[^1];
        for (var index = clauses.Length - 2; index >= 0; index--)
            result = new Formula.Logic(clauses[index], FormulaLogicOperator.And, result);
        return result;
    }

    private static Formula ForAll(Formula.BoundVariable[] variables, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables], body);
}
