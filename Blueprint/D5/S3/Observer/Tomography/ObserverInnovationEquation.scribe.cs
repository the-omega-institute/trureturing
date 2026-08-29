using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Tomography;

internal sealed class ObserverInnovationEquationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A strict Gram spectral-floor drop identifies the unique innovation zero.",
        H("Observer Innovation Equation"),
        Blocks(Describe.Lean(
            DescribeId.Create("strict-gram-floor-drop-identifies-the-innovation-zero"),
            DeclarationHandle.Create(
                "D5/S3/Observer/Tomography/ObserverInnovationEquation."
                    + "observer_innovation_equation"),
            H("The new Gram floor is the unique innovation zero"),
            StatementSource.FromAuthor(InnovationFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The old and extended matrices are constructed from one indexed feature "
                        + "family by the canonical Gram operation. The three displayed floor "
                        + "equivalences are the positive-definite and positive-semidefinite "
                        + "threshold characterizations of their least eigenvalues.")),
                Paragraph(Text(
                    "Pinned Mathlib supplies the canonical Gram matrix, the Schur positivity "
                        + "equivalence, and the block determinant factorization. At the new "
                        + "floor the extended determinant vanishes while the old block remains "
                        + "invertible, forcing the innovation to vanish; the same factorization "
                        + "and the floor thresholds prove uniqueness below the old floor.")),
                Paragraph(Text(
                    "Repository and pinned-library searches found related Schur-energy and "
                        + "block-positivity declarations, but no exact innovation-root theorem "
                        + "on the source-constructed real-or-complex Gram carrier."))),
            DescribeRole.Theorem))));

    private static Formula InnovationFormula()
    {
        Formula type = Call("Type");
        Formula real = Call("Real");
        Formula unit = Call("Unit");
        Formula K = F.Id("K"), V = F.Id("V"), index = F.Id("iota");
        Formula feature = F.Id("feature");
        Formula alphaOld = F.Id("alphaOld"), alphaNew = F.Id("alphaNew");
        Formula a = F.Id("a"), i = F.Id("i"), u = F.Id("u");
        Formula indexSum = Call("Sum", index, unit);
        Formula oldFeature = Call("compose", feature, Call("inl"));
        Formula oldGram = F.Id("oldGram");
        Formula fullGram = F.Id("fullGram");
        Formula coupling = F.Id("coupling");
        Formula innovation = F.Id("innovation");
        Formula oldShift = Sub(
            oldGram,
            Call("scalarMatrix", K, index, a));
        Formula fullShift = Sub(
            fullGram,
            Call("scalarMatrix", K, indexSum, a));
        Formula oldFloor = ForAll(
            "a",
            real,
            Iff(Call("PosDef", oldShift), Less(a, alphaOld)));
        Formula fullFloorSemi = ForAll(
            "a",
            real,
            Iff(Call("PosSemidef", fullShift), LessEqual(a, alphaNew)));
        Formula fullFloorDef = ForAll(
            "a",
            real,
            Iff(Call("PosDef", fullShift), Less(a, alphaNew)));
        Formula couplingValue = Call(
            "matrix",
            Lambda(i, Lambda(u, Call(
                "inner",
                K,
                Apply(feature, Call("inl", i)),
                Apply(feature, Call("inr", Call("unit")))))));
        Formula shiftedInverse = Call("inverse", Sub(
            oldGram,
            Call("scalarMatrix", K, index, a)));
        Formula quadratic = Call(
            "entry",
            Call(
                "multiply",
                Call("conjTranspose", coupling),
                shiftedInverse,
                coupling),
            Call("unit"),
            Call("unit"));
        Formula innovationValue = Sub(
            Sub(
                Call(
                    "inner",
                    K,
                    Apply(feature, Call("inr", Call("unit"))),
                    Apply(feature, Call("inr", Call("unit")))),
                Call("complex", K, a)),
            quadratic);
        Formula uniqueness = ForAll(
            "a",
            real,
            Implies(
                And(
                    Less(a, alphaOld),
                    Equal(Apply(innovation, a), D(0))),
                Equal(a, alphaNew)));
        Formula conclusion = And(
            Equal(Apply(innovation, alphaNew), D(0)),
            uniqueness);
        Formula assumptions = All(
            Call("RCLike", K),
            Call("NormedAddCommGroup", V),
            Call("InnerProductSpace", K, V),
            Call("Fintype", index),
            Call("DecidableEq", index),
            oldFloor,
            fullFloorSemi,
            fullFloorDef,
            Less(alphaNew, alphaOld));
        Formula definitions = Seq(
            F.Id("let"), Sp, oldGram, Sp, Eq, Sp,
            Call("gram", K, oldFeature), Semi, Sp,
            F.Id("let"), Sp, fullGram, Sp, Eq, Sp,
            Call("gram", K, feature), Semi, Sp,
            F.Id("let"), Sp, coupling, Sp, Eq, Sp,
            couplingValue, Semi, Sp,
            F.Id("let"), Sp, innovation, Sp, Eq, Sp,
            Lambda(a, innovationValue), Semi, Sp,
            Implies(assumptions, conclusion));

        return Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                Bound("K", type),
                Bound("V", type),
                Bound("iota", type),
                Bound("feature", Arrow(indexSum, V)),
                Bound("alphaOld", real),
                Bound("alphaNew", real),
            ],
            definitions));
    }

    private static Formula ForAll(string name, Formula domain, Formula body) =>
        new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound(name, domain)],
            body);

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula Lambda(Formula variable, Formula body) =>
        Call("lambda", variable, body);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula Sub(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula Less(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);

    private static Formula LessEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula All(params Formula[] formulas) =>
        formulas.Aggregate(And);

    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Iff, right);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);
}
