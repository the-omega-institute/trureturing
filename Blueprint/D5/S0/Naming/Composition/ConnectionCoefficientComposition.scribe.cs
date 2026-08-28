using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Naming.Composition;

internal sealed class ConnectionCoefficientCompositionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        var statement = AndAll(
            PathWeightMultiplication(),
            CompletedPathFactorization(),
            CompletedPathIsNotPrimitive(),
            RamanujanFactorization(),
            RamanujanCertificateStatus());

        return DocumentDefinition.Create(ScribeNode.Create(
            "Typed completion paths retain coefficient order, factor roles, and certificate status.",
            H("Connection Coefficient Multiplication"),
            Blocks(
                Describe.Lean(
                    DescribeId.Create("connection-coefficient-multiplication"),
                    DeclarationHandle.Create(
                        "D5/S0/Naming/Composition/ConnectionCoefficientComposition."
                            + "connection_coefficient_multiplication"),
                    H("Connection coefficients multiply along typed completion paths"),
                    StatementSource.FromAuthor(Disp(statement)),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text(
                            "The first three conjuncts quantify typed Quiver edges X to Y and "
                                + "Y to Z. Path weight multiplication is the pinned Mathlib "
                                + "theorem Quiver.Path.weight_comp; the same path is explicitly "
                                + "identified as the completed factorization and has length two, "
                                + "so it is not a one-edge primitive.")),
                        Paragraph(Text(
                            "The fourth conjunct is the positive-real Ramanujan 541 identity in "
                                + "the named Gaussian-total-mass, exponential-flow, and "
                                + "scale-Jacobian factors.")),
                        Paragraph(Text(
                            "The fifth conjunct gives the factorization structural-composition "
                                + "certificate status. Its predicate checks the exact three-edge "
                                + "Ramanujan path, the ordered role list, non-primitiveness, and "
                                + "agreement of the radical with the path weight. Permuting the "
                                + "roles therefore changes the certified statement even though "
                                + "real multiplication is commutative."))),
                    DescribeRole.Theorem)),
            []));
    }

    private static Formula AndAll(params Formula[] items)
    {
        Formula result = items[^1];
        for (var index = items.Length - 2; index >= 0; index--)
        {
            result = new Formula.Logic(items[index], FormulaLogicOperator.And, result);
        }
        return result;
    }

    private static Formula PathWeightMultiplication()
    {
        var V = F.Id("V");
        var R = F.Id("R");
        var X = F.Id("X");
        var Y = F.Id("Y");
        var Z = F.Id("Z");
        var edgeWeight = F.Id("edgeWeight");
        var firstStep = F.Id("firstStep");
        var secondStep = F.Id("secondStep");
        var completed = Call("completedPath", firstStep, secondStep);
        var assumptions = new Formula.Logic(
            Call("Quiver", V),
            FormulaLogicOperator.And,
            Call("Monoid", R));
        var equality = Equal(
            Call("pathWeight", edgeWeight, completed),
            Multiply(
                new Formula.Apply(edgeWeight, [firstStep]),
                new Formula.Apply(edgeWeight, [secondStep])));

        return new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                new Formula.BoundVariable(FormulaIdentifier.Create("V"), F.Id("Type")),
                new Formula.BoundVariable(FormulaIdentifier.Create("R"), F.Id("Type")),
                new Formula.BoundVariable(FormulaIdentifier.Create("X"), V),
                new Formula.BoundVariable(FormulaIdentifier.Create("Y"), V),
                new Formula.BoundVariable(FormulaIdentifier.Create("Z"), V),
                new Formula.BoundVariable(
                    FormulaIdentifier.Create("edgeWeight"), Call("EdgeWeight", V, R)),
                new Formula.BoundVariable(
                    FormulaIdentifier.Create("firstStep"), Call("Hom", X, Y)),
                new Formula.BoundVariable(
                    FormulaIdentifier.Create("secondStep"), Call("Hom", Y, Z)),
            ],
            new Formula.Logic(assumptions, FormulaLogicOperator.Implies, equality));
    }

    private static Formula CompletedPathFactorization()
    {
        var V = F.Id("V");
        var R = F.Id("R");
        var X = F.Id("X");
        var Y = F.Id("Y");
        var Z = F.Id("Z");
        var edgeWeight = F.Id("edgeWeight");
        var firstStep = F.Id("firstStep");
        var secondStep = F.Id("secondStep");
        var conclusion = Call(
            "FactorsAlongCompletedPath",
            edgeWeight,
            Multiply(
                new Formula.Apply(edgeWeight, [firstStep]),
                new Formula.Apply(edgeWeight, [secondStep])),
            Call("completedPath", firstStep, secondStep),
            firstStep,
            secondStep);
        var assumptions = new Formula.Logic(
            Call("Quiver", V),
            FormulaLogicOperator.And,
            Call("Monoid", R));

        return new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                new Formula.BoundVariable(FormulaIdentifier.Create("V"), F.Id("Type")),
                new Formula.BoundVariable(FormulaIdentifier.Create("R"), F.Id("Type")),
                new Formula.BoundVariable(FormulaIdentifier.Create("X"), V),
                new Formula.BoundVariable(FormulaIdentifier.Create("Y"), V),
                new Formula.BoundVariable(FormulaIdentifier.Create("Z"), V),
                new Formula.BoundVariable(
                    FormulaIdentifier.Create("edgeWeight"), Call("EdgeWeight", V, R)),
                new Formula.BoundVariable(
                    FormulaIdentifier.Create("firstStep"), Call("Hom", X, Y)),
                new Formula.BoundVariable(
                    FormulaIdentifier.Create("secondStep"), Call("Hom", Y, Z)),
            ],
            new Formula.Logic(assumptions, FormulaLogicOperator.Implies, conclusion));
    }

    private static Formula CompletedPathIsNotPrimitive()
    {
        var V = F.Id("V");
        var X = F.Id("X");
        var Y = F.Id("Y");
        var Z = F.Id("Z");
        var firstStep = F.Id("firstStep");
        var secondStep = F.Id("secondStep");
        var conclusion = new Formula.Not(Call(
            "IsPrimitiveConnectionPath",
            Call("completedPath", firstStep, secondStep)));

        return BindPathData(
            V,
            X,
            Y,
            Z,
            firstStep,
            secondStep,
            new Formula.Logic(
                Call("Quiver", V), FormulaLogicOperator.Implies, conclusion));
    }

    private static Formula BindPathData(
        Formula V,
        Formula X,
        Formula Y,
        Formula Z,
        Formula firstStep,
        Formula secondStep,
        Formula body) =>
        new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                new Formula.BoundVariable(FormulaIdentifier.Create("V"), F.Id("Type")),
                new Formula.BoundVariable(FormulaIdentifier.Create("X"), V),
                new Formula.BoundVariable(FormulaIdentifier.Create("Y"), V),
                new Formula.BoundVariable(FormulaIdentifier.Create("Z"), V),
                new Formula.BoundVariable(
                    FormulaIdentifier.Create("firstStep"), Call("Hom", X, Y)),
                new Formula.BoundVariable(
                    FormulaIdentifier.Create("secondStep"), Call("Hom", Y, Z)),
            ],
            body);

    private static Formula PositiveRealStatement(Formula conclusion)
    {
        var x = F.Id("x");
        return new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("x"),
            Seq(Mathbb, Grp(F.Id("R"))),
            new Formula.Logic(
                new Formula.Relation(Num(0), FormulaRelationOperator.LessThan, x),
                FormulaLogicOperator.Implies,
                conclusion));
    }

    private static Formula RamanujanFactorization()
    {
        var x = F.Id("x");
        return PositiveRealStatement(Equal(
            Call("ramanujanRadical", x),
            Multiply(
                Multiply(F.Id("gaussianMassFactor"), Call("exponentialFlowFactor", x)),
                Call("scaleJacobianFactor", x))));
    }

    private static Formula RamanujanCertificateStatus()
    {
        var x = F.Id("x");
        return PositiveRealStatement(Call(
            "IsStructuralConstantCompositionCertificate",
            x,
            F.Id("ramanujanCompletionPath")));
    }
}
