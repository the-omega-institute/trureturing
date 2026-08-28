using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Naming.Composition;

internal sealed class ConnectionCoefficientCompositionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        var statement = AndAll(
            CoefficientBearingChainComposition(),
            RamanujanFactorization(),
            RamanujanRoleCertificate());

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
                            "The first branch binds a, b, X, Y, and Z once. The named "
                                + "IsCoefficientBearingCompletionChain bridge says that X, Y, Z "
                                + "are the state values on the typed source-middle-target path and "
                                + "that a and b are the weights of its first and second edges.")),
                        Paragraph(Text(
                            "Under that one bridge, the first three semantic conjuncts are the "
                                + "boxed scalar conclusion Z equals (ab)X, the explicit equality "
                                + "between the completed-path weight and ab, and non-primitiveness "
                                + "of that same two-edge path. The weight equality applies the "
                                + "pinned Mathlib theorem Quiver.Path.weight_comp.")),
                        Paragraph(Text(
                            "The fourth semantic conjunct is the positive-real Ramanujan 541 identity in "
                                + "the named Gaussian-total-mass, exponential-flow, and "
                                + "scale-Jacobian factors.")),
                        Paragraph(Text(
                            "The fifth semantic conjunct is the structural-composition certificate: "
                                + "the named typed Ramanujan completion path has, in order, the "
                                + "Gaussian-total-mass, exponential-flow, and scale-Jacobian roles. "
                                + "Swapping Gaussian and flow roles falsifies this public conjunct."))),
                    DescribeRole.Theorem)),
            []));
    }

    private static Formula CoefficientBearingChainComposition()
    {
        var reals = Seq(Mathbb, Grp(F.Id("R")));
        var a = F.Id("a");
        var b = F.Id("b");
        var X = F.Id("X");
        var Y = F.Id("Y");
        var Z = F.Id("Z");
        var bridge = Call("IsCoefficientBearingCompletionChain", a, b, X, Y, Z);
        var scalarConclusion = Equal(Z, Multiply(Seq(Open, Multiply(a, b), Close), X));
        var pathFactorization = Equal(
            Call(
                "pathWeight",
                Call("completionChainStepWeight", a, b),
                F.Id("completionChainPath")),
            Multiply(a, b));
        var nonPrimitive = new Formula.Not(Call(
            "IsPrimitiveConnectionPath",
            F.Id("completionChainPath")));

        return new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                new Formula.BoundVariable(FormulaIdentifier.Create("a"), reals),
                new Formula.BoundVariable(FormulaIdentifier.Create("b"), reals),
                new Formula.BoundVariable(FormulaIdentifier.Create("X"), reals),
                new Formula.BoundVariable(FormulaIdentifier.Create("Y"), reals),
                new Formula.BoundVariable(FormulaIdentifier.Create("Z"), reals),
            ],
            new Formula.Logic(
                bridge,
                FormulaLogicOperator.Implies,
                AndAll(scalarConclusion, pathFactorization, nonPrimitive)));
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

    private static Formula RamanujanRoleCertificate()
    {
        var orderedRoles = Seq(
            OpenBracket,
            F.Id("gaussianTotalMass"),
            Comma,
            Sp,
            F.Id("exponentialFlow"),
            Comma,
            Sp,
            F.Id("scaleJacobian"),
            CloseBracket);

        return Equal(
            Call("ramanujanPathRoles", F.Id("ramanujanCompletionPath")),
            orderedRoles);
    }
}
