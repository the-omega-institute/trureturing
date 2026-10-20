using System;
using System.Linq;
using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.Hyperideal;

internal sealed class PositiveOppositeThirteenThresholdDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Geometry/Hyperideal/PositiveOppositeThirteenThreshold.exact_positive_opposite_thirteen_threshold";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact degree threshold for the positive-opposite-bound estimates.",
        H("The common-bound scheme"),
        Blocks(
            Paragraph(Text("Let a in (1,2) be the common lower bound on critical "
                + "edges, and let b in (1,2) be the common upper bound on high "
                + "edges. The prescribed critical lower, critical upper and high "
                + "upper cosine estimates are L(a)=2(2-a)/(a+1), "
                + "U(a,b)=(2b^2-a)/(1+2b^2) and "
                + "H(b)=(b^3-b^2+8b+1)/(3(2b^2+1)).")),
            Describe.Lean(
                DescribeId.Create("positive-opposite-thirteen-threshold"),
                DeclarationHandle.Create(Declaration),
                H("The first feasible high-edge degree"),
                StatementSource.FromAuthor(F.Disp(Statement())),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The first two strict estimates at critical "
                        + "degree six force a<7/5 and b^2<19/10, hence b<7/5. "
                        + "For 1<b<7/5, the high-edge estimate H(b) exceeds "
                        + "H(7/5)=541/615. This is greater than cos(pi/6), "
                        + "which bounds cos(2pi/D) from above for every "
                        + "integer degree D from seven through twelve. Thus "
                        + "all three strict estimates cannot hold together "
                        + "at those degrees.")),
                    Paragraph(Text("At degree thirteen the common bounds "
                        + "a=1399/1000 and b=689/500 satisfy all three strict "
                        + "estimates. The high-edge inequality follows from "
                        + "H(b)=176969141/199907000 and a rational lower "
                        + "bound for cos(44/91), with 2pi/13<44/91.")),
                    Paragraph(Text("The threshold concerns these three "
                        + "endpoint cosine estimates. It neither constructs "
                        + "shared edge lengths nor proves a hyperbolic "
                        + "realization."))),
                DescribeRole.Theorem))));

    private static Formula Statement()
    {
        var d = F.Id("D");
        var a = F.Id("a");
        var b = F.Id("b");
        var pi = F.Pi;
        var cosSix = Call("cos", new Formula.Fraction(Mul(F.D(2), pi), F.D(6)));
        var low = Call("lowBound", a);
        var critical = Call("criticalUpper", a, b);
        var high = Call("highUpper", b);
        var premises = And(Lt(F.D(6), d), Le(d, F.D(1, 2)),
            Lt(F.D(1), a), Lt(a, F.D(2)), Lt(F.D(1), b), Lt(b, F.D(2)));
        var below = All([("D", F.Id("Nat")),
                ("a", F.Id("Real")), ("b", F.Id("Real"))],
            new Formula.Logic(premises, FormulaLogicOperator.Implies,
                new Formula.Not(And(Lt(cosSix, low), Lt(critical, cosSix),
                    Lt(high, Call("cos", new Formula.Fraction(Mul(F.D(2), pi), d)))))));
        var witness = Exists([("a", F.Id("Real")), ("b", F.Id("Real"))],
            And(Lt(F.D(1), a), Lt(a, F.D(2)), Lt(F.D(1), b), Lt(b, F.D(2)),
                Lt(cosSix, low), Lt(critical, cosSix),
                Lt(high, Call("cos", new Formula.Fraction(Mul(F.D(2), pi), F.D(1, 3))))));
        return And(below, witness);
    }

    private static Formula All((string Name, Formula Type)[] variables, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll,
            [.. variables.Select(v => new Formula.BoundVariable(
                FormulaIdentifier.Create(v.Name), v.Type))], body);
    private static Formula Exists((string Name, Formula Type)[] variables, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.Exists,
            [.. variables.Select(v => new Formula.BoundVariable(
                FormulaIdentifier.Create(v.Name), v.Type))], body);
    private static Formula And(params Formula[] parts)
    {
        if (parts.Length == 0) throw new ArgumentException("Empty conjunction");
        var result = parts[^1];
        for (var i = parts.Length - 2; i >= 0; i--)
            result = new Formula.Logic(parts[i], FormulaLogicOperator.And, result);
        return result;
    }
    private static Formula Lt(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula Le(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Mul(Formula left, Formula right) =>
        F.Seq(left, F.Cdot, F.Sp, right);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(F.Id(name), [.. args]);
}
