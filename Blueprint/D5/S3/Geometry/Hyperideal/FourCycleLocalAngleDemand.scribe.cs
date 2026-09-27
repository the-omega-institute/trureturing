using System;
using System.Linq;
using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.Hyperideal;

internal sealed class FourCycleLocalAngleDemandDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Geometry/Hyperideal/FourCycleLocalAngleDemand.paired_angle_demand";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Strict local angle demand for a paired hyper-ideal cosine tuple.",
        H("Main-edge dominance forces transverse angle demand"),
        Blocks(
            Paragraph(Text("Use the local order (12,13,14,34,24,23) and the exact cosine "
                + "function from FourCycleEnvelopes. The tuple is (r,a,b,o,a,b). "
                + "The three cosine-range assumptions below concern the target angle "
                + "and the two distinct transverse angles.")),
            Describe.Lean(
                DescribeId.Create("paired-fourcycle-strict-local-angle-demand"),
                DeclarationHandle.Create(Declaration),
                H("A strict demand without a common transverse width"),
                StatementSource.FromAuthor(F.Disp(Statement())),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For r,a,b,o>1 with r>=1+a+b, assume each of the three "
                        + "displayed cosine values lies strictly between -1 and 1. The "
                        + "target angle theta and transverse angles beta,delta then satisfy "
                        + "2theta+beta+delta>pi. No acute-target restriction or bound on "
                        + "the ratio a/b is used.")),
                    Paragraph(Text("The proof derives the paired cosine and sine identities "
                        + "from the six-variable formula, a strict positive slack for the "
                        + "half-angle tangent, and a coupled lower bound for the transverse "
                        + "parameter. The final comparison covers both obtuse and acute "
                        + "target angles.")),
                    Paragraph(Text("This analytic statement assumes only the three cosine "
                        + "ranges it uses. It does not establish the range of the distinct "
                        + "opposite-edge cosine, certify a genuine geometric tetrahedron, "
                        + "construct face pairings, or prove global hyperbolic realization."))),
                DescribeRole.Theorem))));

    private static Formula Statement()
    {
        var r = F.Id("r"); var a = F.Id("a");
        var b = F.Id("b"); var o = F.Id("o");
        var ct = Call("cosine", r, a, b, o, a, b);
        var ca = Call("cosine", a, b, r, a, b, o);
        var cb = Call("cosine", b, a, r, b, a, o);
        var minusOne = F.Seq(F.Minus, F.D(1));
        var premise = And(
            Lt(F.D(1), r), Lt(F.D(1), a), Lt(F.D(1), b), Lt(F.D(1), o),
            Le(F.Seq(F.D(1), F.Plus, a, F.Plus, b), r),
            Lt(minusOne, ct), Lt(ct, F.D(1)),
            Lt(minusOne, ca), Lt(ca, F.D(1)),
            Lt(minusOne, cb), Lt(cb, F.D(1)));
        var angleSum = F.Seq(F.D(2), F.Cdot, F.Sp, Call("arccos", ct), F.Plus,
            Call("arccos", ca), F.Plus, Call("arccos", cb));
        var real = new Formula.NamedConstant(FormulaIdentifier.Create("Real"));
        Formula.BoundVariable[] binders = [.. new[] { "r", "a", "b", "o" }
            .Select(name => new Formula.BoundVariable(FormulaIdentifier.Create(name), real))];
        return new Formula.BindMany(FormulaQuantifier.ForAll, [.. binders],
            new Formula.Logic(premise, FormulaLogicOperator.Implies,
                Lt(F.Pi, angleSum)));
    }

    private static Formula And(params Formula[] clauses)
    {
        if (clauses.Length == 0) throw new ArgumentException("Empty conjunction.");
        var result = clauses[^1];
        for (var i = clauses.Length - 2; i >= 0; i--)
            result = new Formula.Logic(clauses[i], FormulaLogicOperator.And, result);
        return result;
    }

    private static Formula Le(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Lt(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(F.Id(name), [.. args]);
}
