using System;
using System.Linq;
using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.Hyperideal;

internal sealed class FourCycleLocalAngleDemandDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Geometry/Hyperideal/FourCycleLocalAngleDemand.paired_angle_demand";
    private const string FlatDeclaration =
        "D5/S3/Geometry/Hyperideal/FourCycleLocalAngleDemand.flat_transverse_gap";
    private const string ChosenFlatDeclaration =
        "D5/S3/Geometry/Hyperideal/FourCycleLocalAngleDemand.flat_transverse_gap_of_chosen";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Local angle demand and flat-branch length gaps for paired hyper-ideal lengths.",
        H("Paired local angle demand and flat transverse gaps"),
        Blocks(
            Paragraph(Text("Use the local order (12,13,14,34,24,23) and the exact cosine "
                + "function from FourCycleEnvelopes. The tuple is (r,a,b,o,a,b). "
                + "The angle result assumes three genuine angle ranges. The two "
                + "flat length results use raw cosine inequalities.")),
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
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("paired-fourcycle-flat-transverse-gap"),
                DeclarationHandle.Create(FlatDeclaration),
                H("The selected transverse length is larger"),
                StatementSource.FromAuthor(F.Disp(FlatStatement())),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For r,a,b,o>1, selecting the a,a transverse pi "
                        + "pair forces a>b and a-b at least sqrt((r+1)(o+1)). Swapping "
                        + "a and b gives the opposite choice.")),
                    Paragraph(Text("The squared gap follows from the axial cosine; "
                        + "the direction follows from the difference of the transverse "
                        + "numerators and positivity of their common denominator.")),
                    Paragraph(Text("These are implications between raw cosine values. "
                        + "They do not construct a flat tetrahedron, a face pairing, "
                        + "or a global zero-curvature assignment."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("paired-fourcycle-one-premise-flat-transverse-gap"),
                DeclarationHandle.Create(ChosenFlatDeclaration),
                H("One transverse raw cosine forces the length gap"),
                StatementSource.FromAuthor(F.Disp(ChosenFlatStatement())),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For r,a,b,o>1, the single raw-cosine inequality "
                        + "cosine(a,b,r,a,b,o)<=-1 forces a>b and "
                        + "sqrt((r+1)(o+1))<=a-b. No axial or opposite transverse "
                        + "cosine premise is needed.")),
                    Paragraph(Text("The negative selected numerator forces a>b and "
                        + "L>0. Its numerator-square factorization then forces "
                        + "M<=0, which gives the squared gap and its positive branch.")),
                    Paragraph(Text("This is an implication for raw cosine values and "
                        + "positive real lengths; it does not construct a flat "
                        + "tetrahedron or a global zero-curvature assignment."))),
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

    private static Formula FlatStatement()
    {
        var r = F.Id("r"); var a = F.Id("a");
        var b = F.Id("b"); var o = F.Id("o");
        var ct = Call("cosine", r, a, b, o, a, b);
        var ca = Call("cosine", a, b, r, a, b, o);
        var cb = Call("cosine", b, a, r, b, a, o);
        var premise = And(
            Lt(F.D(1), r), Lt(F.D(1), a), Lt(F.D(1), b), Lt(F.D(1), o),
            Le(F.D(1), ct), Le(ca, F.Seq(F.Minus, F.D(1))), Le(F.D(1), cb));
        var conclusion = And(
            Lt(b, a),
            Le(Call("sqrt", F.Seq(F.Open, r, F.Plus, F.D(1), F.Close,
                F.Cdot, F.Sp, F.Open, o, F.Plus, F.D(1), F.Close)),
                F.Seq(a, F.Minus, b)));
        var real = new Formula.NamedConstant(FormulaIdentifier.Create("Real"));
        Formula.BoundVariable[] binders = [.. new[] { "r", "a", "b", "o" }
            .Select(name => new Formula.BoundVariable(FormulaIdentifier.Create(name), real))];
        return new Formula.BindMany(FormulaQuantifier.ForAll, [.. binders],
            new Formula.Logic(premise, FormulaLogicOperator.Implies, conclusion));
    }

    private static Formula ChosenFlatStatement()
    {
        var r = F.Id("r"); var a = F.Id("a");
        var b = F.Id("b"); var o = F.Id("o");
        var ca = Call("cosine", a, b, r, a, b, o);
        var premise = And(
            Lt(F.D(1), r), Lt(F.D(1), a), Lt(F.D(1), b), Lt(F.D(1), o),
            Le(ca, F.Seq(F.Minus, F.D(1))));
        var conclusion = And(
            Lt(b, a),
            Le(Call("sqrt", F.Seq(F.Open, r, F.Plus, F.D(1), F.Close,
                F.Cdot, F.Sp, F.Open, o, F.Plus, F.D(1), F.Close)),
                F.Seq(a, F.Minus, b)));
        var real = new Formula.NamedConstant(FormulaIdentifier.Create("Real"));
        Formula.BoundVariable[] binders = [.. new[] { "r", "a", "b", "o" }
            .Select(name => new Formula.BoundVariable(FormulaIdentifier.Create(name), real))];
        return new Formula.BindMany(FormulaQuantifier.ForAll, [.. binders],
            new Formula.Logic(premise, FormulaLogicOperator.Implies, conclusion));
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
