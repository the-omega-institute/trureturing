using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaPntBounds;

internal sealed class MobiusEnergyPointwiseDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Weil/ZetaPntBounds/MobiusEnergyPointwise";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Pointwise Möbius bounds from weighted energy",
        H("Persistence of the reciprocal-weighted prefix"),
        Blocks(Describe.Lean(
            DescribeId.Create("unweighted-mobius-prefix-power-bound"),
            DeclarationHandle.Create(Owner + ".unweighted_mobius_prefix_power_bound"),
            H("Ordinary Möbius prefixes under a zero-free half-plane"),
            StatementSource.FromAuthor(PrefixBound()), AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("The zero-free condition Z(t) means ζ(z)≠0 for every complex "
                    + "z with Re(z)>t and z≠1. M(N) is the ordinary unweighted finite sum of "
                    + "the Möbius function over integers from 1 to N.")),
                Paragraph(Text("Let S(x) be the sum of μ(n)/n over integers 1≤n≤x. At an "
                    + "integer N, every subsequent change has size at most 1/N. A height "
                    + "H=|S(N)| therefore forces magnitude at least H/2 throughout the "
                    + "real interval from N to N+HN/2. This covers intervals shorter than "
                    + "one integer step.")),
                Paragraph(Text("Compare the energy on that interval to the finite integral "
                    + "of S(x)² x^(−α) on x>1. This bounds H³N^(1−α) by the energy times "
                    + "a constant. Discrete partial summation gives M(N)=NS(N)−Σ S(k) "
                    + "over 1≤k<N. Comparing the resulting decreasing power sum with its "
                    + "integral gives the exponent (2+α)/3."))),
            DescribeRole.Theorem))));

    private static Formula Bind(FormulaQuantifier quantifier, string name, string domain, Formula body) =>
        new Formula.Bind(quantifier, FormulaIdentifier.Create(name), F.Seq(F.Mathbb, F.Grp(F.Id(domain))), body);

    private static Formula Le(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);

    private static Formula Lt(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula Imp(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula PrefixBound()
    {
        var t = F.Id("t");
        var a = F.Id("a");
        var c = F.Id("C");
        var n = F.Id("N");
        var zeroFree = new Formula.FunctionCall(FormulaIdentifier.Create("Z"), [t]);
        var sum = new Formula.FunctionCall(FormulaIdentifier.Create("M"), [n]);
        var half = new Formula.Fraction(F.D(1), F.D(2));
        var exponent = new Formula.Fraction(Add(F.D(2), a), F.D(3));
        var constraints = And(And(Le(half, t), Lt(t, F.D(1))),
            And(zeroFree, And(Lt(Subtract(Multiply(F.D(2), t), F.D(1)), a), Lt(a, F.D(1)))));
        var allPrefixes = Bind(FormulaQuantifier.ForAll, "N", "N",
            Imp(Le(F.D(1), n), Le(new Formula.Absolute(sum), Multiply(c, new Formula.Power(n, exponent)))));
        var bound = Bind(FormulaQuantifier.Exists, "C", "R", And(Lt(F.D(0), c), allPrefixes));
        return F.Disp(Bind(FormulaQuantifier.ForAll, "t", "R",
            Bind(FormulaQuantifier.ForAll, "a", "R", Imp(constraints, bound))));
    }
}
