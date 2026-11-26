using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaPntBounds;

internal sealed class MobiusShortAverageDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Weil/ZetaPntBounds/MobiusShortAverage";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Ordinary Möbius prefixes from a zero-free half-plane",
        H("Short averages of the first Riesz sum"),
        Blocks(Describe.Lean(
            DescribeId.Create("ordinary-mobius-prefix-zero-free"),
            DeclarationHandle.Create(Owner + ".ordinary_mobius_prefix_of_zero_free"),
            H("Prefix bounds up to any positive exponent slack"),
            StatementSource.FromAuthor(Estimate()), AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("The predicate Z(b) says that the Riemann zeta function is nonzero "
                    + "at every complex z with Re z>b and z≠1. The ordinary prefix M(N) is "
                    + "the sum of μ(n) over the integers 1≤n≤N.")),
                Paragraph(Text("For x=N and h=sqrt(x), difference the first Riesz sums "
                    + "at x+h and x and divide by h. The contribution of n≤N is M(N). "
                    + "There are at most h remaining integers, whose normalized weights "
                    + "lie in [0,1]. Since |μ(n)|≤1, the error is at most h.")),
                Paragraph(Text("The short secant of the Perron kernel has a single-denominator "
                    + "bound obtained by differentiating y^(s+1)/(s+1) in the positive real "
                    + "cutoff y. Bounding the two endpoint values separately gives an "
                    + "independent quadratic-denominator estimate.")),
                Paragraph(Text("The removable reciprocal of zeta is analytic in Re s>b "
                    + "and has growth O((1+|Im s|)^δ) on every fixed half-plane strictly to "
                    + "its right. The two short-kernel estimates interpolate to an integrable "
                    + "majorant proportional to (1+|Im s|)^(−1−δ). This controls the vertical "
                    + "integrals and the vanishing horizontal integrals during the line shift.")),
                Paragraph(Text("Choose δ=min(e/3,1/4) and move to Re s=b+δ. The kernel "
                    + "majorant contributes (x+h)^(b+δ)((x+h)/h)^(2δ), bounded by "
                    + "a constant times x^(b+2δ). The prefix error h is within the same "
                    + "target exponent. The RH case takes b=1/2, the classical exponent "
                    + "with arbitrary slack recorded by Soundararajan in equation (1) of "
                    + "Partial sums of the Möbius function."))),
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

    private static Formula Estimate()
    {
        var edge = F.Id("b");
        var slack = F.Id("e");
        var order = F.Id("N");
        var bound = F.Id("C");
        var prefix = new Formula.FunctionCall(FormulaIdentifier.Create("M"), [order]);
        var zeroFree = new Formula.FunctionCall(FormulaIdentifier.Create("Z"), [edge]);
        var range = And(Le(new Formula.Fraction(F.D(1), F.D(2)), edge), Lt(edge, F.D(1)));
        var estimate = Le(new Formula.Absolute(prefix), Multiply(bound, new Formula.Power(order, Add(edge, slack))));
        var orders = Bind(FormulaQuantifier.ForAll, "N", "N", Imp(Le(F.D(1), order), estimate));
        var constants = Bind(FormulaQuantifier.Exists, "C", "R", And(Lt(F.D(0), bound), orders));
        return F.Disp(Bind(FormulaQuantifier.ForAll, "b", "R",
            Imp(And(range, zeroFree),
                Bind(FormulaQuantifier.ForAll, "e", "R", Imp(Lt(F.D(0), slack), constants)))));
    }
}
