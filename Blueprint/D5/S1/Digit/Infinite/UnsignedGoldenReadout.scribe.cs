using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Digit.Infinite;

internal sealed class UnsignedGoldenReadoutDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Digit/Infinite/UnsignedGoldenReadout.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Unsigned golden expansions on infinite legal digits.",
        H("Unsigned Golden Readout"),
        Blocks(
            Paragraph(Text("Let L be SuccessorContinuity.LegalDigits: Boolean streams x with no "
                + "adjacent ones, carrying the subspace topology inherited from the product of "
                + "discrete Boolean spaces. Put phi=(1+sqrt(5))/2 and r=phi inverse. Positions "
                + "start at zero; the weight of position k is r to the power k+1. All sums below "
                + "are infinite real sums. The symbols u and v denote the existing legal streams "
                + "101010... and 010101... respectively.")),
            Node("U", "The unsigned series", ReadoutFormula(), DescribeRole.Definition,
                "The coefficient is one for a true digit and zero for a false digit. Thus the "
                + "first coefficient has weight r, with no alternating sign."),
            Node("zeroName", "The zero name", ZeroFormula(), DescribeRole.Definition,
                "Every digit of zeroName is false."),
            Node("singleName", "A single occupied position", SingleFormula(), DescribeRole.Definition,
                "The only true digit of singleName is position zero, so its sequence is 1000...."),
            Node("unsigned_golden_readout", "Continuous interval readout and prefix estimate",
                ResultFormula(), DescribeRole.Theorem,
                "Every legal stream gives a summable series. Its range is exactly the closed "
                + "unit interval, and the readout is continuous in the inherited topology. For "
                + "every natural n, including zero, agreement at each position k<n bounds the "
                + "absolute difference of the readouts by r to the power n. The zero name and u "
                + "realize the endpoints. The distinct names singleName and v both read r."),
            Paragraph(Text("To bound the range, group positions 2k and 2k+1. Legality permits at "
                + "most one occupied position in each pair. Its contribution is at most "
                + "r(r squared) to the power k, whose sum is one because r squared+r=1. "
                + "The alternating stream u attains this bound.")),
            Paragraph(Text("For a real t in [0,1], start with residual t. At a residual z, choose "
                + "digit one when z>r and replace z by (z-r)/r; otherwise choose zero and replace "
                + "z by z/r. Every residual stays in [0,1]. A one leaves a residual at most r, "
                + "so the next digit is zero. The first n terms sum to t minus r to the power n "
                + "times the nth residual. This remainder tends to zero, proving surjectivity, "
                + "including the boundary points.")),
            Paragraph(Text("Deleting n initial digits leaves another legal stream. Splitting the "
                + "series gives the common prefix sum plus r to the power n times the shifted "
                + "readout. Both shifted readouts lie in [0,1], giving the prefix estimate. "
                + "Continuity also follows from the summable geometric bound on the continuous "
                + "coordinate functions. A leading zero scales the tail readout by r; a leading "
                + "10 sends it to r+r squared times the tail readout. These branch intervals "
                + "are [0,r] and [r,1], and cover [0,1].")),
            Paragraph(Text("The endpoint and coincident-name values follow by summing the even "
                + "and odd geometric subseries. In particular U(u)=1 and U(v)=r, whereas the "
                + "single occupied position also has value r. These are unsigned beta expansions; "
                + "no uniqueness of names or mathematical novelty is asserted.")))));

    private static DocumentBlock Node(string name, string title, Formula formula,
        DescribeRole role, string prose) => Describe.Lean(
        DescribeId.Create("unsigned-golden-readout-" + name.Replace("_", "-").ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
        AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role);

    private static Formula ReadoutFormula()
    {
        Formula x = F.Id("x"), k = F.Id("k");
        return Disp(All("x", F.Id("L"), Eq(Call("U", x),
            Call("tsum", Lambda("k", F.Id("Nat"), Term(x, k))))));
    }

    private static Formula ZeroFormula() => Disp(All("k", F.Id("Nat"),
        Eq(Call("val", F.Id("zeroName"), F.Id("k")), F.Id("false"))));

    private static Formula SingleFormula() => Disp(All("k", F.Id("Nat"),
        Eq(Call("val", F.Id("singleName"), F.Id("k")),
            Call("decide", Eq(F.Id("k"), D(0))))));

    private static Formula ResultFormula()
    {
        Formula x = F.Id("x"), y = F.Id("y"), n = F.Id("n"), k = F.Id("k");
        Formula agree = All("k", F.Id("Nat"), Implies(Lt(k, n),
            Eq(Call("val", x, k), Call("val", y, k))));
        Formula estimate = All("n", F.Id("Nat"), All("x", F.Id("L"), All("y", F.Id("L"),
            Implies(Seq(Open, agree, Close),
                Le(Call("abs", Sub(Call("U", x), Call("U", y))), Pow(F.Id("r"), n))))));
        return Disp(And(
            All("x", F.Id("L"), Call("Summable", Lambda("k", F.Id("Nat"), Term(x, k)))),
            Eq(Call("range", F.Id("U")), Call("Icc", D(0), D(1))),
            Call("Continuous", F.Id("U")), estimate,
            Eq(Call("U", F.Id("zeroName")), D(0)), Eq(Call("U", F.Id("u")), D(1)),
            Seq(F.Id("singleName"), Sp, Neq, Sp, F.Id("v")),
            Eq(Call("U", F.Id("singleName")), F.Id("r")), Eq(Call("U", F.Id("v")), F.Id("r"))));
    }

    private static Formula Term(Formula x, Formula k) => Mul(
        Call("if", Call("val", x, k), D(1), D(0)), Pow(F.Id("r"), Add(k, D(1))));
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(F.Id(name), [.. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Lambda(string name, Formula type, Formula body) =>
        Seq(Open, F.Id(name), Colon, type, Sp, Mapsto, Sp, body, Close);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(a, b);
    private static Formula Implies(Formula a, Formula b) => Seq(Open, a, Sp, Rightarrow, Sp, b, Close);
    private static Formula And(params Formula[] terms) => Seq(terms.SelectMany((t, i) =>
        i == 0 ? new[] { Open, t, Close } : new[] { Sp, Land, Sp, Open, t, Close }).ToArray());
}
