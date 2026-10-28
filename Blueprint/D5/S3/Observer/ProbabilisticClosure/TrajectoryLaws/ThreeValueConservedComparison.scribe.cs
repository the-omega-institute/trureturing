using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws;

internal sealed class ThreeValueConservedComparisonDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/ThreeValueConservedComparison.";

    public DocumentDefinition Create()
    {
        Formula jset = F.Id("J"), real = F.Id("Real");
        Formula row = Seq(jset, To, Sp, real);
        Formula matrix = Seq(jset, To, Sp, jset, To, Sp, real);
        Formula pi = F.Id("pi"), b = F.Id("B"), u = F.Id("u"), v = F.Id("v");
        Formula t = F.Id("t"), table = F.Id("T"), w = F.Id("w");
        Formula ah = F.Id("Ah"), vh = F.Id("vh"), tauh = F.Id("tauh");
        Formula i = F.Id("i"), j = F.Id("j");
        Formula h = Apply(F.Id("C"), table);
        Formula originalEnergy = Energy(pi, b, u);
        Formula mass = SumOver("i", Seq(Apply(pi, i), Cdot, Sp,
            Abs(Seq(Apply(u, i), Minus, Apply(w, i)))));
        Formula cost = SumOver("i", Seq(Apply(pi, i), Cdot, Sp, Fraction(D(1), D(2)), Cdot, Sp,
            SumOver("j", Abs(Seq(Apply(b, i, j), Minus, Apply(h, i, j))))));
        Formula premises = And(
            All("i", jset, Seq(D(0), Lt, Apply(pi, i))),
            Seq(SumOver("i", Apply(pi, i)), Eq, D(1)),
            All("i", jset, All("j", jset, Seq(D(0), Le, Sp, Apply(b, i, j)))),
            All("i", jset, Seq(SumOver("j", Apply(b, i, j)), Eq, D(1))),
            Balance(pi, b), Box(u), Box(v), Seq(D(0), Lt, t));
        Formula conclusions = And(
            Seq(Apply(F.Id("piOf"), table), Eq, pi),
            Seq(ah, Eq, Apply(F.Id("identity"), jset)),
            Seq(vh, Eq, v), Seq(tauh, Eq, pi), Box(w), Box(vh),
            All("i", jset, All("j", jset, Seq(D(0), Le, Sp, Apply(h, i, j)))),
            All("i", jset, Seq(SumOver("j", Apply(h, i, j)), Eq, D(1))),
            Balance(pi, h),
            All("j", jset, Seq(SumOver("i", Seq(Apply(pi, i), Cdot, Sp, Apply(h, i, j))),
                Eq, Apply(pi, j))),
            All("i", jset, All("j", jset, Seq(D(0), Lt, Apply(h, i, j), Rightarrow, Sp,
                Apply(w, i), Eq, Apply(w, j)))),
            Seq(mass, Le, Sp, t),
            Seq(cost, Le, Sp, Fraction(Seq(D(2), Cdot, Sp, originalEnergy), Power(t, D(2)))),
            Seq(Energy(pi, h, w), Eq, D(0)));
        Formula statement = All("pi", row, All("B", matrix, All("u", row,
            All("v", row, All("t", real, Seq(Open, premises, Close, Rightarrow, Sp,
                Ex("T", Apply(F.Id("StationaryTable"), jset), Ex("w", row,
                Ex("Ah", matrix, Ex("vh", row, Ex("tauh", row, conclusions)))))))))));
        return DocumentDefinition.Create(ScribeNode.Create(
            "Three real emission values admit one conserved reversible comparison with the same stationary row and simultaneous displacement and total-variation bounds.",
            H("A conserved comparison for three emission values"), Blocks(
                Paragraph(Text("Let J={0,1,2}. All table entries and emission parameters are arbitrary real numbers. The probability row pi is strictly positive and sums to one. The matrix B is nonnegative, each row sums to one, and pi(i)B(i,j)=pi(j)B(j,i). Both u and v belong to the closed interval [1/3,2/5] at every label. The original second update matrix is the identity and its intermediate row is pi.")),
                Paragraph(Text("StationaryTable is the existing finite stationary-table structure. In the formula, piOf(T) is its probability row and C(T) its stochastic matrix. identity(J)(i,j) is one when i=j and zero otherwise. Every sum is over the displayed finite label set J. The energy expression is J(u)=(1/2) sum_i sum_j pi(i)B(i,j)(u(i)-u(j))^2. The comparison uses the same pi, keeps v unchanged, and keeps the second update equal to the identity.")),
                Describe.Lean(DescribeId.Create("three-value-conserved-comparison"),
                    DeclarationHandle.Create(Prefix + "three_value_conserved_comparison"),
                    H("One table satisfies every bound for every positive threshold"),
                    StatementSource.FromAuthor(Disp(statement)), AssessedProvenance.FromRepo(), Blocks(
                        Paragraph(Text("Sort the three emission values, including ties, and cut precisely at adjacent gaps greater than t. Each resulting block contains at most two uncut gaps, so its span is at most 2t. Replace every emission in a block by the midpoint of its smallest and largest values. The midpoint stays in [1/3,2/5], and each label moves by at most t. Any two labels assigned different midpoints have original separation at least t.")),
                        Paragraph(Text("For each row i, remove transitions to labels with a different new emission value and add their total mass to the diagonal entry. All retained off-diagonal entries remain unchanged. Nonnegativity and the row sum are preserved. Detailed balance is inherited within each new-emission class; between classes both directions vanish. Summing detailed balance against a stochastic row proves that the stationary row remains exactly pi.")),
                        Paragraph(Text("Write l(i) for the removed mass in row i. The diagonal gains l(i), the deleted coordinates lose total mass l(i), and the remaining coordinates do not change. Therefore q(i)=(1/2) sum_j |B(i,j)-C(T)(i,j)| equals l(i). Every deleted edge has squared original emission separation at least t^2. Multiplication by its nonnegative flow pi(i)B(i,j) and summation gives t^2 sum_i pi(i)q(i) at most 2J(u). Dividing by the positive t^2 gives the stated bound. This estimate and the displacement bound refer to the same constructed table.")),
                        Paragraph(Text("Every positive comparison edge joins equal new emissions. Every summand of its emission energy is consequently zero. The construction includes tied emissions, both closed endpoints, arbitrary positive weights, self-loops, disconnected and reducible chains, and heterogeneous v. It assumes no irreducibility, spectral gap, aperiodicity, or lower bound on the positive weights."))),
                    DescribeRole.Theorem),
                Paragraph(Text("The comparison is an existence statement about mathematical tables. It supplies no physical implementation, sampling algorithm, observation interface, full-law distance estimate, or history-risk transport theorem.")))));
    }

    private static Formula Apply(Formula f, params Formula[] args)
    {
        var parts = new List<Formula> { f, Open };
        for (var k = 0; k < args.Length; k++)
        {
            if (k > 0) parts.Add(Comma);
            parts.Add(args[k]);
        }
        parts.Add(Close);
        return Seq(parts.ToArray());
    }
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, F.Id(name), Colon, type, Comma, body);
    private static Formula Ex(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, F.Id(name), Colon, type, Comma, body);
    private static Formula SumOver(string name, Formula body) =>
        Seq(Sum, Underscore, Grp(Seq(F.Id(name), InMacro, Sp, F.Id("J"))), Sp, Grp(body));
    private static Formula Power(Formula value, Formula exponent) => Seq(Open, value, Close, Caret, Grp(exponent));
    private static Formula Abs(Formula value) => Seq(Lvert, Sp, value, Rvert, Sp);
    private static Formula Fraction(Formula n, Formula d) => Seq(Frac, Grp(n), Grp(d));
    private static Formula And(params Formula[] clauses)
    {
        var parts = new List<Formula>();
        for (var k = 0; k < clauses.Length; k++)
        {
            if (k > 0) parts.Add(Land);
            parts.Add(Seq(Open, clauses[k], Close));
        }
        return Seq(parts.ToArray());
    }
    private static Formula Box(Formula f) => All("i", F.Id("J"), And(
        Seq(Fraction(D(1), D(3)), Le, Sp, Apply(f, F.Id("i"))),
        Seq(Apply(f, F.Id("i")), Le, Sp, Fraction(D(2), D(5)))));
    private static Formula Balance(Formula pi, Formula b) => All("i", F.Id("J"),
        All("j", F.Id("J"), Seq(Apply(pi, F.Id("i")), Cdot, Sp, Apply(b, F.Id("i"), F.Id("j")),
            Eq, Apply(pi, F.Id("j")), Cdot, Sp, Apply(b, F.Id("j"), F.Id("i")))));
    private static Formula Energy(Formula pi, Formula b, Formula u) =>
        Seq(Fraction(D(1), D(2)), Cdot, Sp, SumOver("i", SumOver("j", Seq(
            Apply(pi, F.Id("i")), Cdot, Sp, Apply(b, F.Id("i"), F.Id("j")), Cdot, Sp,
            Power(Seq(Apply(u, F.Id("i")), Minus, Apply(u, F.Id("j"))), D(2))))));
}
