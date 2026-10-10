using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic.Observer;

internal sealed class CommonPredictionExteriorCapacityDocument : IScribeDocumentDefinition
{
    private static Formula V(string name) => F.Id(name);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(name))), [.. args]);
    private static Formula Par(Formula body) => Seq(Left, Open, body, Right, Close);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Par(Seq(V(name), Colon, Sp, type)), Comma, Sp, body);
    private static Formula Ex(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, Par(Seq(V(name), Colon, Sp, type)), Comma, Sp, body);
    private static Formula Eq(Formula a, Formula b) => Seq(a, Sp, F.Eq, Sp, b);
    private static Formula Le(Formula a, Formula b) => Seq(a, Sp, F.Le, Sp, b);
    private static Formula And(Formula a, Formula b) => Seq(Par(a), Sp, Land, Sp, Par(b));
    private static Formula Imp(Formula a, Formula b) => Seq(Par(a), Sp, Implies, Sp, Par(b));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "One deterministic majority classifier balances all teachers in every rare-count class.", H("Exterior Discrepancy and Common Balance"), Blocks(
            Paragraph(Text("For each reduced word, exteriorSelector selects a label with maximal total teacher votes. Outside the reservoir, Ez(m,z,i) is the sum of left-teacher error minus right-teacher error over words with z rare symbols. The subtraction compares the two teachers at the same prefix coordinate i.")),
            Paragraph(Text("Write L(m) for the sum of the positive prefix slices of length m-1 through floor(m/3). The complete exterior discrepancy polynomial is 2 X squared times (2+X), multiplied by ((2+3X)L(m) minus 4((2+3X)^(m-1)-(2+X)^(m-1))). Its coefficient at z is Ez(m,z,i), independently of i.")),
            Paragraph(Text("Positive prefix fibers split according to one endpoint bit. Coin balance halves each fiber uniformly. Pairing the anchor configurations then gives the same signed discrepancy for each teacher. The zero-prefix fiber cancels separately.")),
            Paragraph(Text("The reservoir and discrepancy polynomials have even integer coefficients; coefficient extraction identifies their halves with the capacity sequences. The two-sided capacity bound makes the required reservoir split a legal integer in every rare-count class.")),
            Paragraph(Text("In each rare-count class choose a reservoir subset of the required size. A single classifier labels this subset two and its reservoir complement zero, and uses the exterior majority selector elsewhere. Both reservoir labels maximize votes. Prefix permutation symmetry equalizes positions, and the split equation equalizes the two layers. This gives an existence construction, with no computable or lexicographic selection rule asserted.")),
            Describe.Lean(DescribeId.Create("exterior-capacity"),
                DeclarationHandle.Create("D5/S3/Arith/FibonacciAtomic/Observer/CommonPredictionExteriorCapacity.uniform_mass_balanced"),
                H("One majority classifier with classwise equal errors"), StatementSource.FromAuthor(ResultFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Summing the coin fibers and extracting coefficients gives the actual exterior error difference. The capacity estimate then supplies each reservoir split. The same classifier is a pointwise majority choice and balances both layers at every position, simultaneously for all rare-count classes."))), DescribeRole.Theorem))));

    private static Formula ResultFormula()
    {
        var input = Call("Input", Seq(V("m"), Plus, D(3)));
        var left = Call("errorCount", V("z"), V("false"), V("i"), V("f"));
        var balance = All("z", V("Nat"), All("i", Call("Fin", V("m")),
            All("j", Call("Fin", V("m")),
                And(Eq(left, Call("errorCount", V("z"), V("false"), V("j"), V("f"))),
                    Eq(left, Call("errorCount", V("z"), V("true"), V("j"), V("f")))))));
        var majority = All("x", input, All("c", Call("Fin", D(3)),
            Le(Call("actualVotes", V("x"), V("c")),
                Call("actualVotes", V("x"), Call("f", V("x"))))));
        return All("m", V("Nat"), Imp(Seq(D(0), Sp, Lt, Sp, V("m")),
            Ex("f", Call("Function", input, Call("Fin", D(3))), And(majority, balance))));
    }
}
