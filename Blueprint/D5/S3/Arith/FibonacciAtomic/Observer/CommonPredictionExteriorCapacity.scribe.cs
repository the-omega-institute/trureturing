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
        "The external teacher discrepancy fits inside every actual reservoir mass class.", H("Exterior Discrepancy and Reservoir Capacity"), Blocks(
            Paragraph(Text("For each reduced word, exteriorSelector selects a label with maximal total teacher votes. Outside the reservoir, Ez(m,z,i) is the sum of left-teacher error minus right-teacher error over words with z rare symbols. The subtraction compares the two teachers at the same prefix coordinate i.")),
            Paragraph(Text("Write L(m) for the sum of the positive prefix slices of length m-1 through floor(m/3). The complete exterior discrepancy polynomial is 2 X squared times (2+X), multiplied by ((2+3X)L(m) minus 4((2+3X)^(m-1)-(2+X)^(m-1))). Its coefficient at z is Ez(m,z,i), independently of i.")),
            Paragraph(Text("Positive prefix fibers split according to one endpoint bit. Coin balance halves each fiber uniformly. Pairing the anchor configurations then gives the same signed discrepancy for each teacher. The zero-prefix fiber cancels separately.")),
            Paragraph(Text("The binomial weights choose(j,k) 2^k have total 3^j and first moment 2j 3^(j-1). A tail estimate at floor(m/3), together with tail growth, bounds the discrepancy coefficients between minus the reservoir coefficients and the reservoir coefficients. The cases m=1 and m=2 are included.")),
            Paragraph(Text("The reservoir and discrepancy coefficients are both twice integers. Their half difference is nonnegative and does not exceed the full reservoir size. Therefore every positive m and every z admit an integer split with exterior discrepancy plus twice the split size minus the reservoir size equal to zero.")),
            Describe.Lean(DescribeId.Create("exterior-capacity"),
                DeclarationHandle.Create("D5/S3/Arith/FibonacciAtomic/Observer/CommonPredictionExteriorCapacity.actual_ez_identity"),
                H("Actual exterior discrepancy coefficients"), StatementSource.FromAuthor(ResultFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Summing the two coin fibers yields the paired anchor polynomial. The low, middle and high prefix-count regions then sum to the displayed exterior polynomial. Coefficient extraction preserves the signed difference of the two actual error counts. The coefficient capacity estimate ensures that a common reservoir split exists in every mass class."))), DescribeRole.Theorem))));

    private static Formula ResultFormula() =>
        All("m", V("Nat"), All("z", V("Nat"),
            Imp(Seq(D(0), Sp, Lt, Sp, V("m")),
                All("i", Call("Fin", V("m")),
                    Eq(Call("Ez", V("m"), V("z"), V("i")),
                        Call("coeff", Call("Eformula", V("m")), V("z")))))));
}
