using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic;

internal sealed class PrimeGcdHorizonDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciAtomic/PrimeGcdHorizon.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The least Fibonacci zero rank determines the signed prime gcd prefix horizon, attained on bounded nonnegative sources.",
        H("Sharp Prime Gcd Observation Horizon"),
        Blocks(
            Paragraph(Text("N includes zero and Z denotes the signed integers. F(0)=0 and F(1)=1. For a natural modulus p, r(p) is "
                + "the infimum of the positive indices t such that p divides F(t), with infimum zero "
                + "when that set is empty. For every prime p this set is nonempty, "
                + "3 <= r(p) <= p+1, and B(p) is at least two. Subtraction in N is truncated.")),
            Node("observation", "Actual nonnegative source observation", ObservationFormula(),
                "A source consists of independent natural coordinates a,b. Its initial recurrence "
                + "state is (n,z)=(2a+3b,3a+5b), with y(0)=n, y(1)=z and "
                + "y(k+2)=y(k+1)+y(k). Thus the displayed observation is the actual recurrence "
                + "at time k, not merely a phase label. All source coordinates, including zero, are allowed.",
                DescribeRole.Definition),
            Node("signedObservation", "Signed initial-state observation", SignedObservationFormula(),
                "The initial coordinates n,z are arbitrary signed integers, not nonnegative source "
                + "coordinates. Y(0;n,z)=n. For positive natural k, Y(k;n,z)=F(k-1)n+F(k)z, "
                + "so Y(1;n,z)=z and Y(k+2;n,z)=Y(k+1;n,z)+Y(k;n,z). "
                + "Its prime gcd reading is gcd(|Y(k;n,z)|,p), a natural number. "
                + "Only positive times occur in the recovery clauses.", DescribeRole.Definition),
            Node("horizon", "The full-orbit correction", HorizonFormula(),
                "The function ite takes its second argument when its first argument holds, "
                + "and its third argument otherwise. Thus B(p)=r(p)-1 when r(p)=p+1, "
                + "and B(p)=r(p) otherwise. For primes, the latter case is exactly r(p)<p+1.",
                DescribeRole.Definition),
            Node("sharp_prime_gcd_horizon", "Universal recovery and attained first separation", ResultFormula(),
                "For every prime p and arbitrary signed integer initial pairs (n,z),(n2,z2), "
                + "agreement of their absolute prime gcd readings at times 1 through B(p) implies "
                + "agreement at every positive time. For arbitrary natural source coordinates a,b,c,d, "
                + "agreement of the prime gcd "
                + "readings at times 1 through B(p) implies agreement at every positive time. "
                + "Conversely, four coordinates smaller than p can be chosen so that the readings "
                + "agree at every positive time smaller than B(p) and differ exactly at B(p). "
                + "No common initial value, known common content, or primitive-source restriction "
                + "is assumed. All three conjuncts include p=2 and p=5.", DescribeRole.Theorem),
            Paragraph(Text("Over the field Z/pZ, the Fibonacci step (u,v) -> (v,u+v) is invertible. "
                + "Its second-coordinate reading at time t is F(t)u+F(t+1)v. The nonzero kernel "
                + "vector (F(t+1),-F(t)) defines a projective direction. Two zero readings of a "
                + "nonzero state have time difference divisible by r(p). The r(p) distinct kernel "
                + "directions therefore occupy an orbit inside the p+1 directions of the projective line. "
                + "When that orbit is proper, its last phase and an outside direction first differ "
                + "at positive time r(p). When the orbit is full, the last two phases first differ "
                + "at r(p)-1. The zero state is identified by the first two readings, so removing "
                + "the primitive-source restriction does not enlarge the horizon.")),
            Paragraph(Text("For signed initial state (n,z), the residue of Y(k;n,z) is the field "
                + "reading F(k-1)n+F(k)z at time k-1. A signed integer has zero residue modulo p "
                + "exactly when p divides its absolute value. Thus the same field-state estimate "
                + "determines the absolute gcd readings without a sign or nonnegativity assumption.")),
            Paragraph(Text("For any two prescribed residue states (n,z), the inverse matrix "
                + "[[5,-3],[-3,2]] gives residue source coordinates. Taking their representatives "
                + "between zero and p-1 yields actual nonnegative sources. Multiplication by "
                + "[[2,3],[3,5]] returns exactly the prescribed residue state. A prime gcd is p "
                + "at a zero residue and 1 otherwise, so this transport preserves every gcd reading "
                + "and the exact first separation time.")))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create("prime-gcd-horizon-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role);

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. args]);
    private static Formula Par(Formula value) => Seq(Open, value, Close);
    private static Formula Equal(Formula left, Formula right) => Seq(left, Sp, Eq, Sp, right);
    private static Formula Both(params Formula[] values) => Seq(values.SelectMany((value, index) =>
        index == 0 ? new[] { Par(value) } : new[] { Sp, Land, Sp, Par(value) }).ToArray());
    private static Formula AllN(string names, Formula body) =>
        Seq(Forall, Sp, Names(names), Sp, InMacro, Sp, F.Id("N"), Comma, Sp, body);
    private static Formula AllZ(string names, Formula body) =>
        Seq(Forall, Sp, Names(names), Sp, InMacro, Sp, F.Id("Z"), Comma, Sp, body);
    private static Formula Names(string names) => Seq(names.Split(',').SelectMany((name, index) =>
        index == 0 ? new[] { F.Id(name) } : new[] { Comma, F.Id(name) }).ToArray());
    private static Formula ImpliesFormula(Formula premise, Formula conclusion) =>
        Seq(Par(premise), Sp, Implies, Sp, Par(conclusion));
    private static Formula GcdReading(Formula time, string left, string right) =>
        Call("gcd", Call("y", time, F.Id(left), F.Id(right)), F.Id("p"));
    private static Formula SignedGcdReading(Formula time, string left, string right) =>
        Call("gcd", Call("natAbs", Call("Y", time, F.Id(left), F.Id(right))), F.Id("p"));
    private static Formula ObservationFormula() => Disp(AllN("k,a,b", Equal(
        Call("y", F.Id("k"), F.Id("a"), F.Id("b")),
        Add(Multiply(Call("F", Add(F.Id("k"), D(3))), F.Id("a")),
            Multiply(Call("F", Add(F.Id("k"), D(4))), F.Id("b"))))));
    private static Formula SignedObservationFormula() => Disp(AllN("k", AllZ("n,z", Equal(
        Call("Y", F.Id("k"), F.Id("n"), F.Id("z")),
        Call("ite", Equal(F.Id("k"), D(0)), F.Id("n"),
            Add(Multiply(Call("F", Subtract(F.Id("k"), D(1))), F.Id("n")),
                Multiply(Call("F", F.Id("k")), F.Id("z"))))))));
    private static Formula HorizonFormula() => Disp(AllN("p", Equal(Call("B", F.Id("p")),
        Call("ite", Equal(Call("r", F.Id("p")), Add(F.Id("p"), D(1))),
            Subtract(Call("r", F.Id("p")), D(1)), Call("r", F.Id("p"))))));
    private static Formula ResultFormula()
    {
        Formula time = F.Id("k"), bound = Call("B", F.Id("p"));
        Formula agrees = Equal(GcdReading(time, "a", "b"), GcdReading(time, "c", "d"));
        Formula positive = Seq(D(1), Sp, Le, Sp, time);
        Formula signedAgrees = Equal(SignedGcdReading(time, "n", "z"), SignedGcdReading(time, "n2", "z2"));
        Formula signedPrefix = AllN("k", ImpliesFormula(Both(positive, Seq(time, Sp, Le, Sp, bound)), signedAgrees));
        Formula signedFuture = AllN("k", ImpliesFormula(positive, signedAgrees));
        Formula signedUpper = AllZ("n,z,n2,z2", ImpliesFormula(signedPrefix, signedFuture));
        Formula prefix = AllN("k", ImpliesFormula(Both(positive, Seq(time, Sp, Le, Sp, bound)), agrees));
        Formula future = AllN("k", ImpliesFormula(positive, agrees));
        Formula upper = AllN("a,b,c,d", ImpliesFormula(prefix, future));
        Formula shorter = AllN("k", ImpliesFormula(Both(positive, Seq(time, Sp, Lt, Sp, bound)), agrees));
        Formula[] coordinateBounds = new[] { "a", "b", "c", "d" }
            .Select(name => Seq(F.Id(name), Sp, Lt, Sp, F.Id("p"))).ToArray();
        Formula separates = Seq(GcdReading(bound, "a", "b"), Sp, Neq, Sp, GcdReading(bound, "c", "d"));
        Formula lower = Seq(Exists, Sp, Names("a,b,c,d"), Sp, InMacro, Sp, F.Id("N"), Comma, Sp,
            Both([.. coordinateBounds, shorter, separates]));
        return Disp(AllN("p", ImpliesFormula(Call("Prime", F.Id("p")), Both(signedUpper, upper, lower))));
    }
}
