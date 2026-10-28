using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith;

internal sealed class CubeRecursionFamilyDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/CubeRecursionFamily.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Factorization/matijasevick2026squares");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "One uniform autonomous degree-three rational family has cube sums for the actual positive reduced pairs of every positive rational orbit.",
        H("A uniform reduced-coordinate cube family"),
        Blocks(
            Paragraph(Text("The information-escape audit remains unfinished. The eight same-author registration attempts "
                + "remain declared_unresolved with null certificates; the missing compiler source bindings are disclosed in "
                + "https://github.com/the-omega-institute/trureturing/issues/18969. The linked issue does not validate "
                + "the registrations. Mathematical proof, canonical admission, independent acceptance and solve credit "
                + "are distinct; no native acceptance or solve credit is claimed here.")),
            Paragraph(Text("N includes zero, Q is the rational field, and Z the integers. "
                + "orbit(t,x,n) starts at n=0 and iterates the single map step(t). For a rational y, "
                + "num(y) is its intrinsic integer numerator and den(y) its positive natural "
                + "denominator, already coprime. natAbs is the natural absolute value of an integer; "
                + "all cross-type arithmetic uses the canonical casts. tsub is truncated natural "
                + "subtraction. In the projective clauses C, OnePoint(C), PGL, GL, mk, finite, "
                + "projectivePoint, homogeneousImage, rationalMap and mobius have the meanings "
                + "given by CubeRecursionProjective. The coordinate formulas use every invertible "
                + "matrix and every complex point, including poles and infinity.")),
            Paragraph(Text("Section 7 question 2 of arXiv:2610.00765v1 leaves natural undefined. "
                + "Here it means an explicit uniform family of autonomous rational maps over Q "
                + "with one nonnegative integer parameter, fixed degree, one formula and a "
                + "constant independent of parameter, start and index. The constant is c=1. "
                + "The theorem strengthens the inherited positive-integer starts and n>=2 "
                + "to all positive rational starts and every n>=1. It makes no n=0 cube-sum "
                + "or classification claim. A stricter unstated author intent is unresolved. "
                + "The construction is repository-derived. The supplied bounded comparison "
                + "identified no equivalent whole answer, but global priority is UNDETERMINED "
                + "and the companion works were unlocated; no new-solve credit follows here.")),
            Node("step", All("t", N(), All("x", Q(), Eqn(S(V("t"), V("x")),
                Fr(Add(V("x"), V("t")), Sub(Pow(Add(Add(V("x"), V("t")), D(1)), 3),
                    Add(V("x"), V("t"))))))),
                "The map is autonomous. Division is rational division; positivity of the denominator on positive inputs is proved below.", DescribeRole.Definition),
            Node("nextA", TAB(Eqn(A(V("t"), V("a"), V("b")),
                Mul(Add(V("a"), Mul(V("t"), V("b"))), Pow(V("b"), 2)))),
                "For positive coprime a,b this is the exact next reduced numerator.", DescribeRole.Definition),
            Node("nextB", TAB(Eqn(B(V("t"), V("a"), V("b")),
                ExpandedDenominator())),
                "The expanded natural-valued denominator is visibly positive on positive inputs.", DescribeRole.Definition),
            Node("orbit", All("t", N(), All("x", Q(), All("n", N(),
                Eqn(O(V("t"), V("x"), V("n")),
                    Call("iterate", Call("step", V("t")), V("n"), V("x")))))),
                "iterate(f,n,x) is f iterated n times at x, with the zeroth iterate equal to x.", DescribeRole.Definition),
            Node("reduced_step", ReducedStep(),
                "Put u=a+t*b. The next numerator is u times b squared and the denominator is (u+b) cubed minus that numerator. "
                + "The denominator expands as u cubed plus 3*u squared*b plus 2*u*b squared plus b cubed, so both entries are positive. "
                + "Coprimality of a,b gives coprimality of u,b and of u+b with both. Thus the numerator is coprime to (u+b) cubed, "
                + "and hence to the denominator. Canonical Rat numerator and denominator lemmas identify this pair with the actual reduced pair.",
                DescribeRole.Theorem),
            Node("positive_orbit_cube", All("t", N(), All("x", Q(), Imp(Pos(V("x")),
                And(All("n", N(), Pos(O(V("t"), V("x"), V("n")))),
                    All("n", N(), CubeAt(V("t"), V("x"), Add(V("n"), D(1)), V("n"))))))),
                "Every positive rational is its canonical reduced numerator divided by denominator. Apply reduced_step to that pair; induction "
                + "preserves positivity and gives the integer cube identity for every next step. There is no finite index bound or conditional no-cancellation assumption.",
                DescribeRole.Theorem),
            Node("originalClaim", Seq(Named("originalClaim"), Sp, Iff, Sp, Par(Whole())),
                "This closed proposition states the whole source endpoint together with the semantic bridges. In each n>=1 cube equality "
                + "the displayed num and den are intrinsic to the actual iterate. All projective clauses are conjoined, including the full quotient and action correspondence.",
                DescribeRole.Definition),
            Node("result", Whole(),
                "The single result combines reduced_step and orbit induction with the complex rational-map degree, homogeneous "
                + "coordinates, affine/pole/infinity evaluation, the full PGL quotient and action, and nonconjugacy. The rational orbit "
                + "and complex projective map agree at every positive rational iterate. The reduced polynomial degrees are one and three. "
                + "The fibre obstruction excludes every complex Möbius conjugacy to z cubed. Positivity and coprimality are conclusions, "
                + "not extra orbit hypotheses. Under the declared minimal reading this provides the requested family with c=1; it "
                + "does not settle a stronger unstated definition of natural or claim global originality.", DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("arxiv-2610-00765-cube-recursion-family"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, Formula body, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create("cube-family-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(name.Replace('_', ' ')),
            StatementSource.FromAuthor(Disp(body)), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
    internal static Formula V(string s) => F.Id(s);
    internal static Formula Named(string s) => Seq(Operatorname, Grp(V(s)));
    internal static Formula Call(string s, params Formula[] args) =>
        new Formula.Apply(Named(s), [.. args]);
    internal static Formula N() => Seq(Mathbb, Grp(V("N")));
    internal static Formula C() => Seq(Mathbb, Grp(V("C")));
    internal static Formula P() => Call("OnePoint", C());
    internal static Formula RF() => Call("RatFunc", C());
    internal static Formula PGL() => Call("PGL", D(2), C());
    internal static Formula GL() => Call("GL", D(2), C());
    internal static Formula Par(Formula f) => Seq(Open, f, Close);
    internal static Formula All(string s, Formula type, Formula body) =>
        Seq(Forall, Sp, V(s), Colon, Sp, type, Comma, Sp, body);
    internal static Formula Eqn(Formula a, Formula b) => Seq(a, Sp, Eq, Sp, b);
    internal static Formula Ne(Formula a, Formula b) => Seq(a, Sp, Neq, Sp, b);
    internal static Formula And(Formula a, Formula b) => Seq(Par(a), Sp, Land, Sp, Par(b));
    internal static Formula Or(Formula a, Formula b) => Seq(Par(a), Sp, Lor, Sp, Par(b));
    internal static Formula Imp(Formula a, Formula b) => Seq(Par(a), Sp, Implies, Sp, Par(b));
    internal static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    internal static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    internal static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    internal static Formula Pow(Formula a, byte n) => new Formula.Power(Par(a), D(n));
    internal static Formula Fr(Formula a, Formula b) => new Formula.Fraction(a, b);
    internal static Formula Fin(Formula z) => Call("finite", z);
    internal static Formula R(Formula t) => Call("rationalMap", t);
    internal static Formula PM(Formula t, Formula p) => Call("projectiveMap", t, p);
    internal static Formula Mob(Formula g, Formula p) => Call("mobius", g, p);
    private static Formula NonzeroPair() => Or(Ne(V("x"), D(0)), Ne(V("y"), D(0)));
    internal static Formula DegreeBody(Formula t) => And(Eqn(Call("natDegree", Call("num", R(t))), D(1)),
        And(Eqn(Call("natDegree", Call("denom", R(t))), D(3)), Eqn(Call("mapDegree", R(t)), D(3))));
    internal static Formula HomogeneousBody(Formula t) => All("x", C(), All("y", C(),
        Imp(NonzeroPair(), Eqn(PM(t, Call("projectivePoint", V("x"), V("y"))),
            Call("homogeneousImage", t, V("x"), V("y"))))));
    internal static Formula SemanticsBody(Formula t) => And(Eqn(PM(t, Infty), Fin(D(0))),
        All("z", C(), Eqn(PM(t, Fin(V("z"))), Call("ite",
            Eqn(Call("eval", Call("denom", R(t)), V("z")), D(0)), Infty,
            Fin(Call("eval", R(t), V("z")))))));
    internal static Formula NonconjugacyBody(Formula t) => All("g", PGL(), Seq(Neg, Sp,
        Par(All("p", P(), Eqn(Mob(V("g"), PM(t, Mob(Call("inv", V("g")), V("p")))),
            Call("powerMap", V("p")))))));
    private static Formula E(Formula m, byte i, byte j) => Call("entry", m, D(i), D(j));
    internal static Formula MobiusBody(Formula m) => And(
        Eqn(Mob(Call("mk", m), Infty), Call("ite", Eqn(E(m, 1, 0), D(0)), Infty,
            Fin(Fr(E(m, 0, 0), E(m, 1, 0))))),
        All("z", C(), Eqn(Mob(Call("mk", m), Fin(V("z"))),
            Call("ite", Eqn(Add(Mul(E(m, 1, 0), V("z")), E(m, 1, 1)), D(0)), Infty,
                Fin(Fr(Add(Mul(E(m, 0, 0), V("z")), E(m, 0, 1)),
                    Add(Mul(E(m, 1, 0), V("z")), E(m, 1, 1))))))));
    private static Formula Q() => Seq(Mathbb, Grp(V("Q")));
    private static Formula Pos(Formula a) => Seq(D(0), Sp, Lt, Sp, a);
    private static Formula LeqTo(Formula a, Formula b) => Seq(a, Sp, Le, Sp, b);
    private static Formula Coprime(Formula a, Formula b) => Call("Coprime", a, b);
    private static Formula S(Formula t, Formula x) => Call("step", t, x);
    private static Formula O(Formula t, Formula x, Formula n) => Call("orbit", t, x, n);
    private static Formula A(Formula t, Formula a, Formula b) => Call("nextA", t, a, b);
    private static Formula B(Formula t, Formula a, Formula b) => Call("nextB", t, a, b);
    private static Formula Num(Formula y) => Call("num", y);
    private static Formula Den(Formula y) => Call("den", y);
    private static Formula TAB(Formula f) => All("t", N(), All("a", N(), All("b", N(), f)));
    private static Formula ExpandedDenominator()
    {
        Formula u = Add(V("a"), Mul(V("t"), V("b")));
        return Add(Add(Add(Pow(u, 3), Mul(Mul(D(3), Pow(u, 2)), V("b"))),
            Mul(Mul(D(2), u), Pow(V("b"), 2))), Pow(V("b"), 3));
    }
    private static Formula ReducedStep()
    {
        Formula t = V("t"), a = V("a"), b = V("b");
        Formula y = S(t, Fr(a, b));
        return TAB(Imp(Pos(a), Imp(Pos(b), Imp(Coprime(a, b),
            And(Pos(y), And(Eqn(Num(y), A(t, a, b)), And(Eqn(Den(y), B(t, a, b)),
                And(Coprime(A(t, a, b), B(t, a, b)), Eqn(Add(A(t, a, b), B(t, a, b)),
                    Pow(Add(a, Mul(Add(t, D(1)), b)), 3))))))))));
    }
    private static Formula CubeAt(Formula t, Formula x, Formula next, Formula prev)
    {
        Formula yn = O(t, x, next), yp = O(t, x, prev);
        return Eqn(Add(Num(yn), Den(yn)), Pow(Add(Num(yp), Mul(Add(t, D(1)), Den(yp))), 3));
    }
    private static Formula PairData(Formula y) => And(Pos(y), And(Pos(Num(y)),
        And(Pos(Den(y)), And(Coprime(Call("natAbs", Num(y)), Den(y)), Eqn(Fr(Num(y), Den(y)), y)))));
    private static Formula Representatives() => All("g", PGL(), Seq(Exists, Sp,
        V("m"), Colon, Sp, GL(), Comma, Sp, Eqn(Call("mk", V("m")), V("g"))));
    private static Formula Whole()
    {
        Formula t = V("t"), x = V("x"), n = V("n");
        Formula orbitLaws = All("x", Q(), Imp(Pos(x), And(
            All("n", N(), PairData(O(t, x, n))), And(
                All("n", N(), Imp(LeqTo(D(1), n), CubeAt(t, x, n, Call("tsub", n, D(1))))),
                All("n", N(), Eqn(PM(t, Fin(Call("toComplex", O(t, x, n)))),
                    Fin(Call("toComplex", O(t, x, Add(n, D(1)))))))))));
        return All("t", N(), And(Eqn(Call("mapDegree", R(t)), D(3)),
            And(HomogeneousBody(t), And(And(Representatives(), All("m", GL(), MobiusBody(V("m")))),
                And(SemanticsBody(t), And(NonconjugacyBody(t), orbitLaws))))));
    }
}
