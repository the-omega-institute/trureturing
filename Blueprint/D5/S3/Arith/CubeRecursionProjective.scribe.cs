using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith;

internal sealed class CubeRecursionProjectiveDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/CubeRecursionProjective.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Factorization/matijasevick2026squares");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The cubic family has true degree three and is not conjugate to the cubic power map over the full complex projective group.",
        H("The projective cubic family"),
        Blocks(
            Paragraph(Text("The information-escape audit remains unfinished. The eight same-author registration attempts "
                + "remain declared_unresolved with null certificates; the missing compiler source bindings are disclosed in "
                + "https://github.com/the-omega-institute/trureturing/issues/18969. The linked issue does not validate "
                + "the registrations. Mathematical proof, canonical admission, independent acceptance and solve credit "
                + "are distinct; no native acceptance or solve credit is claimed here.")),
            Paragraph(Text("N includes zero, C is the complex field, C[X] is its polynomial ring, "
                + "RatFunc(C) is its rational-function field, and P is OnePoint(C). finite(z) "
                + "is the canonical embedding C into P, and infinity is its remaining point. "
                + "num and denom on a rational function mean its coprime polynomial numerator "
                + "and monic denominator; natDegree is polynomial degree as a natural number. "
                + "The function e is Mathlib's canonical equivalence from P to the projectivization "
                + "of C squared; pair(x,y) denotes the class of the displayed nonzero vector. "
                + "act is the actual projective PGL action, GL means invertible two by two complex "
                + "matrices, mk is the quotient to PGL, and entry(m,i,j) is a matrix entry. "
                + "The operator ite denotes if-then-else. Proof arguments witnessing a nonzero "
                + "vector are implicit and irrelevant to its projective class.")),
            Paragraph(Text("The construction answers Section 7 question 2 under the explicit "
                + "minimal uniform autonomous fixed-degree-family reading documented with the "
                + "main result. These proofs are repository-derived; the source paper asks the "
                + "question and does not contain this family. Global priority is UNDETERMINED.")),
            Def("numerator", All("t", N(), Eqn(Call("numerator", V("t")),
                Add(V("X"), Call("C", V("t"))))),
                "X is the polynomial indeterminate, not a free complex variable. C(t) is the constant polynomial."),
            Def("denominator", All("t", N(), Eqn(Call("denominator", V("t")),
                Sub(Pow(Add(Add(V("X"), Call("C", V("t"))), D(1)), 3),
                    Add(V("X"), Call("C", V("t")))))),
                "The affine denominator is monic cubic."),
            Def("rationalMap", All("t", N(), Eqn(R(V("t")),
                Fr(Call("algebraMap", Call("numerator", V("t"))),
                    Call("algebraMap", Call("denominator", V("t")))))),
                "algebraMap is the canonical inclusion of C[X] into RatFunc(C)."),
            Def("mapDegree", All("f", RF(), Eqn(Call("mapDegree", V("f")),
                Call("max", Call("natDegree", Call("num", V("f"))),
                    Call("natDegree", Call("denom", V("f")))))),
                "This is the maximum of the reduced polynomial degrees, not RatFunc.intDegree, which is their difference."),
            Def("q", All("t", N(), All("z", C(), Eqn(Call("q", V("t"), V("z")),
                Sub(Pow(Add(Add(V("z"), V("t")), D(1)), 3), Add(V("z"), V("t")))))),
                "q is evaluation of the denominator in the finite chart."),
            Def("projectiveMap", All("t", N(), And(Eqn(PM(V("t"), Infty), Fin(D(0))),
                All("z", C(), Eqn(PM(V("t"), Fin(V("z"))),
                    Call("ite", Eqn(Call("q", V("t"), V("z")), D(0)), Infty,
                        Fin(Fr(Add(V("z"), V("t")), Call("q", V("t"), V("z"))))))))),
                "Every pole maps to infinity; infinity maps to zero."),
            Def("homogeneousA", XYZ(Eqn(Call("homogeneousA", V("t"), V("x"), V("y")),
                Mul(Add(V("x"), Mul(V("t"), V("y"))), Pow(V("y"), 2)))),
                "The first homogeneous form has degree three."),
            Def("homogeneousB", XYZ(Eqn(Call("homogeneousB", V("t"), V("x"), V("y")),
                Sub(Pow(Add(V("x"), Mul(Add(V("t"), D(1)), V("y"))), 3),
                    Mul(Add(V("x"), Mul(V("t"), V("y"))), Pow(V("y"), 2))))),
                "The second homogeneous form has no common nonzero-coordinate zero with the first."),
            Def("projectivePoint", All("x", C(), All("y", C(), Imp(NonzeroPair(),
                Eqn(Call("projectivePoint", V("x"), V("y")),
                    Call("inverse", Named("e"), Call("pair", V("x"), V("y"))))))),
                "The vector (x,y) is nonzero. inverse(e,pair(x,y)) means e inverse applied to that projective class."),
            Def("homogeneousImage", XYZ(Imp(NonzeroPair(),
                Eqn(Call("homogeneousImage", V("t"), V("x"), V("y")),
                    Call("inverse", Named("e"), Call("pair",
                        Call("homogeneousA", V("t"), V("x"), V("y")),
                        Call("homogeneousB", V("t"), V("x"), V("y"))))))),
                "The internal nonvanishing proof covers y=0 and x+t*y=0 as well as ordinary finite points."),
            Def("powerMap", And(Eqn(Call("powerMap", Infty), Infty),
                All("z", C(), Eqn(Call("powerMap", Fin(V("z"))), Fin(Pow(V("z"), 3))))),
                "This is z cubed extended to the entire complex projective line."),
            Def("mobius", All("g", PGL(), All("p", P(),
                Eqn(Mob(V("g"), V("p")), Call("inverse", Named("e"),
                    Call("act", V("g"), Call("e", V("p"))))))),
                "mobius is a genuine permutation transported from the PGL action, with group inverse acting as inverse permutation."),
            Thm("map_degree_three", All("t", N(), DegreeBody(V("t"))),
                "A polynomial Bezout identity proves coprimality. The monic denominator fixes the reduced pair, of degrees one and three."),
            Thm("homogeneous_coordinates", All("t", N(), HomogeneousBody(V("t"))),
                "The e-equivalence gives x/y in the finite chart and infinity when y=0. Direct algebra proves the equality, including denominator zeros."),
            Thm("rational_map_semantics", All("t", N(), SemanticsBody(V("t"))),
                "The reduced rational-function numerator and denominator identify its evaluation with the same finite-point map. Poles and infinity are explicit."),
            Thm("not_conjugate", All("t", N(), NonconjugacyBody(V("t"))),
                "The zero fibre is exactly {-t,infinity}. If two distinct points have the same image under z cubed, there is a third: for finite u,v take -u-v. "
                + "The factorization of u cubed minus v cubed proves the third image and distinctness. A bijection preserves fibre cardinality, "
                + "so conjugacy by any PGL element is impossible. No local critical-degree axiom or conditional normal form is used."),
            Thm("mobius_coordinates", All("m", GL(), MobiusBody(V("m"))),
                "Every complex PGL class has a GL representative by Mathlib's mk_surjective. These are the actual fractional-linear formulas for every "
                + "invertible matrix, including its finite poles and infinity. The main result consumes both this theorem and the quotient surjectivity."))));

    private static DocumentBlock Def(string name, Formula body, string prose) =>
        Node(name, body, prose, DescribeRole.Definition);
    private static DocumentBlock Thm(string name, Formula body, string prose) =>
        Node(name, body, prose, DescribeRole.Theorem);
    private static DocumentBlock Node(string name, Formula body, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("cube-projective-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(name.Replace('_', ' ')),
            StatementSource.FromAuthor(Disp(body)), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role);

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
    private static Formula XYZ(Formula f) => All("t", N(), All("x", C(), All("y", C(), f)));
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
}
