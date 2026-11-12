using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Invariants;

internal sealed class SomosFirstDualIntegralityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Invariants/SomosFirstDualIntegrality.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/RecurrenceAlgebraic/ovsienko2017dual");
    private static Formula V(string s) => F.Id(s);
    private static Formula Named(string s) => Seq(Operatorname, Grp(V(s)));
    private static Formula App(string s, params Formula[] args) =>
        new Formula.Apply(Named(s), [.. args]);
    private static Formula At(Formula f, Formula n) => new Formula.Apply(f, [n]);
    private static Formula Par(Formula x) => Seq(Open, x, Close);
    private static Formula Set(string s) => Seq(Mathbb, Grp(V(s)));
    private static Formula N => Set("N");
    private static Formula Z => Set("Z");
    private static Formula Q => Set("Q");
    private static Formula R => Set("R");
    private static Formula Dual(Formula k) => App("DualNumber", k);
    private static Formula Arrow(Formula a, Formula b) => Seq(a, Sp, To, Sp, b);
    private static Formula SeqType(Formula k) => Arrow(N, Dual(k));
    private static Formula InitialType => Arrow(App("Fin", D(4)), Z);
    private static Formula All(string s, Formula t, Formula b) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(s), t, b);
    private static Formula Ex(string s, Formula t, Formula b) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(s), t, b);
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Iffn(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula Conj(params Formula[] fs) => fs.Length == 1 ? fs[0] :
        And(fs[0], Conj(fs[1..]));
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(a, b);
    private static Formula Cast(Formula x, Formula k) => Par(Seq(x, Colon, Sp, k));
    private static Formula Fst(Formula x) => App("fst", x);
    private static Formula Snd(Formula x) => App("snd", x);
    private static Formula Pos(Formula x) =>
        new Formula.Relation(D(0), FormulaRelationOperator.LessThan, x);
    private static Formula LambdaN(Formula body) =>
        Seq(Par(Seq(V("n"), Colon, Sp, N, Sp, Mapsto, Sp, body)));

    private static Formula OrbitBody(Formula k)
    {
        Formula An(int j) => At(V("A"), j == 0 ? V("n") : Add(V("n"), Num(j)));
        Formula eps = V("epsilon");
        return And(
            All("i", App("Fin", D(4)), Equal(At(V("A"), V("i")),
                Add(D(1), Multiply(Cast(At(V("c"), V("i")), k), eps)))),
            All("n", N, Equal(Multiply(An(4), An(0)),
                Add(Pow(Multiply(An(1), An(3)), V("p")),
                    Multiply(Add(D(1), eps), Pow(An(2), V("q")))))));
    }

    private static Formula OrbitDefinition(string name, Formula k) =>
        All("p", N, All("q", N, All("c", InitialType, All("A", SeqType(k),
            Iffn(App(name, V("p"), V("q"), V("c"), V("A")), OrbitBody(k))))));

    private static Formula IntegralShadows(Formula k, bool mapped = false) =>
        All("n", N, Ex("b", Z, Equal(Cast(V("b"), k),
            Snd(mapped ? App("realCast", At(V("A"), V("n"))) : At(V("A"), V("n"))))));

    private static Formula InjectiveCast() => All("x", Dual(Q), All("y", Dual(Q),
        Imp(Equal(App("realCast", V("x")), App("realCast", V("y"))), Equal(V("x"), V("y")))));

    private static Formula ResultBody() => All("p", N, All("q", N, All("c", InitialType,
        Imp(And(Pos(V("p")), Pos(V("q"))), Ex("A", SeqType(Q), Conj(
            App("IsOrbit", V("p"), V("q"), V("c"), V("A")),
            All("X", SeqType(Q), Imp(App("IsOrbit", V("p"), V("q"), V("c"), V("X")),
                Equal(V("X"), V("A")))),
            All("n", N, Pos(Fst(At(V("A"), V("n"))))),
            Iffn(IntegralShadows(Q), Equal(V("p"), D(1))),
            All("B", SeqType(R), Iffn(App("IsRealOrbit", V("p"), V("q"), V("c"), V("B")),
                Equal(V("B"), LambdaN(App("realCast", At(V("A"), V("n"))))))),
            Iffn(IntegralShadows(R, mapped: true), Equal(V("p"), D(1))),
            InjectiveCast()))))));

    private static DocumentBlock Node(string name, string title, Formula formula,
        DescribeRole role, string prose, bool fromSource = false,
        OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
            DescribeId.Create("first-dual-somos-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(Disp(formula)),
            fromSource ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The first dual Somos-4 orbit has integer shadows exactly at p=1, for each integer initial tuple.",
        H("Pointwise integrality of the first dual Somos recurrence"),
        Blocks(
            Paragraph(Text("DualNumber K is the square-zero algebra K + K epsilon, with epsilon squared zero. "
                + "The first and second projections are the real and shadow coefficients. All sequence indices "
                + "are natural and the four initial slots are indexed from zero. The source's product of "
                + "two p-th powers equals the p-th power of their product in this commutative algebra. "
                + "No positivity or nonvanishing assumption is added to the source exchange predicate.")),
            Node("IsOrbit", "The rational-dual exchange predicate", OrbitDefinition("IsOrbit", Q),
                DescribeRole.Definition,
                "The first non-homogeneous recurrence in the source conjecture, with each arbitrary "
                + "integer tuple retained separately. The source's initial-shadow indices b1 through b4 "
                + "are normalized to the section's leading slots 0 through 3.", fromSource: true),
            Node("realCast", "Coefficientwise inclusion into real duals",
                All("x", Dual(Q), And(
                    Equal(Fst(App("realCast", V("x"))), Cast(Fst(V("x")), R)),
                    Equal(Snd(App("realCast", V("x"))), Cast(Snd(V("x")), R)))),
                DescribeRole.Definition,
                "This is a ring homomorphism. The result proves it is injective and that it "
                + "preserves and reflects the existence of an integer shadow coefficient."),
            Node("IsRealOrbit", "The real-dual source exchange predicate", OrbitDefinition("IsRealOrbit", R),
                DescribeRole.Definition,
                "The same recurrence over real dual numbers, as in the paper. "
                + "The final theorem identifies every such orbit with the embedded rational orbit.", fromSource: true),
            Node("result", "The full integrality equivalence and faithful source realization", ResultBody(),
                DescribeRole.Theorem,
                "For every positive p and q and each integer tuple c there exists a unique rational-dual "
                + "orbit with the prescribed initial data; its real coefficients are positive. All of its "
                + "shadow coefficients are integers if and only if p=1. The displayed conjunction also gives "
                + "the unique real-dual realization, the same shadow equivalence there, and injectivity "
                + "of the coefficientwise embedding. The p=1 sufficient direction is published prior work. "
                + "The formal proof uses the following elementary divisibility route.",
                resolution: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("ovsienko-tabachnikov-first-dual-somos-integrality"),
                    ResolutionKind.Proved)),
            Paragraph(Text("For eight consecutive integer duals A,B,C,D,E,F,G,H, reduce modulo E. "
                + "Coprimality of the real parts of B,C,D with that of E makes B,C,D units by a "
                + "lifted Bezout identity. The four exchange equations make F,G,H units as well. "
                + "Writing t=1+v epsilon and N=(FH)^p+tG^q, lawful unit calculations give "
                + "t^(2p)N=(HF)^p(t^(2p)-t^2). The difference is (2p-2)v epsilon. "
                + "Both prefactors are units, so E divides N exactly when the real part of E divides "
                + "(2p-2)v. Coefficient comparison proves this last equivalence without cancelling epsilon. "
                + "Only natural powers occur, so q=1 is included.")),
            Paragraph(Text("With zero obstruction, strong induction constructs the next integer dual "
                + "before propagating pairwise coprimality of each four-term real window. Its v=0 "
                + "instance proves real-part integrality for arbitrary exponents; its p=1 instance "
                + "proves the required shadows. Conversely, an entirely integer v=1 orbit would "
                + "force 2^p+1 to divide 2p-2 at the window with divisor A5. For p at least two the "
                + "latter is positive and strictly smaller. This contradiction is independent of "
                + "all four initial shadows. Neither the second deformation nor a separate growth "
                + "assertion is part of this theorem. No global novelty or priority is asserted.")))));
}
