using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Probability;

internal sealed class KingmanPointwiseDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "On every finite measure space, nonnegative integrable subadditive cocycles have an integrable invariant real limit almost everywhere.",
        H("Kingman's nonnegative subadditive ergodic theorem"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("kingman-finite-measure"),
                DeclarationHandle.Create("D5/S3/Analytic/Probability/KingmanPointwise.kingman_subadditive"),
                H("An integrable invariant limit"),
                StatementSource.FromAuthor(Statement()),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Asymptotics/durrett2019probability")),
                Blocks(
                    Paragraph(Text("The carrier alpha ranges over every universe u and has an arbitrary measurable-space structure. The measure mu is finite, including zero. The transformation T preserves mu. For each natural n the real function X(n) is integrable and nonnegative almost everywhere. For every m,n, X(m+n,x) is at most X(m,x)+X(n,T^m x) almost everywhere. The exceptional sets may depend on the indices.")),
                    Paragraph(Text("There exists a real function g, integrable for the same mu, invariant under T almost everywhere, such that X(n,x)/n tends to g(x) almost everywhere along the full sequence of natural times. Real division is totalized, so the value at n=0 imposes no additional condition. The original X(0) need not vanish. No pointwise measurability of X(n), nonempty carrier, probability normalization, positive mass, ergodicity, invertibility, countability, standard Borel structure, boundedness or square integrability is assumed.")),
                    Paragraph(Text("When mu is zero, choose g=0; all almost-everywhere conclusions also hold on the empty carrier. For nonzero finite mu, normalize the measure to a probability measure. Its almost-everywhere filter agrees with that of mu, and integrability is equivalent for the two measures. Choose measurable representatives for the functions at positive times and set only the internal zeroth function to zero. Quasi-measure preservation transports their equalities through every orbit shift. Countable intersections produce a measurable forward-invariant set of full measure on which nonnegativity, the zeroth identity and all subadditive inequalities hold together. Setting the family to zero outside that set gives everywhere hypotheses.")),
                    Paragraph(Text("Subadditivity bounds the family by orbit sums of its first term. Fatou's lemma then bounds the integral of the nonnegative extended-real liminf rate and makes that rate finite almost everywhere. The one-step subadditive inequality makes the liminf subinvariant. Measure preservation gives equal integrals for the liminf and its composition; finiteness upgrades their one-sided inequality to equality almost everywhere.")),
                    Paragraph(Text("For each positive epsilon, the sets on which every average up to a horizon exceeds the liminf plus epsilon decrease to a null set. Their first-term integrals tend to zero. The adaptive greedy block estimate bounds each long average by the liminf plus epsilon, an orbit average of the bad-set indicator times the first term, and a terminal strip. Stationary-tail decay removes that strip. The weak maximal inequality makes the remaining excess set null as the bad-set horizon grows. Countably many epsilon levels give the upper limit bound; the definition of liminf gives the lower bound. The real-valued liminf is therefore the integrable invariant limit.")),
                    Paragraph(Text("Transfer this same function g, its integrability and invariance back to mu. Countably many representative equalities identify the original and internal positive-time sequences almost everywhere. Eventual equality transfers convergence without changing g or imposing an identity on X(0).")),
                    Paragraph(Text("Durrett, fifth edition, Section 6.4, Theorem 6.4.1 on printed page 343 with proof on pages 344–347, treats stationary subadditive arrays and also states L1 convergence and an infimum formula. Those further conclusions and a constant ergodic limit are not asserted here. Applying the theorem to a concrete array, matrix product or first-passage model requires the actual common law, shift action, integrability, nonnegativity and subadditive identification. Signed logarithmic cocycles require a separate argument.")),
                    Paragraph(Text("The Lean proof is an attributed adaptation of facebookresearch/atlas-lean, MathlibExt/Dynamics/Ergodic/Kingman.lean, revision a60759060b5616df0d5775b42da4d337719feb32. The Meta Platforms copyright and complete supplier license, including its intended-use preface, are retained. KingmanSigned.exists_invariant_limit_of_nonneg supplies the broad finite-measure specification; no signed-cocycle conclusion is used. The book is a citation-only mathematical source."))),
                DescribeRole.Theorem))));

    private static Formula V(string name) => name switch
    {
        "alpha" => Alpha,
        "mu" => Mu,
        _ => F.Id(name)
    };
    private static Formula Nat => Seq(Mathbb, Grp(V("N")));
    private static Formula Real => Seq(Mathbb, Grp(V("R")));
    private static Formula Fn(Formula a, Formula b) => new Formula.TypeArrow(a, b);
    private static Formula Par(Formula value) => Seq(Open, value, Close);
    private static Formula All(string name, Formula type) =>
        Seq(Forall, Sp, V(name), Colon, Sp, type, Comma, Sp);
    private static Formula Instance(Formula type) => Seq(OpenBracket, type, CloseBracket, Sp);
    private static Formula Lam(string name, Formula type, Formula body) =>
        Seq(LambdaLower, Sp, Par(Seq(V(name), Colon, Sp, type)), Sp, Mapsto, Sp, body);
    private static Formula App(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula Ae(Formula body) =>
        Call("Eventually", Lam("x", V("alpha"), body), Call("ae", V("mu")));
    private static Formula Term(Formula n, Formula x) => App(V("X"), n, x);
    private static Formula Statement() => Disp(new Formula.Aligned([
        Seq(All("alpha", Seq(Call("Type"), Sp, V("u"))),
            Instance(Call("MeasurableSpace", V("alpha"))),
            All("mu", Call("Measure", V("alpha"))),
            Instance(Call("IsFiniteMeasure", V("mu")))),
        Seq(All("T", Fn(V("alpha"), V("alpha"))),
            Call("MeasurePreserving", V("T"), V("mu"), V("mu")), Sp, Rightarrow,
            All("X", Fn(Nat, Fn(V("alpha"), Real)))),
        Seq(Par(Seq(All("n", Nat), Call("Integrable", App(V("X"), V("n")), V("mu")))),
            Sp, Rightarrow),
        Seq(Par(Seq(All("n", Nat), Ae(Seq(D(0), Leq, Term(V("n"), V("x")))))),
            Sp, Rightarrow),
        Seq(Par(Seq(All("m", Nat), All("n", Nat),
            Ae(Seq(Term(Seq(V("m"), Plus, V("n")), V("x")), Leq,
                Term(V("m"), V("x")), Plus,
                Term(V("n"), App(Call("iterate", V("T"), V("m")), V("x"))))))),
            Sp, Rightarrow),
        Seq(Exists, Sp, V("g"), Colon, Fn(V("alpha"), Real), Comma, Sp,
            Call("Integrable", V("g"), V("mu")), Land,
            Ae(Seq(App(V("g"), App(V("T"), V("x"))), Eq, App(V("g"), V("x")))), Land),
        Ae(Call("Tendsto", Lam("n", Nat,
                Seq(Frac, Grp(Term(V("n"), V("x"))), Grp(V("n")))),
            Call("atTop"), Call("nhds", App(V("g"), V("x")))))
    ]));
}
