using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Games;

internal sealed class PyranimCollisionRootDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Combinatorics/Games/PyranimCollisionRoot";
    private static LibraryNoteRef Source =>
        LibraryNoteRef.Create("D5/L/Asymptotics/binyaminkniffen2026pyranim");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "All-width root limits for Pyranim collisions",
        H("All-width root limits for Pyranim collisions"),
        Blocks(
            Node("CollisionPairs", "Ordered collision event",
                All("n", Nat, Eq(Call("CollisionPairs", V("n")), SetOf("p", Pair(V("n")), Iso(First(V("p")), Second(V("p")))))),
                "On an ordered pair of width-n stable positions the event is recursive game isomorphism.",
                DescribeRole.Definition),
            Node("collisionProbability", "Independent uniform collision probability",
                All("n", Nat, Eq(P("collisionProbability"), Div(Cast(Card(Call("CollisionPairs", V("n")))), Pow(Cast(Card(Stable(V("n")))), D(2))))),
                "Independent draws with replacement give equal mass to every ordered pair. Every stable position of width n is eligible.",
                DescribeRole.Definition),
            Node("stable_card_pos", "Nonempty sample space",
                All("n", Nat, Lt(D(0), Card(Stable(V("n"))))),
                "The empty stable position belongs to the sample space at every width.",
                DescribeRole.Lemma),
            Node("tendsto_collisionProbability_root", "All-width root limit for independent draws",
                Root("collisionProbability"),
                "Full blocks of width b+2 have Catalan(b+1) choices. Equal block multiplicities induce an order isomorphism and transport every legal option. Counting multiplicity vectors gives a lower bound after division by the square of the Catalan population. First let n grow through every width with b fixed, including the final remainder, and then let b grow. The probability is at most one.",
                DescribeRole.Theorem),
            Node("DistinctPairs", "Ordered pairs of distinct positions",
                All("n", Nat, Eq(Call("DistinctPairs", V("n")), SetOf("p", Pair(V("n")), Ne(First(V("p")), Second(V("p")))))),
                "Pairs exclude the diagonal of literal equality.",
                DescribeRole.Definition),
            Node("DistinctCollisionPairs", "Distinct ordered collisions",
                All("n", Nat, Eq(Call("DistinctCollisionPairs", V("n")), SetOf("p", Call("CollisionPairs", V("n")), Ne(First(Val(V("p"))), Second(Val(V("p"))))))),
                "A distinct collision is an ordered collision whose two literal positions differ.",
                DescribeRole.Definition),
            Node("distinctCollisionProbability", "Uniform distinct-pair collision probability",
                All("n", Nat, Eq(P("distinctCollisionProbability"), Div(Cast(Card(Call("DistinctCollisionPairs", V("n")))), Cast(Card(Call("DistinctPairs", V("n"))))))),
                "There are distinct ordered pairs at every positive width. Width zero uses totalized real division as its Lean convention.",
                DescribeRole.Definition),
            Node("distinctCollisionProbability_eq", "Removing the diagonal",
                DistinctIdentity(),
                "With N stable positions the event includes all N diagonal pairs. Removing the diagonal from the numerator and denominator gives the displayed equality when N is greater than one.",
                DescribeRole.Theorem),
            Node("tendsto_distinctCollisionProbability_root", "All-width root limit for distinct draws",
                Root("distinctCollisionProbability"),
                "The independent collision probability eventually dominates twice the diagonal mass, by the independent root limit and the exponential size of the population. The distinct-pair probability then lies between half the independent probability and the independent probability.",
                DescribeRole.Theorem),
            Node("tendsto_distinctCollisionProbability_zero_of", "Transferring decay to distinct draws",
                Imp(Decay("collisionProbability"), Decay("distinctCollisionProbability")),
                "At positive widths the distinct-pair probability lies between zero and the independent probability.",
                DescribeRole.Lemma))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role, bool literature = false, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create("pyranim-" + name.ToLowerInvariant().Replace('_', '-')),
            DeclarationHandle.Create(Module + "." + name), H(title),
            StatementSource.FromAuthor(Disp(formula)),
            literature ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula Nat => Seq(Mathbb, Grp(F.Id("N")));

    private static Formula Real => Seq(Mathbb, Grp(F.Id("R")));

    private static Formula V(string name) => F.Id(name);

    private static Formula Named(string name) => Seq(Operatorname, Grp(V(name)));

    private static Formula Call(string name, params Formula[] args) => App(Named(name), args);

    private static Formula App(Formula name, params Formula[] args) => new Formula.Apply(name, [.. args]);

    private static Formula Par(Formula f) => Seq(Open, f, Close);

    private static Formula Field(Formula x, string f) => Seq(x, Dot, V(f));

    private static Formula All(string x, Formula type, Formula f) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(x), type, f);

    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);

    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);

    private static Formula Ne(Formula a, Formula b) => Seq(a, Neq, Sp, b);

    private static Formula Imp(Formula a, Formula b) => Logic(a, FormulaLogicOperator.Implies, b);

    private static Formula Logic(Formula a, FormulaLogicOperator op, Formula b) => new Formula.Logic(Par(a), op, Par(b));

    private static Formula SetOf(string x, Formula type, Formula f) => Seq(OpenBrace, V(x), Colon, type, Mid, Sp, f, CloseBrace);

    private static Formula Val(Formula x) => Field(x, "val");

    private static Formula Card(Formula x) => App(Seq(Named("Nat"), Dot, Named("card")), x);

    private static Formula Cast(Formula x) => Par(Seq(x, Colon, Real));

    private static Formula Pow(Formula a, Formula b) => new Formula.Power(a, b);

    private static Formula Div(Formula a, Formula b) => new Formula.Fraction(a, b);

    private static Formula Stable(Formula n) => Call("Stable", n);

    private static Formula Iso(Formula a, Formula b) => Call("GameIso", a, b);

    private static Formula P(string prob) => Call(prob, V("n"));

    private static Formula Tends(Formula sequence, Formula limit) => Call("Tendsto", sequence, V("atTop"), Call("nhds", limit));

    private static Formula Lambda(Formula body) => Par(Seq(LambdaLower, Sp, Par(Seq(V("n"), Colon, Nat)), Mapsto, body));

    private static Formula Root(string prob) => Tends(Lambda(Pow(Par(P(prob)), Div(D(1), Cast(V("n"))))), D(1));

    private static Formula Decay(string prob) => Tends(Named(prob), D(0));

    private static Formula Pair(Formula n) => Seq(Stable(n), Times, Sp, Stable(n));

    private static Formula First(Formula p) => Seq(p, Dot, D(1));

    private static Formula Second(Formula p) => Seq(p, Dot, D(2));

    private static Formula DistinctIdentity()
    {
        var count = Card(Stable(V("n")));
        return All("n", Nat, Imp(Lt(D(1), count), Eq(P("distinctCollisionProbability"),
            Div(Subtract(Multiply(Cast(count), P("collisionProbability")), D(1)), Subtract(Cast(count), D(1))))));
    }
}
