using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Games;

internal sealed class PyranimCollisionLimitsDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Combinatorics/Games/PyranimCollisionLimits";
    private static LibraryNoteRef Source =>
        LibraryNoteRef.Create("D5/L/Asymptotics/binyaminkniffen2026pyranim");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Root and zero limits for Pyranim collisions",
        H("Root and zero limits for Pyranim collisions"),
        Blocks(
            Node("unmarkedBound", "Bound for words avoiding a prescribed block",
                UnmarkedBody(),
                "At each width-n encoding there are q complete slots of length M and a tail of length r. M is 2(L+1), q is the floor of 2(n+1)/M and r is its remainder. The letter equivalence with Bool and Mathlib’s fixed-length vector count give 2^M words in a slot and 2^r words in the tail. Mathlib’s Set.card_ne_eq counts the words unequal to the prescribed block, giving 2^M−1 slot choices. Splitting off the first slot gives an injection into a nonpivot block and a shorter avoiding word.",
                DescribeRole.Definition),
            Node("gameIso_class_card_upper", "Uniform collision-class bound",
                ClassBound(),
                "Equivalent games have the same maximum complete legal path length, equal to chip count. In each marked position, changing the first marked slot produces L+1 different counts and preserves the identity of the slot. The remaining words avoid a prescribed pattern in every complete slot.",
                DescribeRole.Theorem),
            Node("tendsto_collisionProbability_zero", "Decay for independent draws",
                Decay("collisionProbability"),
                "Sum the uniform class bound over all first draws. At fixed L the unmarked fraction goes to zero because the loss in each slot is exponential in the number of slots, whereas the Catalan denominator differs from 4^(n+1) by at most a polynomial factor. The remaining bound is 1/(L+1), which tends to zero.",
                DescribeRole.Theorem),
            Node("tendsto_distinctCollisionProbability_zero", "Decay for uniformly sampled distinct pairs",
                Decay("distinctCollisionProbability"),
                "The distinct-pair probability is bounded by the independent probability at every positive width, so it tends to zero as well.",
                DescribeRole.Theorem),
            Node("result", "Root and zero limits for both distributions",
                ResultBody(),
                "The root tends to one and the probability tends to zero at all widths tending to infinity, for independent uniform draws and for uniform distinct pairs. A sharp decay rate, random-start expectations, and the full reverse reconstruction are open within this result’s scope.",
                DescribeRole.Theorem))));

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

    private static Formula All(string x, Formula type, Formula f) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(x), type, f);

    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);

    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);

    private static Formula And(Formula a, Formula b) => Logic(a, FormulaLogicOperator.And, b);

    private static Formula Logic(Formula a, FormulaLogicOperator op, Formula b) => new Formula.Logic(Par(a), op, Par(b));

    private static Formula SetOf(string x, Formula type, Formula f) => Seq(OpenBrace, V(x), Colon, type, Mid, Sp, f, CloseBrace);

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

    private static Formula UnmarkedBody()
    {
        var width = Multiply(D(2), Par(Add(V("L"), D(1))));
        var length = Multiply(D(2), Par(Add(V("n"), D(1))));
        var slots = Call("floor", Div(length, width));
        var remainder = Call("mod", length, width);
        return All("n", Nat, All("L", Nat, Eq(Call("unmarkedBound", V("n"), V("L")),
            Multiply(Pow(Par(Subtract(Pow(D(2), width), D(1))), slots), Pow(D(2), remainder)))));
    }

    private static Formula ClassBound()
    {
        var n = V("n"); var l = V("L");
        var size = Cast(Card(SetOf("J", Stable(n), Iso(V("I"), V("J")))));
        return All("n", Nat, All("L", Nat, All("I", Stable(n), Le(size,
            Add(Div(Cast(Card(Stable(n))), Add(Cast(l), D(1))),
                Cast(Call("unmarkedBound", n, l)))))));
    }

    private static Formula ResultBody() =>
        And(Root("collisionProbability"), And(Decay("collisionProbability"),
            And(Root("distinctCollisionProbability"), Decay("distinctCollisionProbability"))));
}
