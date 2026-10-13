using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.ExtremalDensity;

internal sealed class NagyOptimizerMonotonicityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/ExtremalDensity/NagyOptimizerMonotonicity.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/GraphInvariants/daysarkar2021extremaldensities");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The optimal T-parameter need not increase with edge density.",
        H("The optimal T-parameter is not monotone"),
        Blocks(
            Describe.Lean(DescribeId.Create("optimizer-monotonicity-claim"),
                DeclarationHandle.Create(Prefix + "claim"), H("Monotone selections of maximisers"),
                StatementSource.FromAuthor(Disp(Claim())), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "Day and Sarkar, §5, p. 14 (arXiv v1), verbatim: “Conjecture 2. For each graph G_l, "
                    + "we have that q(G_l, β) is an increasing function of β.” The optimiser is introduced "
                    + "on pp. 13–14 by sup(q∈[0,1]) t(G_l,T_n^e(q)), followed by “and let q(G_l,β)∈[0,1] "
                    + "be the value of q at which the supremum is attained”. The graph has vertex set Fin v, "
                    + "the real density beta ranges over [0,1], and qf selects a maximiser in [0,1] at every "
                    + "density. MonotoneOn means nondecreasing. This is the weakest selection reading; "
                    + "a refutation also excludes a strictly increasing selection. The density is the "
                    + "literal homomorphism limit defined in ThreeClassHomomorphismLimit."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("optimizer-monotonicity-refutation"),
                DeclarationHandle.Create(Prefix + "result"), H("A seven-vertex counterexample"),
                StatementSource.FromAuthor(Disp(Seq(Neg, Sp, V("claim")))), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "Take the graph on Fin 7 with edges 01, 12, 20, 03, 34, 35 and 36. "
                    + "It consists of a triangle and a three-leaf star whose centre is joined to one "
                    + "triangle vertex. At beta = 1/1000000 every maximiser exceeds 7743/10000; "
                    + "at beta = 1/10000 every maximiser is below 7719/10000. Each maximum exists "
                    + "and is unique. Since the density increases and the optimal parameter decreases, "
                    + "no monotone selection can satisfy claim.")),
                    Paragraph(Text(
                        "Write z = r+y. Splitting on the star centre's class gives the density "
                        + "r z³ + 3 b r³ + y z⁶ + 2 b y r² z³ + b r⁴ beta. "
                        + "For s = √beta and x = z/s, use r = s²(1−x²)/(2(1−sx)) and "
                        + "q = x−s(1−x²)/(2(1−sx)). The coordinate map is strictly increasing "
                        + "on [0,1] for 0<s≤1/100. The rational identity and derivative explicitly "
                        + "require 1−sx≠0; this holds on the intervals used here. "
                        + "The derivative of the density divided by s⁵ is "
                        + "(sx²+s−2x) Q_s(x)/(16(sx−1)⁴), where Q_s is a degree-eight polynomial. "
                        + "Its derivative is positive on [1/2,1]. The density divided by s⁵ is "
                        + "below 83/1000 for x≤1/2, whereas its value at x=3/4 exceeds 9/100 "
                        + "at both densities. Exact sign evaluations place the two roots in "
                        + "(77451/100000,77452/100000) and (77384/100000,77385/100000), "
                        + "respectively. The increasing coordinate map transfers these intervals "
                        + "to disjoint, reversed bounds for q. This conclusion concerns the "
                        + "seven-vertex graph and these two densities; no uniform interval of "
                        + "decrease or assertion for every pendant-star graph is made."))), DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("day-sarkar-2021-t-optimizer-monotonicity"),
                    ResolutionKind.Refuted)))));

    private static Formula V(string name) => FormulaDsl.Id(name);
    private static Formula N(int n) => new Formula.Number(n);
    private static Formula Real => Seq(Mathbb, Grp(V("R")));
    private static Formula Natural => Seq(Mathbb, Grp(V("N")));
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula Qualified(string owner, string name) =>
        Seq(Operatorname, Grp(V(owner)), Dot, Operatorname, Grp(V(name)));
    private static Formula App(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, V(name), Colon, Sp, type, Comma, Sp, body);
    private static Formula Some(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, V(name), Colon, Sp, type, Comma, Sp, body);
    private static Formula Arrow(Formula a, Formula b) => new Formula.TypeArrow(a, b);
    private static Formula Member(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.MemberOf, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Icc => App(Qualified("Set", "Icc"), N(0), N(1));
    private static Formula Claim() => new Formula.Relation(V("claim"), FormulaRelationOperator.Equal,
        Parenthesized(All("v", Natural, All("G", Call("SimpleGraph", Call("Fin", V("v"))),
            Some("qf", Arrow(Real, Real),
                And(Parenthesized(All("beta", Real, Imp(Member(V("beta"), Icc),
                    And(Member(Call("qf", V("beta")), Icc),
                        Call("IsMaxOn", Parenthesized(Call("tDens", V("G"), V("beta"))),
                            Icc, Call("qf", V("beta"))))))), Call("MonotoneOn", V("qf"), Icc)))))));
}
