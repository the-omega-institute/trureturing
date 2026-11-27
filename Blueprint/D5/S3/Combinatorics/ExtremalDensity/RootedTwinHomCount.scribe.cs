using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.ExtremalDensity;

internal sealed class RootedTwinHomCountDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Two rooted copies joined through a centre satisfy a general quarter-square homomorphism bound.",
        H("The rooted-twin homomorphism bound"),
        Blocks(Describe.Lean(DescribeId.Create("rooted-twin-quarter-bound"),
            DeclarationHandle.Create("D5/S3/Combinatorics/ExtremalDensity/RootedTwinHomCount.quarter_bound"),
            H("A fixed centre in an asymmetric host"),
            StatementSource.FromAuthor(Disp(Statement())), AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("Let A : Type u and B : Type v be arbitrary finite types in independent universe levels u and v, H a digraph on A, w a vertex of H, "
                    + "R an asymmetric relation on B, and t a vertex of B. Put D = rootedTwin H w. "
                    + "Its vertex type is Option (Bool × A): none is the new centre, and some (false,a) "
                    + "and some (true,a) are the two copies of a. Within either copy the arcs are exactly "
                    + "those of H. The only additional arcs are some (false,w) → none and none → some (true,w). "
                    + "There are no other cross-copy or centre arcs. RelHom counts every adjacency-preserving "
                    + "map; neither injectivity nor disjoint images of the two copies is required.")),
                Paragraph(Text("The proof is Omega.RootedTwinHomCount.quarter_bound in "
                    + "OmegaMath.Combinatorics.RootedTwinHomCount. Restriction to the two copies gives an "
                    + "equivalence between the fibre f(none)=t and the product of the H-homomorphisms g "
                    + "with R(g(w),t) and the H-homomorphisms h with R(t,h(w)). Assembly assigns t to the "
                    + "centre and uses g and h on their respective copies. All internal and centre arcs "
                    + "are preserved, and restriction and assembly are inverse. This correspondence requires "
                    + "neither finiteness nor asymmetry.")),
                Paragraph(Text("Write a and b for the sizes of these two homomorphism classes and N for "
                    + "the number of all H-homomorphisms into R. Asymmetry prevents any homomorphism from "
                    + "belonging to both classes, so their disjoint sum injects into all H-homomorphisms. "
                    + "Thus a+b≤N and 4ab≤(a+b)²≤N². This division-free bound includes N=0, loops in H "
                    + "and singleton hosts. A chosen t already supplies an element of B. Completeness of "
                    + "the host and positivity of a homomorphism count are not assumptions.")),
                Paragraph(Text("This is the structural counting step of Proposition 5.2 in Xiaoyu He, "
                    + "Nitya Mani, Jiaxi Nie, Nathan Tung and Fan Wei, New Sidorenko-type inequalities in "
                    + "tournaments, https://arxiv.org/html/2512.11222v1 . The proposition uses tournament "
                    + "hosts and feeds the construction toward Theorem 1.3 and the conjecture that every "
                    + "tree admits a tournament anti-Sidorenko orientation. Here the counting inequality "
                    + "holds for every asymmetric host relation. The final comparison uses a+b≤N: maps "
                    + "whose root is sent to t, or to a vertex unrelated to t, need not belong to either "
                    + "class. This theorem establishes this counting step; the general tree conjecture "
                    + "remains open."))), DescribeRole.Theorem))));

    private static Formula V(string s) => FormulaDsl.Id(s);
    private static Formula Call(string s, params Formula[] xs) => new Formula.FunctionCall(FormulaIdentifier.Create(s), [.. xs]);
    private static Formula App(Formula f, params Formula[] xs) => new Formula.Apply(f, [.. xs]);
    private static Formula All(string s, Formula t, Formula b) => Seq(Forall, Sp, V(s), Colon, Sp, t, Comma, Sp, b);
    private static Formula Arr(Formula a, Formula b) => new Formula.TypeArrow(a,b);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal,b);
    private static Formula Qualified(string a, string b) => Seq(Operatorname, Grp(V(a)), Dot, Operatorname, Grp(V(b)));
    private static Formula Adj(Formula h) => Seq(h, Dot, Operatorname, Grp(V("Adj")));
    private static Formula Card(Formula t) => App(Qualified("Nat","card"), t);
    private static Formula Statement()
    {
        var A = V("A"); var B = V("B"); var Hh = V("H"); var R = V("R"); var t = V("t");
        var asym = All("x", B, All("y", B, new Formula.Logic(Call("R",V("x"),V("y")),
            FormulaLogicOperator.Implies, Seq(Neg, Sp, Call("R",V("y"),V("x"))))));
        var fibre = Seq(OpenBrace, V("f"), Colon, Sp,
            Call("RelHom", Adj(Call("rootedTwin", Hh, V("w"))), R), Sp, Mid, Sp,
            Eq(Call("f",V("none")),t), CloseBrace);
        var bound = new Formula.Relation(new Formula.Binary(D(4), FormulaBinaryOperator.Multiply, Card(fibre)),
            FormulaRelationOperator.LessThanOrEqual, new Formula.Power(Card(Call("RelHom",Adj(Hh),R)),D(2)));
        return All("A", new Formula.Subscript(V("Type"),V("u")), All("B", new Formula.Subscript(V("Type"),V("v")), Seq(
            OpenBracket, Call("Finite",A), CloseBracket, Sp,
            OpenBracket, Call("Finite",B), CloseBracket, Sp,
            All("H",Call("Digraph",A),All("w",A,All("R",Arr(B,Arr(B,V("Prop"))),
                new Formula.Logic(Seq(Open,asym,Close),FormulaLogicOperator.Implies,All("t",B,bound))))))));
    }
}
