using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Coding.PrimitiveLifts;

internal sealed class BoundedExponentRootCriterionDocument : IScribeDocumentDefinition
{
    private static Formula I(string n) => F.Id(n);
    private static Formula.BoundVariable B(string n, Formula t) => new(FormulaIdentifier.Create(n), t);
    private static Formula Q(Formula f, params Formula.BoundVariable[] v) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. v], f);
    private static Formula Ex(Formula f, params Formula.BoundVariable[] v) =>
        new Formula.BindMany(FormulaQuantifier.Exists, [.. v], f);
    private static Formula And(Formula a, Formula b) => Seq(Open,Open,a,Close,Sp,Land,Sp,Open,b,Close,Close);
    private static Formula App(Formula f, Formula x) => Call("apply",f,x);
    private static Formula Ai(Formula i) => App(I("A"),i);
    private static Formula Carrier => Call("Sigma",I("X"));
    private static Formula Deck(Formula a) => Call("jointDeck",I("A"),a);
    private static Formula Root => Ex(And(Q(Equal(App(I("R"),App(Deck(I("a")),I("q"))),
        App(Deck(I("a")),App(I("R"),I("q")))),B("a",I("H")),B("q",Carrier)),
        Equal(Call("iterate",I("R"),I("k")),Call("jointTime",I("A")))),
        B("R",Call("Map",Carrier,Carrier)));
    private static Formula AllRoots => Q(Seq(D(0),Sp,Lt,Sp,I("k"),Sp,Implies,Sp,Root),B("k",I("Nat")));
    private static Formula FiniteClasses => Q(Seq(
        Call("Finite",Call("IsotypicClass",I("A"),I("i"))),Sp,Implies,Sp,
        And(Equal(Call("period",Ai(I("i"))),D(1)),Equal(Call("holonomy",Ai(I("i"))),D(1)))),
        B("i",I("iota")));
    private static Formula Scope(Formula f) => Q(Q(Seq(
        OpenBracket,Call("Group",I("H")),CloseBracket,
        Call("ExponentExists",I("H")),Sp,Implies,Sp,
        Q(f,B("iota",Call("TypeAt",I("w"))),
            B("X",Call("Map",I("iota"),Call("TypeAt",I("v")))),
            B("A",Call("DependentReturnAtlases",I("H"),I("X"))))),
        B("H",Call("TypeAt",I("u")))),
        B("u",I("Universe")),B("v",I("Universe")),B("w",I("Universe")));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For a group of bounded exponent, roots of every positive degree exist precisely when every finite actual isotypic class has trivial return data.",
        H("Universal roots over groups of bounded exponent"),Blocks(
        Paragraph(Text("Let u, v and w be independent universes. Let H:Type u be any group satisfying Mathlib's Monoid.ExponentExists H: there is a positive natural E with b^E=1 for every b:H. This assumption allows infinite and noncommutative groups. Let iota:Type w be arbitrary, X:iota->Type v a dependent family, and A_i:ReturnAtlas H (X i) complete signed return atlases. The family may be empty and may contain both finite and infinite actual isotypic classes.")),
        Paragraph(Text("Write d_i=(A_i).period>0 and h_i=(A_i).holonomy. The complete chart covers X i by A_i.point(t,z), for t:Int and z:H, with equality exactly when t=s+d_i*m and z*h_i^m=w for an integer m. Its time adds one to t and its left deck action multiplies z on the left. On Sigma X, T=jointTime A and D_a=jointDeck A a act by these maps within each component. Isotypic A i j means equal periods and holonomy conjugacy: d_i=d_j and some b:H satisfies b*h_j=h_i*b. IsotypicClass(A,i) is the actual subtype {j:iota | Isotypic A i j}. ExponentExists and TypeAt in the formula denote the Mathlib predicate and the indicated universe, respectively.")),
        Describe.Lean(DescribeId.Create("bounded-exponent-universal-rootability"),
            DeclarationHandle.Create("D5/S3/ConceptDynamics/Coding/PrimitiveLifts/BoundedExponentRootCriterion.universal_rootability_iff"),
            H("Exact arbitrary-family criterion"),
            StatementSource.FromAuthor(Disp(Scope(Seq(Open,AllRoots,Close,Sp,F.Iff,Sp,Open,FiniteClasses,Close)))),
            AssessedProvenance.FromRepo(),Blocks(
                Paragraph(Text("For every positive natural k there exists an actual map R:Sigma X->Sigma X commuting with every left deck map and satisfying R iterated k times equal to T if and only if every finite actual isotypic class has period one and holonomy one. R may route between components. Neither component preservation nor bijectivity is assumed. The existential choice of R is inside the quantifier over k; no compatibility, commutation or coherent choice between different degrees is required."))),DescribeRole.Theorem),
        Paragraph(Text("The proof uses FiniteOrbitRootCriterion.arbitrary_root_criterion exactly on this entire dependent carrier. For a fixed positive degree k, that criterion characterizes a root by a list L of positive block lengths for each i, summing to Nat.card C_i, where C_i is the actual isotypic class. Every ell in L divides k and satisfies Local (k/ell) A_i. Here Local q A_i means that there exist s:Fin d_i, m:Int and b:H with Commute b h_i, q*s.val=1+d_i*m, and b^q*h_i^m=1.")),
        Paragraph(Text("For necessity, fix a finite C_i. It contains i by reflexivity of Isotypic, so N=Nat.card C_i is positive. Choose the single test degree k=N!*d_i*E, using the positive Mathlib exponent E=Monoid.exponent H. The resulting list has positive sum N and therefore has an entry ell. Since all entries are nonnegative, ell<=N, so Nat.dvd_factorial gives ell dividing N!. Consequently both d_i and E divide q=k/ell. This bound accounts for every possible routing cycle in that finite class; it makes no assertion about routing in an infinite class.")),
        Paragraph(Text("The local phase equation q*s.val=1+d_i*m now forces d_i to divide one. Positivity gives d_i=1. The sole value of Fin 1 is zero, and the same integer equation gives m=-1. Since E divides q, the common exponent law gives b^q=1. The holonomy equation reduces to h_i inverse=1, hence h_i=1. The argument uses no commutation among different group elements and needs no nilpotence or finite cardinality of H.")),
        Paragraph(Text("For sufficiency, fix k>0. In a finite C_i use a list of N copies of one. Its sum is N, and each entry has the required local equation with d_i=1, h_i=1, s=0, m=-1 and b=1. In an infinite C_i use the empty list: Mathlib's Nat.card C_i=0 convention makes the sum condition true and the entry conditions vacuous. This does not replace the infinite class by an empty carrier. The arbitrary-index criterion constructs its roots by an actual equivalence C_i equivalent to C_i times Fin k, partitioning the infinite multiplicity into full k-blocks. It assembles those blocks with all finite classes to give a root on the full Sigma X. For an empty index type both sides hold and the constructed map is the unique map on the empty carrier.")),
        Paragraph(Text("As mathematical context, a positive common exponent also forces every group homomorphism from the additive rationals to H to be trivial: for a rational r write r=E*(r/E), then the homomorphism identity and the exponent law give the image of r equal to one. This concerns coherent rational homomorphisms. The theorem above concerns separate roots at each degree and asserts no classification of rational flows. The result is derived from the existing root criterion and bounded-exponent arithmetic; no novelty or priority claim is made."))
        )));
}
