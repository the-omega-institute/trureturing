using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Coding.PrimitiveLifts;

internal sealed class UniversalRootCriterionDocument : IScribeDocumentDefinition
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
    private static Formula HolonomyRoots => Q(Seq(
        D(0),Sp,Lt,Sp,I("n"),Sp,Implies,Sp,
        Ex(Equal(Call("pow",I("b"),I("n")),Call("holonomy",Ai(I("i")))),B("b",I("H")))),
        B("n",I("Nat")));
    private static Formula FiniteClasses => Q(Seq(
        Call("Finite",Call("IsotypicClass",I("A"),I("i"))),Sp,Implies,Sp,
        And(Equal(Call("period",Ai(I("i"))),D(1)),HolonomyRoots)),
        B("i",I("iota")));
    private static Formula Scope(Formula f) => Q(
        Seq(OpenBracket,Call("Group",I("H")),CloseBracket,
            Q(f,
                B("iota",Call("TypeAt",I("w"))),
                B("X",Call("Map",I("iota"),Call("TypeAt",I("v")))),
                B("A",Call("DependentReturnAtlases",I("H"),I("X"))))),
        B("u",I("Universe")),B("v",I("Universe")),B("w",I("Universe")),
        B("H",Call("TypeAt",I("u"))));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For an arbitrary group, roots of every positive degree exist precisely when every finite actual isotypic class has period one and infinitely divisible holonomy.",
        H("Universal independent roots over arbitrary groups"),Blocks(
        Paragraph(Text("Let u, v and w be independent universes. Let H:Type u be any group, with no finiteness, exponent, commutativity or nilpotence assumption. Let iota:Type w be arbitrary, X:iota->Type v a dependent family, and A_i:ReturnAtlas H (X i) complete signed return atlases. The family may be empty and may contain both finite and infinite actual isotypic classes.")),
        Paragraph(Text("Write d_i=(A_i).period>0 and h_i=(A_i).holonomy. The complete chart covers X i by A_i.point(t,z), for t:Int and z:H, with equality exactly when t=s+d_i*m and z*h_i^m=w for an integer m. Its time adds one to t and its left deck action multiplies z on the left. On Sigma X, T=jointTime A and D_a=jointDeck A a act by these maps within each component. Isotypic A i j means equal periods and holonomy conjugacy: d_i=d_j and some b:H satisfies b*h_j=h_i*b. IsotypicClass(A,i) is the actual subtype {j:iota | Isotypic A i j}.")),
        Describe.Lean(DescribeId.Create("universal-rootability-iff"),
            DeclarationHandle.Create("D5/S3/ConceptDynamics/Coding/PrimitiveLifts/UniversalRootCriterion.universal_rootability_iff"),
            H("Exact arbitrary-family criterion"),
            StatementSource.FromAuthor(Disp(Scope(Seq(Open,AllRoots,Close,Sp,F.Iff,Sp,Open,FiniteClasses,Close)))),
            AssessedProvenance.FromRepo(),Blocks(
                Paragraph(Text("For every positive natural k there exists an actual map R:Sigma X->Sigma X commuting with every left deck map and satisfying R iterated k times equal to T if and only if every finite actual isotypic class has period one and its holonomy has an n-th root in H for every positive n. R may route between components. Neither component preservation nor bijectivity is assumed. The existential choice of R is inside the quantifier over k; no compatibility, commutation or coherent choice between different degrees is required."))),DescribeRole.Theorem),
        Paragraph(Text("The proof applies FiniteOrbitRootCriterion.arbitrary_root_criterion exactly on this entire dependent carrier. For a fixed positive degree k, that criterion characterizes a root by a list L of positive block lengths for each i, summing to Nat.card C_i, where C_i is the actual isotypic class. Every ell in L divides k and satisfies Local (k/ell) A_i. Here Local q A_i means that there exist s:Fin d_i, m:Int and b:H with Commute b h_i, q*s.val=1+d_i*m, and b^q*h_i^m=1.")),
        Paragraph(Text("For necessity, fix a finite C_i and put N=Nat.card C_i>0. For each positive n, test k=N!*d_i*n. The resulting list has positive sum N and therefore has an entry ell. Since every entry is positive and sums to N, ell<=N, so Nat.dvd_factorial gives ell dividing N!. Thus q=k/ell is divisible by both d_i and n. The local phase equation q*s.val=1+d_i*m then forces d_i to divide one, hence d_i=1; the sole value of Fin 1 gives s=0 and the same equation gives m=-1. The holonomy equation becomes b^q*h_i^-1=1, so b^q=h_i. Writing q=n*r extracts (b^r)^n=h_i. Taking n=1 supplies the period clause, while each positive n supplies its own root.")),
        Paragraph(Text("For sufficiency, fix k>0. In a finite C_i use a list of N copies of one. Choose an element b with b^k=h_i. Since h_i=b^k, b commutes with h_i by Commute.self_pow; with d_i=1, s=0 and m=-1 this is exactly Local k A_i. In an infinite C_i use the empty list: the arbitrary-index criterion partitions the actual infinite isotypic fiber into full k-blocks, so no multiplicity condition is imposed. The construction retains those infinite classes as genuine carriers. The criterion then assembles the blocks into a global deck-equivariant root.")),
        Paragraph(Text("Independent roots are chosen separately for each degree; no coherent rational action is asserted. The theorem is an arbitrary-group statement and makes no novelty or priority claim."))
        )));
}
