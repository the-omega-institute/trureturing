using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Coding.PrimitiveLifts;

internal sealed class FiniteOrbitRootCriterionDocument : IScribeDocumentDefinition
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
    private static Formula Time => Call("jointTime",I("A"));
    private static Formula Deck(Formula a) => Call("jointDeck",I("A"),a);
    private static Formula Div(Formula a, Formula b) => Call("natDiv",a,b);
    private static Formula Local(Formula q, Formula a) => Call("Local",q,a);
    private static Formula Root => Ex(And(Q(Equal(App(I("R"),App(Deck(I("a")),I("x"))),
        App(Deck(I("a")),App(I("R"),I("x")))),B("a",I("H")),B("x",Carrier)),
        Equal(Call("iterate",I("R"),I("k")),Time)),B("R",Call("Map",Carrier,Carrier)));
    private static Formula Allowed => And(Seq(D(0),Sp,Lt,Sp,I("ell")),And(Call("Divides",I("ell"),I("k")),
        Local(Div(I("k"),I("ell")),Ai(I("i")))));
    private static Formula Multiplicities => Q(Ex(And(
        Equal(Call("sum",I("L")),Call("NatCard",Call("IsotypicClass",I("A"),I("i")))),
        Q(Seq(Call("Mem",I("ell"),I("L")),Sp,Implies,Sp,Allowed),B("ell",I("Nat")))),
        B("L",Call("List",I("Nat")))),B("i",I("iota")));
    private static Formula Scope(Formula f) => Q(Seq(
        OpenBracket,Call("Group",I("H")),CloseBracket,
        Q(Seq(OpenBracket,Call("Finite",I("iota")),CloseBracket,
            Q(Seq(Seq(D(0),Sp,Lt,Sp,I("k")),Sp,Implies,Sp,Open,f,Close),B("k",I("Nat")))),
            B("iota",I("Type")),B("X",Call("Map",I("iota"),I("Type"))),
            B("A",Call("DependentReturnAtlases",I("H"),I("X"))))),B("H",I("Type")));
    private static Formula ScopeArbitrary(Formula f) => Q(
        Seq(
            OpenBracket,Call("Group",I("H")),CloseBracket,
            Q(
                Q(Seq(Seq(D(0),Sp,Lt,Sp,I("k")),Sp,Implies,Sp,Open,f,Close),B("k",I("Nat"))),
                B("iota",I("Type")),B("X",Call("Map",I("iota"),I("Type"))),
                B("A",Call("DependentReturnAtlases",I("H"),I("X"))))),
            B("H",I("Type")));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Allowed component cycles give an exact additive criterion for equivariant roots on any finite chart family.",
        H("Finite families and exact root multiplicities"),Blocks(
        Paragraph(Text("Let H be any group, iota any finite type, X:iota->Type any dependent family, and A_i:ReturnAtlas H (X i) complete signed return charts. No finiteness or commutativity is required of H. The finite index type may be empty. Write d_i>0 for the atlas period and h_i for the holonomy. Each chart covers its entire carrier and satisfies A_i(t,z)=A_i(s,w) exactly when t=s+d_i*m and z*h_i^m=w for some integer m. These periods describe the primitive base returns, rather than the ordinary periods of the lifted time maps.")),
        Paragraph(Text("On Sigma X, T(i,x)=(i,A_i.time(x)) and D_a(i,x)=(i,A_i.deck(a,x)) are the existing jointTime and jointDeck. Isotypic A i j means d_i=d_j and there exists b:H with b*h_j=h_i*b. It is an equivalence relation, expressing equal periods and conjugate holonomy. IsotypicClass(A,i) denotes the subtype {j:iota | Isotypic A i j}, and NatCard is its finite cardinality. Local q B is the existing signed local equation: there exist s:Fin B.period, m:Int and b:H with b commuting with B.holonomy, q*s.val=1+B.period*m, and b^q*B.holonomy^m=1. The integer m is unrestricted in sign.")),
        Describe.Lean(DescribeId.Create("finite-orbit-root-criterion"),
            DeclarationHandle.Create("D5/S3/ConceptDynamics/Coding/PrimitiveLifts/FiniteOrbitRootCriterion.finite_root_criterion"),
            H("Exact additive multiplicity criterion"),
            StatementSource.FromAuthor(Disp(Scope(Seq(Open,Root,Close,Sp,F.Iff,Sp,Open,Multiplicities,Close)))),
            AssessedProvenance.FromRepo(),Blocks(
                Paragraph(Text("For every positive natural k, an unrestricted map R:Sigma X->Sigma X with R(D_a(x))=D_a(R(x)) for all a,x and R iterated k times equal to T exists if and only if, for every index i, there is an actual finite list L of natural block lengths whose sum is the cardinality of {j | Isotypic A i j}, and each ell in L is positive, divides k, and satisfies Local (k/ell) A_i. Repeated lengths are permitted. The statement assumes neither bijectivity, time commutation nor component preservation of R."))),DescribeRole.Theorem),
        Describe.Lean(DescribeId.Create("arbitrary-orbit-root-criterion"),
            DeclarationHandle.Create("D5/S3/ConceptDynamics/Coding/PrimitiveLifts/FiniteOrbitRootCriterion.arbitrary_root_criterion"),
            H("Arbitrary-index criterion with infinite fibers"),
            StatementSource.FromAuthor(Disp(ScopeArbitrary(Seq(Open,Root,Close,Sp,F.Iff,Sp,Open,Multiplicities,Close)))),
            AssessedProvenance.FromRepo(),Blocks(
                Paragraph(Text("The same exact equivalence holds for every index type iota, with no Finite iota premise. For every positive k, the unrestricted equivariant kth root exists exactly when each isotypic class has a finite list of allowed positive block lengths whose sum is Nat.card of that class. The full telescope retains arbitrary H, dependent universes X:iota->Type and A:DependentReturnAtlases H X, and permits noncommutative or infinite groups, all positive k, and the empty family.")),
                Paragraph(Text("For an infinite isotypic fiber C := {j // Isotypic A i j}, the construction uses an actual equivalence C ≃ C × Fin k, obtained from the infinite-cardinal arithmetic for nonempty Fin k. It does not replace C by the empty type: C remains the nonempty infinite block-index carrier. Mathlib's Nat.card C = 0 convention and the witness list [] encode only the absence of a finite multiplicity obstruction; they do not assert that C is empty. Finite fibers use the original finite list blocks, and the two branches are assembled by the existing roots_of_blocks construction."))),DescribeRole.Theorem),
        Paragraph(Text("Necessity begins with R^k=T. Since T is injective and k is positive, R is injective; R also commutes with T. Completeness of each chart and deck equivariance make the output component constant on that whole chart. Thus R induces a component permutation sigma with sigma^k=id. The existing routing_isotypic proof uses ReturnAtlasFiniteCovers.normal_form and the full fiberEquiv: an injective factor cannot have positive covering degree greater than one, even when H is infinite. Hence every component is isotypic to its image under sigma.")),
        Paragraph(Text("Fix i and restrict sigma to the finite class {j | Isotypic A i j}. The SameCycle quotient includes both moving cycles and fixed points. For a cycle representative j its length ell is minimalPeriod(sigma,j), which is positive and divides k. The existing iterate-distinctness and iterate-mod-period identities identify the entire cycle with Fin ell, so its actual cardinality is ell. Fintype's sigma-fiber equivalence then makes the class cardinality the sum of these lengths.")),
        Paragraph(Text("Because sigma^ell fixes j, the actual map R^ell restricts to X_j. Its (k/ell)-fold iterate is T_j, and it remains deck equivariant. Apply ReturnAtlas.root_criterion to obtain Local (k/ell) A_j. Equal atlas periods and holonomy conjugacy give a chart equivalence intertwining deck and time, so the local root transfers to A_i. These are the required allowed lengths for the fixed class.")),
        Paragraph(Text("For sufficiency, quotient iota by Isotypic and choose one representative in each class. Its length list L gives a finite type of positions (t,j) with t:Fin L.length and j:Fin L[t]. Its cardinality is L.sum, so a finite equivalence partitions the actual class into precisely those blocks. The construction chooses no index in an empty class; when iota is empty, both the quotient and the constructed carrier are empty.")),
        Paragraph(Text("Choose a local q-root f on the representative chart of each block, where q=k/ell. Gauges built from the existing complete coordinates and right multiplication identify every chart in that block with the representative chart. On Fin ell times that carrier define C(j,y)=((j.val+1) mod ell, f^floor((j.val+1)/ell)(y)). The reused cycleStep_iterate identity gives C^n(j,y)=((j.val+n) mod ell, f^floor((j.val+n)/ell)(y)). Since ell divides k, at n=k the first coordinate returns to j and the second becomes f^(k/ell)(y)=T(y). Deck equivariance of f makes every carry deck equivariant. Combine the block maps and conjugate through the full dependent chart equivalence to obtain R on Sigma X.")),
        Paragraph(Text("The numerical condition is membership in the additive monoid generated by the allowed positive divisors of k. A greatest-common-divisor divisibility condition alone need not express this membership: for example, sums of 2 and 3 include every natural number at least 2 and exclude 1, although their greatest common divisor is 1. The theorem keeps the actual list of lengths. It extends the earlier two-chart, three-chart and prime-cardinality mechanisms by retaining all component-cycle multiplicities. No literature priority is claimed."))
        )));
}
