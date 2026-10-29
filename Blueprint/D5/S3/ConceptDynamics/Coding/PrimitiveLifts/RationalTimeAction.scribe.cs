using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Coding.PrimitiveLifts;

internal sealed class RationalTimeActionDocument : IScribeDocumentDefinition
{
    private static Formula I(string n) => F.Id(n);
    private static Formula.BoundVariable B(string n, Formula t) => new(FormulaIdentifier.Create(n),t);
    private static Formula Q(Formula f, params Formula.BoundVariable[] v) =>
        new Formula.BindMany(FormulaQuantifier.ForAll,[..v],f);
    private static Formula Ex(Formula f, params Formula.BoundVariable[] v) =>
        new Formula.BindMany(FormulaQuantifier.Exists,[..v],f);
    private static Formula And(Formula a, Formula b) => Seq(Open,Open,a,Close,Sp,Land,Sp,Open,b,Close,Close);
    private static Formula App(Formula f, Formula x) => Call("apply",f,x);
    private static Formula Carrier => Call("Sigma",I("X"));
    private static Formula RatGroup => Call("Multiplicative",I("Rational"));
    private static Formula Action => App(I("rho"),I("q"));
    private static Formula Deck => Call("jointDeck",I("A"),I("a"));
    private static Formula DeckLaw => Q(Equal(App(Action,App(Deck,I("x"))),
        App(Deck,App(Action,I("x")))),B("q",RatGroup),B("a",I("H")),B("x",Carrier));
    private static Formula TimeLaw => Equal(
        App(I("rho"),Call("ofAdd",D(1))),Call("jointTime",I("A")));
    private static Formula Statement => Q(Seq(
        OpenBracket,Call("Group",I("H")),CloseBracket,
        Q(Seq(Open,Q(Call("Infinite",Call("IsotypicClass",I("A"),I("i"))),B("i",I("iota"))),
            Close,Sp,Implies,Sp,Ex(And(DeckLaw,TimeLaw),B("rho",Call("MonoidHom",RatGroup,
                Call("Perm",Carrier))))),
            B("iota",I("Type")),B("X",Call("Map",I("iota"),I("Type"))),
            B("A",Call("DependentReturnAtlases",I("H"),I("X"))))),B("H",I("Type")));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Infinite isotypic multiplicity permits a single coherent rational-time action on the complete family.",
        H("Coherent rational time from infinite multiplicity"),Blocks(
        Paragraph(Text("Let H be an arbitrary group, iota an arbitrary index type, X:iota->Type a dependent family and A_i:ReturnAtlas H (X i) complete signed return charts. The universes of H, iota and the fibers may vary independently. The charts have positive natural periods d_i and arbitrary holonomies h_i. Isotypic A i j means d_i=d_j and there is b:H satisfying b*h_j=h_i*b. Its actual class is the subtype {j:iota | Isotypic A i j}. Assume every such class is infinite, with no countability restriction on the class or index type. The empty family is permitted.")),
        Paragraph(Text("Write T=jointTime A and D_a=jointDeck A a on Sigma X. Multiplicative Rational is the multiplicative type synonym for the additive rational group: its identity is ofAdd(0), and ofAdd(1) is the unit of time, not the group identity. MonoidHom into Perm means an actual group homomorphism, including its identity and composition laws; negative times therefore act by inverse permutations.")),
        Describe.Lean(DescribeId.Create("exists-rational-time-action"),
            DeclarationHandle.Create("D5/S3/ConceptDynamics/Coding/PrimitiveLifts/RationalTimeAction.exists_rational_time_action"),
            H("One rational action with the prescribed time-one map"),
            StatementSource.FromAuthor(Disp(Statement)),AssessedProvenance.FromRepo(),Blocks(
                Paragraph(Text("There exists rho:Multiplicative Rational ->* Perm(Sigma X) such that for every q:Multiplicative Rational, a:H and x:Sigma X, rho(q)(D_a(x))=D_a(rho(q)(x)), and the underlying function of rho(ofAdd(1)) is exactly T. This is one homomorphism for all rational times, not a separate choice of an nth root for each positive n. No nilpotence, commutativity, divisibility or root-existence assumption is made on H or on the holonomies."))),DescribeRole.Theorem),
        Paragraph(Text("For a permutation U of a carrier Y, use the rational phase P={r:Rational | 0<=r and r<1}. The fractional suspension sends (r,y) at rational time q to (fract(r+q),U^floor(r+q)(y)). The floor is the signed integer floor, and powers are integer powers of the permutation, including negative exponents. The identity floor(fract(a)+b)+floor(a)=floor(a+b) supplies the exact carry in the homomorphism law. At time 1 the phase is unchanged and y becomes U(y). Every map commuting with U also commutes with its signed powers, and hence its phasewise lift commutes with the whole suspension.")),
        Paragraph(Text("The phase P is countable and nonempty. For every infinite actual isotypic index class C, infinite_block_equiv gives C equivalent to C times P: multiplication by a nonzero countable cardinal preserves every infinite cardinal. After swapping the factors, this absorbs the suspension phase into the existing multiplicity. It requires no countable enumeration of C.")),
        Paragraph(Text("Quotient iota by isotypy and choose one representative chart in each occurring class. The chartGauge equivalence identifies every chart in that class with its representative, intertwining time and all deck maps by the actual holonomy-conjugacy witness. The sigma-fiber equivalence separates the quotient class and its actual indices. Absorb P only into this index factor; the representative-carrier time permutation fixes the index. Assemble its suspension over all classes and conjugate the resulting permutation homomorphism through the complete dependent equivalence back to Sigma X. The transported time-one function is precisely jointTime, and all rational times commute with the original jointDeck maps.")),
        Paragraph(Text("The proof uses classical choice for quotient representatives, holonomy gauges and cardinal equivalences. It proves an algebraic action; no topology, continuity, real-time extension or physical realization is asserted. The construction gives coherent roots by a rational group action and therefore strengthens the separately chosen finite-order roots supplied by the earlier arbitrary-index root criterion. No literature-priority claim is made."))
        )));
}
