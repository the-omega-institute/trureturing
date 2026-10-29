using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Coding.PrimitiveLifts;

internal sealed class CoherentRationalTimeCriterionDocument : IScribeDocumentDefinition
{
    private static Formula I(string n) => F.Id(n);
    private static Formula.BoundVariable B(string n, Formula t) => new(FormulaIdentifier.Create(n), t);
    private static Formula Q(Formula f, params Formula.BoundVariable[] v) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. v], f);
    private static Formula Ex(Formula f, params Formula.BoundVariable[] v) =>
        new Formula.BindMany(FormulaQuantifier.Exists, [.. v], f);
    private static Formula And(Formula a, Formula b) =>
        Seq(Open,Open,a,Close,Sp,Land,Sp,Open,b,Close,Close);
    private static Formula App(Formula f, Formula x) => Call("apply",f,x);
    private static Formula RatGroup => Call("Multiplicative",I("Rational"));
    private static Formula OneTime => Call("ofAdd",D(1));
    private static Formula Carrier => Call("Sigma",I("X"));
    private static Formula Ai => App(I("A"),I("i"));
    private static Formula Action => App(I("rho"),I("q"));
    private static Formula Deck => Call("jointDeck",I("A"),I("a"));
    private static Formula DeckLaw => Q(Equal(App(Action,App(Deck,I("x"))),
        App(Deck,App(Action,I("x")))),B("q",RatGroup),B("a",I("H")),B("x",Carrier));
    private static Formula ActionExists => Ex(And(DeckLaw,
        Equal(Call("underlyingFunction",App(I("rho"),OneTime)),Call("jointTime",I("A")))),
        B("rho",Call("MonoidHom",RatGroup,Call("Perm",Carrier))));
    private static Formula FiniteCondition => Q(Seq(
        Call("Finite",Call("IsotypicClass",I("A"),I("i"))),Sp,Implies,Sp,
        And(Equal(Call("period",Ai),D(1)),
            Ex(Equal(App(I("phi"),OneTime),Call("holonomy",Ai)),
                B("phi",Call("MonoidHom",RatGroup,I("H")))))),B("i",I("iota")));
    private static Formula Statement => Q(
        Seq(OpenBracket,Call("Group",I("H")),CloseBracket,
            Q(Seq(Open,ActionExists,Close,Sp,F.Iff,Sp,Open,FiniteCondition,Close),
                B("iota",Call("TypeAt",I("w"))),
                B("X",Call("Map",I("iota"),Call("TypeAt",I("v")))),
                B("A",Call("DependentReturnAtlases",I("H"),I("X"))))),
        B("u",I("Universe")),B("v",I("Universe")),B("w",I("Universe")),
        B("H",Call("TypeAt",I("u"))));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A coherent rational action on an arbitrary return-atlas family exists exactly when its finite actual isotypic classes have period one and coherently extensible holonomy.",
        H("The full coherent rational-time criterion"),Blocks(
        Paragraph(Text("The universes u, v and w are independent. H:Type u is any group, iota:Type w is any index type, X:iota->Type v is a dependent family, and A_i:ReturnAtlas H (X i) is a complete signed return chart for each actual index i. The family may be empty, and finite and infinite isotypic classes may coexist. No commutativity, common exponent, nilpotence or holonomy-centrality hypothesis is imposed on H.")),
        Paragraph(Text("Each chart has a positive natural period d_i and holonomy h_i. Its points point(t,z), for t:Int and z:H, cover X i and satisfy point(t,z)=point(s,w) exactly when t=s+d_i*m and z*h_i^m=w for an integer m. Time advances t by one; deck(a) multiplies z on the left. On the dependent disjoint union Sigma X these give T=jointTime A and D_a=jointDeck A a. Isotypic A i j means d_i=d_j and b*h_j=h_i*b for some b:H. IsotypicClass(A,i) is the actual subtype {j:iota | Isotypic A i j}, including every occurrence of an isotypic chart; it is not the quotient of types.")),
        Describe.Lean(DescribeId.Create("coherent-rational-time-iff"),
            DeclarationHandle.Create("D5/S3/ConceptDynamics/Coding/PrimitiveLifts/CoherentRationalTimeCriterion.coherent_rational_time_iff"),
            H("One action, with an exact necessary and sufficient condition"),
            StatementSource.FromAuthor(Disp(Statement)),AssessedProvenance.FromRepo(),Blocks(
                Paragraph(Text("Multiplicative Rational is the additive rational group written multiplicatively. Its identity is ofAdd(0), whereas ofAdd(1) is unit time. The existential quantifier chooses one monoid homomorphism rho into the permutation group of the entire Sigma X. Every rho(q) commutes with every specified D_a, and equality at unit time is equality of underlying functions on the whole carrier. The right side constrains precisely the finite actual classes: for every such i, d_i=1 and there exists a genuine homomorphism phi:Multiplicative Rational ->* H with phi(ofAdd(1))=h_i. No condition on period or holonomy is imposed on infinite actual classes."))),DescribeRole.Theorem),
        Paragraph(Text("For necessity, the homomorphism law and commutativity of the rational source imply that every rho(q) commutes with T=rho(ofAdd(1)). PrimeOrbitRootCriterion.component_constant then makes the first component of rho(q)(i,x) independent of x. Evaluating it at point(0,1) defines an action sigma on the actual index set. The identity and multiplication laws follow from those of rho and this component constancy. PrimeOrbitRootCriterion.routing_isotypic shows that sigma preserves the actual isotypic classes, using the injectivity of the permutation rho(q).")),
        Paragraph(Text("Fix a finite actual class C_i and restrict the index action to it. A group-source homomorphism into endomorphisms gives genuine permutations via toHomPerm. For any homomorphism f from Multiplicative Rational to a finite group K, put N=Nat.card K>0. The identity q=(ofAdd(toAdd(q)/N))^N and Mathlib's pow_card_eq_one' imply f(q)=1. Apply this to the permutation group of C_i. Every rational time therefore fixes i. Restrict rho to the subtype of Sigma X with first component i, transport through Equiv.sigmaSubtype i, and obtain one genuine rational permutation homomorphism on X i. RationalReturnAtlasCriterion.rational_time_action_criterion now gives exactly d_i=1 and the coherent holonomy homomorphism into H, including when H is noncommutative.")),
        Paragraph(Text("For sufficiency, let F(i) mean that the actual class C_i is finite. Isotypy identifies actual classes by the equivalence that keeps their indices, so F is invariant under isotypy. On the subfamily {i | F(i)}, the single-chart criterion supplies a rational action on each X i; their dependent disjoint union is a rational permutation homomorphism. On the complementary subfamily {i | not F(i)}, its restricted actual class is equivalent to the original class: all members of that class also fail F. It is therefore infinite. Apply RationalTimeAction.exists_rational_time_action once to this complementary subfamily, with no holonomy restriction.")),
        Paragraph(Text("Finally, Equiv.subtypeSigmaEquiv and Equiv.sumCompl identify Sigma X with the binary sum of these two dependent subfamilies. Equiv.Perm.sumCongrHom combines their rational actions, and conjugation through this partition equivalence gives the required action on the original carrier. The partition equivalence intertwines the specified deck maps and time, so these equalities hold on the entire original family, including either empty part. The identity, negative-time, addition and denominator-compatibility laws all come from the genuine monoid homomorphisms.")),
        Paragraph(Text("UniversalRootCriterion concerns a weaker requirement: a separately chosen root for every positive degree, with no compatibility among choices. Such independent root existentials do not supply the coherent homomorphisms used here. The present proof uses the existing all-infinite construction and single-chart criterion and supplies the missing finite-class routing, restriction and mixed-family assembly. This is an algebraic criterion, with classical choice permitted; it makes no literature-priority, continuity, real-time extension or physical-realization claim."))
        )));
}
