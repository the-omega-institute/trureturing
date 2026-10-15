using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Coding;
internal sealed class ResetNativeUnitNormalFormDocument : IScribeDocumentDefinition
{
    private static Formula I(string s) => F.Id(s);
    private static Formula.BoundVariable B(string s, Formula t) => new(FormulaIdentifier.Create(s), t);
    private static Formula All(Formula f, params Formula.BoundVariable[] v) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. v], f);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Conj(params Formula[] c)
    {
        Formula f = c[^1];
        for (int j = c.Length - 2; j >= 0; --j) f = And(c[j], f);
        return f;
    }
    private static Formula Unique(string n, Formula t, Formula law, Formula otherLaw) =>
        new Formula.BindMany(FormulaQuantifier.Exists, [B(n, t)], And(law,
            All(Imp(otherLaw, Equal(I("r"), I(n))), B("r", t))));
    private static DocumentBlock Entry(string n, string h, Formula f, string p, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(n.Replace('_', '-').ToLowerInvariant()), DeclarationHandle.Create(
            "D5/S3/ConceptDynamics/Coding/ResetNativeUnitNormalForm." + n), H(h),
            StatementSource.FromAuthor(Disp(f)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(p))), role);

    private static Formula Q => Call("QF", I("q"));
    private static Formula Nq => Call("Native", I("q"));
    private static Formula Phi(Formula z) => Call("nativeIntEquiv", I("q"), I("hq"), z);
    private static Formula Psi(Formula z) => Call("nativeGluing", I("q"), I("hq"), z);
    private static Formula Glue(Formula z) => Call("gluing", I("q"), z);
    private static Formula FP(Formula p) => Call("fp", I("q"), p);
    private static Formula Parameters => Call("product", I("Int"),
        Call("product", Call("Fin", Num(2)), Call("Fin", Num(2))));
    private static Formula Act(Formula p, Formula v) => Call("integerScale",
        Call("power", Call("neg", Num(1)), Call("val", Call("fst", Call("snd", p)))),
        Call("apply", Call("power", I("U"), Call("val", Call("snd", Call("snd", p)))),
            Call("apply", Call("integerPower", I("T"), Call("fst", p)), v)));
    private static Formula Law(Formula f, Formula p) =>
        All(Equal(Call("apply", f, I("v")), Act(p, I("v"))), B("v", I("N")));
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The full integral unit classification acts on every original native centralizer automorphism and every original full-rho value.",
        H("Original native signed time normal forms"), Blocks(
            Paragraph(Text("Native(q) is literally DimensionGroup(resetMatrix q), Theta is actual "
                + "forward resetTheta q, and Phi=nativeIntEquiv q hq is the existing integer-linear "
                + "cyclic chart. nativeGluing is Phi inverse followed by the new integral gluing. "
                + "Only an integer-linear equivalence is asserted on Native; no multiplication "
                + "or ring structure is assigned to that original group.")),
            Entry("native_gluing", "The literal original native orientation",
                All(Conj(
                    All(Equal(Psi(Phi(I("z"))), Glue(I("z"))), B("z", Q)),
                    All(Equal(Psi(Call("resetTheta", I("q"), I("v"))),
                        Call("multiply", Glue(FP(I("X"))), Psi(I("v")))), B("v", Nq)),
                    All(Equal(Psi(Call("groupAction", Call("resetMatrix", I("q")),
                        Call("ofAdd", I("true")), I("v"))),
                        Call("multiply", Glue(FP(Call("W", I("q")))), Psi(I("v")))), B("v", Nq)),
                    All(Equal(Psi(Call("integerScale", I("z"), I("v"))),
                        Call("integerScale", I("z"), Psi(I("v")))), B("z", I("Int")), B("v", Nq)),
                    All(Equal(Psi(Call("nativeStage", I("q"), I("n"), I("v"))),
                        Glue(Call("ringEquiv", I("q"), Call("pp", I("q"),
                            Call("coordinatePolynomial", I("resetLabel"), I("q"),
                                Call("apply", Call("power", Call("resetInverse", I("q"), I("hq")), I("n")),
                                    I("v"))))))),
                        B("n", I("Nat")), B("v", Call("VertexModule", I("Sign"), I("q"))))),
                    B("q", I("Nat")), B("hq", Call("positive", I("q")))),
                "positive(q) is 0<q. Time acts by the compatible pair ([X],[X]); the actual original "
                + "Sign action acts by ([W],[W])=(1,-1). Scalars are the actual integer module action. "
                + "For an original stage-n row, resetInverse^n acts BEFORE coordinatePolynomial; "
                + "these inverse transition powers coexist with forward time X. The proof reuses "
                + "all corresponding clauses of native_presentation, including its actual coefficient law.",
                DescribeRole.Theorem),
            Paragraph(Text("For every q>0 let S be the actual groupAction(resetMatrix q)(ofAdd true) on "
                + "Native(q)=DimensionGroup(resetMatrix q). The additive subgroups Kplus=ker(S-id) and "
                + "Kminus=ker(S+id) consist exactly of the fixed and negated native vectors. nativeGluing "
                + "maps their sum L to eigenLattice(q,1) plus eigenLattice(q,-1). The product coordinates "
                + "of this sum are exactly (2a,2b), with arbitrary a in Plus(q) and b in Minus(q); these "
                + "halves need not be compatible. This is also the conductor condition against every "
                + "multiplier in Plus(q) times Minus(q). Put kappaNative=commonResidue composed with "
                + "nativeGluing. Its kernel is L and it is surjective, so the additive quotient Q=Native(q)/L "
                + "is identified with Common(q) by E([v])=kappaNative(v), and has cardinality 2^q. "
                + "No multiplication is assigned to the original Native group.")),
            Paragraph(Text("The literal native_gluing time and sign clauses give "
                + "kappaNative(resetTheta q v)=[X]*kappaNative(v) for every v, where [X] is the value of "
                + "commonTimeUnit(q). Every s in the actual Sign=Multiplicative Bool acts trivially on "
                + "the residue. Its induced additive quotient map is exactly the identity. These are "
                + "applications of ResetIntegralGluing's kernel and quotient results and the generic "
                + "additive quotient APIs; they retain q=1 and every repeated-factor case.")),
            Entry("scalarUnit", "A genuine unit from an actual commuting equivalence",
                All(Call("hasType", Call("scalarUnit", I("q"), I("hq"), I("A"), I("ht")), Call("Units", Q)),
                    B("q", I("Nat")), B("hq", Call("positive", I("q"))),
                    B("A", Call("IntLinearEquiv", Nq, Nq)),
                    B("ht", Call("commutesWithForwardTime", I("q"), I("A")))),
                "commutesWithForwardTime(q,A) means forall v, A(Theta(v))=Theta(A(v)). The owning "
                + "ResetHistoryKernel.centralizingMap_scalar argument makes Phi inverse A Phi "
                + "multiplication by its value at one. A inverse also commutes; its scalar supplies "
                + "the actual inverse unit. nativeAction conjugates multiplication by this unit "
                + "through Phi, and recovers the given A on every vector. This is the already "
                + "documented cyclic scalar argument, retained as a consumed helper.",
                DescribeRole.Definition),
            Paragraph(Text("For every integer-linear automorphism A of Native(q) commuting with the literal "
                + "resetTheta q, set g0=nativeIntEquiv q hq 1 and cA=kappaNative(A(g0)). The existing "
                + "scalarUnit and nativeAction identity give kappaNative(A(v))=cA*kappaNative(v) for every v. "
                + "Map scalarUnit through the RingHom commonResidue composed with gluing to obtain a unit "
                + "with value cA. Thus A preserves L and induces an additive automorphism dA on Q satisfying "
                + "dA([v])=[A(v)] and E(dA(z))=cA*E(z) for every z. Its additive homomorphism is the generic "
                + "QuotientAddGroup.map for A with this proved subgroup stability. The existing "
                + "centralizingMap_scalar is reused for every such A; no general-q unit classification is asserted.")),
            Paragraph(Text("Specialize to every h in the original ResetFullAut(q)=fullAutSubgroup(ResetGraph q), "
                + "whose elements are homeomorphisms of History(ResetGraph q) commuting with the actual shift. "
                + "rho_time gives the required centralizer premise. This yields a representation rhoBar on Q "
                + "with rhoBar(h)([v])=[rho(q,hq,h)(v)] for every original h and v. Its scalar is the unit "
                + "cH=kappaNative(rho(q,hq,h)(g0)); E(rhoBar(h)(z))=cH*E(z) for every z. The actual original "
                + "unitShift(ResetGraph q) acts by resetTheta q on representatives and by commonTimeUnit(q) "
                + "in Common(q). Multiplication by units on Common(q) is faithful, as evaluation at one shows. "
                + "Conjugating that action through E and applying exact_common_time_order gives order q+1 "
                + "for this induced original time action when q>=2, and order one when q=1. "
                + "The application introduces no named Native theorem or additional hypothesis.")),
            Entry("native_normal_forms", "Every native centralizer and every original rho value",
                And(All(Imp(Call("commutesWithForwardTime", Num(2), I("A")),
                    Unique("p", Parameters, Law(I("A"), I("p")), Law(I("A"), I("r")))),
                        B("A", Call("IntLinearEquiv", I("N"), I("N")))),
                    All(Unique("p", Parameters,
                        Law(Call("rho", Num(2), I("positiveTwo"), I("h")), I("p")),
                        Law(Call("rho", Num(2), I("positiveTwo"), I("h")), I("r"))),
                        B("h", Call("ResetFullAut", Num(2))))),
                "Here N=Native(2), positiveTwo is the proof 0<2, T is EXACTLY "
                + "rho(2,positiveTwo,unitShift(ResetGraph 2)), and U is EXACTLY "
                + "groupAction(resetMatrix 2)(ofAdd true), kept as an integer-linear endomorphism. "
                + "The action in the formula is (-1)^a.val times U^b.val applied to T^n(v), "
                + "for p=(n,a,b):Int times Fin 2 times Fin 2. Every commuting A is obtained from "
                + "scalarUnit and the complete unit_normal_form; evaluation at the original "
                + "cyclic generator reflects uniqueness through the injective unit action. "
                + "rho_time uses literal membership of h in the original fullAutSubgroup and "
                + "rho_unitShift, so the second clause covers EVERY original h without an "
                + "extra Sign-equivariance, inertness, positivity or marker premise.",
                DescribeRole.Theorem),
            Paragraph(Text("This is a repository synthesis; the integral reconstruction and coupled-unit "
                + "classification supply the missing live content. The prior centralizer/scalar "
                + "argument and native chart are reused at their owners. No literature novelty is "
                + "claimed. The theorem bounds the actual rho image. The uniform residue application "
                + "asserts no lifting of every Common(q) unit to a native automorphism or to rho, no "
                + "ambient surjectivity and no kernel splitting. ResetPerronBeamTrace.original_action_positive "
                + "and rho_negative_bit give original-beam positivity and exclusion of a negative scalar bit "
                + "for any supplied signed time/Sign expression when q>=2. Exact q=2 image exhaustion "
                + "and lift elaboration are outside this uniform residue application.")))));

}
