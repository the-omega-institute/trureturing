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
                + "cyclic chart. nativeGluing is Phi inverse followed by the existing integral gluing. "
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
            Paragraph(Text("Fix every natural q and every hq:0<q, including q=1. In this application "
                + "Nq=Native(q)=DimensionGroup(resetMatrix q) is the ORIGINAL additive dimension group, "
                + "e=nativeGluing(q,hq), and S=groupAction(resetMatrix q)(Multiplicative.ofAdd true) "
                + "is its actual integer-linear Sign endomorphism. Put Kplus=ker((S-id).toAddMonoidHom), "
                + "Kminus=ker((S+id).toAddMonoidHom), L_N=Kplus sup Kminus and Q_N=Nq/L_N. "
                + "For every v in Nq, v in Kplus iff S(v)=v, and v in Kminus iff S(v)=-v. "
                + "Use V(q,epsilon), kappa(q) and tau(q) solely as the local mathematical notation "
                + "defined in the application exposition at ResetIntegralGluing.")),
            Paragraph(Text("The native_gluing sign clause gives, for every v in Nq, "
                + "e(S(v))=gluing(q,fp(q,W(q)))*e(v). Thus "
                + "L_N.map(e.toAddMonoidHom)=V(q,1) sup V(q,-1). For every v in Nq, "
                + "v in L_N iff there exist a in Plus(q) and b in Minus(q) with "
                + "e(v).val=(2*a,2*b), iff for every t in D(q)=Plus(q) times Minus(q), "
                + "e(v).val*t belongs to (rplus q).pullback(rminus q). The halves are arbitrary "
                + "and may be incompatible. Reuse native_gluing, the (1,-1) identity from "
                + "ResetIntegralGluing.gluing_generators, the monic-representative/half derivation at "
                + "that owner, and Mathlib's AddSubgroup.map_sup and AddSubgroup.mem_map_iff_mem "
                + "for the injective equivalence e. This transports both actual eigenspaces and "
                + "the full-product conductor criterion, without assigning multiplication to Nq.")),
            Paragraph(Text("Put kappa_N=kappa(q).toAddMonoidHom composed with e.toAddMonoidHom and "
                + "g0=nativeIntEquiv(q,hq)(1). Then kappa_N is surjective, ker(kappa_N)=L_N, "
                + "and kappa_N(g0)=1. There exists E:Q_N ~=+ Common(q) such that for every v in Nq, "
                + "E([v])=kappa_N(v), and Nat.card(Q_N)=2^q. Here [v]=QuotientAddGroup.mk' L_N v. "
                + "Use the coefficient lifts from ResetIntegralGluing.common_surjective (private at its owner) "
                + "through gluing, the component-kernel and AddSubgroup.mem_sup derivation there, and "
                + "Mathlib's QuotientAddGroup.congr to transport the actual subgroup quotient. "
                + "Compose with QuotientAddGroup.quotientAddEquivOfEq and "
                + "QuotientAddGroup.quotientKerEquivOfSurjective as at the arithmetic owner. "
                + "AdjoinRoot.powerBasis', Basis.equivFun and Nat.card_congr then give the size, "
                + "including odd q, repeated factors and nonreduced Common(q).")),
            Paragraph(Text("For every v in Nq, kappa_N(resetTheta q v)=[X]*kappa_N(v), "
                + "where [X] is the value of tau(q). For every s in the ORIGINAL "
                + "Sign=Multiplicative Bool and every v in Nq, "
                + "kappa_N(groupAction(resetMatrix q)(s)(v))=kappa_N(v). Consequently for every s "
                + "there is hs:L_N <= L_N.comap((groupAction(resetMatrix q)(s)).toAddMonoidHom) "
                + "such that QuotientAddGroup.map L_N L_N ((groupAction(resetMatrix q)(s)).toAddMonoidHom) hs "
                + "=AddMonoidHom.id Q_N. The actual sign acts as (1,-1), whose common residue is one; "
                + "the other element is the identity by leftTranslation(1)=id and Module.DirectLimit.map_id. "
                + "Use native_gluing's time and sign clauses, ResetIntegralGluing.gluing_generators, "
                + "AdjoinRoot.mk_X and QuotientAddGroup.induction_on. The kernel equality proves hs, "
                + "and E's injectivity proves the displayed quotient identity on every class.")),
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
            Paragraph(Text("For every q>0, every integer-linear additive automorphism "
                + "A:Native(q) ~=_Int Native(q), and every proof ht of "
                + "forall v in Native(q), A(resetTheta q v)=resetTheta q (A(v)), put "
                + "cA=kappa_N(A(g0)). This covers every actual integer-linear time-centralizing AddAut "
                + "on the original group, with its canonical integer module structure. Then IsUnit(cA) "
                + "and, for every v in Native(q), kappa_N(A(v))=cA*kappa_N(v). "
                + "More explicitly, uA=Units.map ((kappa(q).comp (gluing q).toRingHom).toMonoidHom) "
                + "(scalarUnit q hq A ht) is a unit with value cA. Reuse "
                + "ResetHistoryKernel.centralizingMap_scalar for A and its inverse, and this owner's "
                + "scalarUnit, private scalarUnit_action and nativeAction_apply. These identify A with "
                + "multiplication by scalarUnit in the existing cyclic chart. Apply the ring homomorphism "
                + "kappa(q) composed with gluing, and evaluate at g0, whose residue is one.")),
            Paragraph(Text("Use composition as multiplication on AddAut(Q_N): "
                + "(d1*d2)(z)=d1(d2(z)), with identity and inverse the actual additive equivalences. "
                + "Define locally mu(u)(z)=E.inverse((u:Common(q))*E(z)) for every unit u of Common(q) "
                + "and every z in Q_N. It is a group homomorphism into AddAut(Q_N) and is injective: "
                + "evaluate E(mu(u)(E.inverse(1)))=u. For every A and ht as above, there exists "
                + "dA=mu(uA) in AddAut(Q_N) with dA([v])=[A(v)] for every v in Native(q), "
                + "and E(dA(z))=cA*E(z) for every z in Q_N. There exists "
                + "hA:L_N <= L_N.comap(A.toAddMonoidHom) such that "
                + "QuotientAddGroup.map L_N L_N A.toAddMonoidHom hA=dA.toAddMonoidHom. "
                + "Indeed kappa_N(A(v))=cA*kappa_N(v) proves subgroup stability; the same formula "
                + "and E([v])=kappa_N(v) prove descent on representatives. Apply "
                + "QuotientAddGroup.map and QuotientAddGroup.induction_on for the generic-map equality. "
                + "The inverse unit makes dA an actual additive automorphism, with no general-q unit classification.")),
            Paragraph(Text("For every q>0 the source group is the ORIGINAL "
                + "ResetFullAut(q)=fullAutSubgroup(ResetGraph q), consisting of homeomorphisms of "
                + "History(ResetGraph q) commuting with the actual shift. The representation "
                + "rho=ResetFullStandardBeamRepresentation.rho(q,hq) acts on Native(q). "
                + "There exists rhoBar:ResetFullAut(q) ->* AddAut(Q_N) with rhoBar(1)=id and "
                + "rhoBar(h*k)=rhoBar(h) composed with rhoBar(k) for every h,k. For every original "
                + "h in ResetFullAut(q), cH=kappa_N(rho(q,hq,h)(g0)) is a unit; for every v in Native(q), "
                + "kappa_N(rho(q,hq,h)(v))=cH*kappa_N(v) and rhoBar(h)([v])=[rho(q,hq,h)(v)]; "
                + "for every z in Q_N, E(rhoBar(h)(z))=cH*E(z). Set "
                + "rhoBar(h)=mu(uA) with A=rho(q,hq,h) and ht=ResetHistoryKernel.rho_time(q,hq,h). "
                + "The representative identity and rho's existing monoid-homomorphism laws give the "
                + "representation laws on every class via QuotientAddGroup.induction_on. "
                + "Thus every original full-rho value is covered, without assuming Sign-equivariance or inertness.")),
            Paragraph(Text("For every q>0, the literal original unitShift(ResetGraph q) satisfies "
                + "rhoBar(unitShift(ResetGraph q))([v])=[resetTheta q v] for every v in Native(q), "
                + "and E(rhoBar(unitShift(ResetGraph q))(z))=(tau(q):Common(q))*E(z) for every z in Q_N. "
                + "In fact rhoBar(unitShift(ResetGraph q))=mu(tau(q)) and "
                + "orderOf(rhoBar(unitShift(ResetGraph q)))=orderOf(tau(q)). "
                + "If q=1 this order is 1; for every q with 2<=q this order is q+1. "
                + "ResetFullStandardBeamRepresentation.rho_unitShift identifies the action on representatives "
                + "with literal resetTheta. The residue time formula at g0 identifies its scalar with tau(q). "
                + "Apply Mathlib's orderOf_injective to the faithful mu, then use geom_sum_mul, "
                + "AdjoinRoot.mk_eq_zero, the monic degree comparison and X-coefficient exclusion "
                + "derived at ResetIntegralGluing's application location. These are exact reuse "
                + "derivations on the original groups, with no assumed conjugacy, semisimplicity, "
                + "squarefreeness, surrogate histories or surrogate actions.")),
            Paragraph(Text("Put R=rhoBar(unitShift(ResetGraph q)). rho_unitShift and native_gluing "
                + "give R([v])=[resetTheta(q)(v)] and E(R(z))=[X]*E(z), with the literal positive "
                + "forward [X] of Common(q). Induction gives E(R^[n](z))=[X]^n*E(z) for every "
                + "natural n. Restrict E to the two fixed subtypes; its inverse restricts because "
                + "E is injective and the iterate equation is proved. Both restricted inverse identities "
                + "are the inverse identities of E; no fixedness or count is assumed. Applying Nat.card_congr and "
                + "the companion/coset/parity derivation at ResetIntegralGluing gives |{z in Q : R^[n](z)=z}| = "
                + "2^(gcd(q+1,n)-1 + (if Even((q+1)/gcd(q+1,n)) then 1 else 0)). "
                + "At q=1 this is 2 for every n, and at n=0 it is 2^q. All q>0 and all n "
                + "are retained. Arbitrary full rho values retain their proved scalar descent, "
                + "but are not substituted for R in this periodic formula. There is no assumed "
                + "conjugacy, inertness, positivity, field property or entropy premise.")),
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
            Paragraph(Text("For every q>=2, hp:0<q and original h:ResetFullAut(q) of finite "
                + "order, set A=rho(q,hp,h) and u=scalarUnit(q,hp,A,rho_time(q,hp,h)). "
                + "The equality nativeAction(u)=A and faithfulness of nativeAction transfer "
                + "h^n=1, n>0, to u^n=1. For R=E composed with plus(q), the exact trace "
                + "identity and tau_one=1 give R(u)=tau(rho(h)(Phi(1)))>0 by "
                + "original_action_positive, which applies to every original h. "
                + "Its positive finite-order real value is one. Injectivity of E gives "
                + "plus(q,u)=1, and applying rplus(q) gives Common residue one. "
                + "No finite-order generation, image-exhaustion or inertness assumption is used.")),
            Paragraph(Text("At q=4 take the original group G=ResetFullAut(4), forward time "
                + "t=unitShift(ResetGraph 4), and e=evenAut(4,hp,Even4). With "
                + "res=rplus(4) composed with plus(4), set s(h)=scalarUnit(4,hp,rho(h),rho_time(h)) "
                + "and psi(h)=Units.map(res)(s(h)). Faithfulness of nativeAction and rho.map_mul "
                + "give the homomorphism laws. Evaluation at Phi(1) identifies "
                + "s(h)=Phi.inverse(rho(h)(Phi(1))). Let a=psi(t), Ht=Subgroup.zpowers(a), "
                + "and chi=QuotientGroup.mk'(Ht) composed with psi. The target units are "
                + "commutative, so this cyclic subgroup is normal. The existing whole-action "
                + "rho_unitShift and rho_even give a.val=x and psi(e).val=1+x, "
                + "where x=[X] in Common(4). The original F=id+Theta realizer is exactly e.")),
            Paragraph(Text("This q4 separation needs only the monic polynomial "
                + "P=reduce(g(4))=X^4+X^3+X^2+X+1 of degree four. "
                + "The identity X^5-1=(X-1)P gives a^5=1. Over F2, "
                + "(1+X)^5-1=XP+(X^3+X^2). The remainder has nonzero X^2 coefficient "
                + "and degree three, so its quotient class is nonzero; hence psi(e)^5!=1. "
                + "The fifth-power homomorphism kills Ht, separating psi(e) from Ht and "
                + "giving chi(e)!=1. Quotient membership kills actual forward time, and "
                + "the uniform finite-order result gives psi(h)=1 and chi(h)=1 for every "
                + "finite-order original h. For S={t} union {h in G | IsOfFinOrder(h)}, "
                + "normalClosure(S) lies in ker(chi) and misses e, so is proper. "
                + "The ordinary closure(S) is proper by inclusion in normalClosure(S). "
                + "No equality of these closures, target cardinality, surjectivity, "
                + "full rho-image classification or finite-history factorization follows.")),
            Paragraph(Text("ResetIntegralGluing supplies the integral reconstruction, and "
                + "ResetIntegralUnits.unit_normal_form supplies the q=2 coupled-unit classification. "
                + "The centralizer/scalar argument and native chart are reused at their owners; "
                + "the uniform residue formulas above apply these existing results. No literature novelty "
                + "is claimed. native_normal_forms bounds the actual rho image. The uniform residue application "
                + "asserts no lifting of every Common(q) unit to a native automorphism or to rho, no "
                + "ambient surjectivity and no kernel splitting. ResetPerronBeamTrace.original_action_positive "
                + "and rho_negative_bit give original-beam positivity and exclusion of a negative scalar bit "
                + "for any supplied signed time/Sign expression when q>=2. Exact q=2 image exhaustion "
                + "and lift elaboration are outside this uniform residue application.")))));

}
