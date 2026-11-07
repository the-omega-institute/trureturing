using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Analysis;

internal sealed class SeparateMassEvolutionStabilityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Strong L1 convergence on each fixed vector, under separate integrable scalar controls of uniformly bounded mass, gives uniform strong convergence of the original measurable nonautonomous Banach evolution on the full closed ordered time triangle.",
        H("Separate scalar masses and strong stability of the original evolution"), Blocks(
            Paragraph(Text("Let E be a complex normed space in any universe, with its normed additive commutative group and complex normed-space structures. The evolution assertions assume CompleteSpace E. The zero space in every universe is included. Let S be the original NonautonomousDysonPhillips.Contraction E: bounded complex-linear contractions on nonnegative real times, with identity at zero, the semigroup law and continuous vector orbits. Write A(t)=S.action(t)=S.operator(Real.toNNReal(t)). Evolution integrals are the original vector Bochner integrals for real Lebesgue measure volume. Scalar norm integrals are real integrals with their displayed measures.")),
            Paragraph(Text("For T>=0, set J=Icc(0,T), mu=volume restricted to J and Delta(T)={(t,r):0<=r<=t<=T}. B_n(s) and B(s) are bounded complex-linear endomorphisms of E for each real absolute time s. Every fixed-vector slice is AE strongly measurable for mu, separately for each n and x. Every n has its own arbitrary nonnegative real integrable control g_n on J, and B has another such control g. Require norm(B_n(s))<=g_n(s) and norm(B(s))<=g(s) at every s in J. A single real C>=0 bounds the integral of every g_n and the integral of g over J. These integral bounds do not require a common pointwise integrable envelope or uniform integrability of the controls. No hypothesis concerns their values outside J.")),
            new DocumentBlock.DisplayFormula(Recurrence()),
            Paragraph(Text("Write V_m(B;t,r)x for the displayed NonautonomousDysonPhillips.term; its sum is exactly NonautonomousDysonPhillips.sum. The order A(t-s) after B(s) is retained. The coefficient-indexed measurableEvolution(S,B,t,r) is the existing bounded linear realization of that sum, defined before any horizon or scalar control. Its original measurableEvolution_apply identity supplies the identification on every eligible ordered interval.")),
            Describe.Lean(DescribeId.Create("compact-range-strong-l1-evaluation"), Handle("uniform_integral_evaluation_of_mass"),
                H("Uniform evaluation on compact vector ranges"),
                StatementSource.FromAuthor(CompactEvaluation()), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("This assertion needs no completeness. Alpha is any measurable space in any universe, mu is any measure, D_n(s) is a bounded complex-linear endomorphism of E and each c_n is a real mu-integrable function. Require c_n>=0 almost everywhere and norm(D_n(s))<=c_n(s) almost everywhere, separately for each n, a real M bounding every integral of c_n, and AE strong measurability of every fixed-vector slice. If the integral of norm(D_n(s)x) tends to zero for each fixed x, then the conclusion holds for every compact K in E, including the empty compact set. Every AE strongly measurable path v with v(s) in K almost everywhere has actually integrable D_n(s)v(s). For each epsilon>0 a single eventual index bounds its norm integral by epsilon for all these paths at once.")),
                    Paragraph(Text("Compactness gives a finite cover of K by balls of radius delta. For each vector in K choose one center only in the pointwise estimate. Bound norm(D_n(s)v(s)) by the sum of norm(D_n(s)y) over all cover centers y, plus c_n(s)*delta. Each fixed-center integral tends to zero, while the integrated remainder is at most delta*M, uniformly in n. Choose delta before n, using the uniform mass bound. No pointwise majorant common to n is used. The pointwise choice needs no measurability assumption, since the finite sum supplies a measurable integrable bound. Actual vector integrability follows from the existing AE strongly measurable evaluation theorem and boundedness of the compact range. This argument neither interchanges a supremum with an integral nor requires a common exceptional set for uncountably many vectors."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("uniform-original-dyson-term-convergence"), Handle("uniform_term_convergence_of_mass"),
                H("Uniform convergence of each original Dyson term"),
                StatementSource.FromAuthor(EvolutionStatement(false)), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("Under the stated horizon, measurability, separate controls, uniform mass bounds and fixed-vector L1 hypotheses, every fixed natural m and every fixed x satisfy convergence of V_m(B_n;t,r)x to V_m(B;t,r)x uniformly over all (t,r) in Delta(T). The eventual index can depend on m,x and epsilon, and it is independent of both endpoints.")),
                    Paragraph(Text("For the induction step, the limiting term path is s maps to V_m(B;max(s,r),r)x. The argument pair (max(s,r),r) stays in Delta(T) whenever s,r belong to J. Original joint continuity makes the image of the compact square J times J a compact subset of E. Apply compact-range L1 evaluation with D_n=B_n-B and c_n=g_n+g, whose integrals are at most 2*C. This gives uniform convergence of the integral of the coefficient difference evaluated on all these paths. For r<=s the clamped path is precisely V_m(B;s,r)x.")),
                    Paragraph(Text("Subtract the original two Bochner recurrences. Inside the integrand use B_n(s)(V_m(B_n;s,r)x-V_m(B;s,r)x)+(B_n(s)-B(s))V_m(B;s,r)x. Contractivity bounds the first contribution by g_n(s) times the uniform previous-term error, and compact-range evaluation controls the second. Both contributions have actual integrability; the original term_integrable theorem justifies subtraction of the original integrals. Extend only the scalar upper estimate from Icc(r,t) to J using nonnegativity. The integral of the first contribution is at most C times the previous-term tolerance. Choosing that tolerance after C closes the induction, including C=0, without dividing by a control mass."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("uniform-strong-measurable-evolution-stability"), Handle("measurable_evolution_stability_of_mass"),
                H("Uniform strong convergence on the entire ordered triangle"),
                StatementSource.FromAuthor(EvolutionStatement(true)), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("For every vector x and epsilon>0 there exists one natural N such that for every n>=N and every pair of real times 0<=r<=t<=T, the norm of measurableEvolution(S,B_n,t,r)x-measurableEvolution(S,B,t,r)x is less than epsilon. The conclusion concerns the same coefficient-indexed measurableEvolution and includes a moving initial time r, the diagonal and both boundary edges.")),
                    Paragraph(Text("The original factorial bound gives norm(V_m(Q;t,r)x)<=G^m/m!*norm(x), where G is the integral of the separate control of Q from 0 to T. Thus norm(V_m(Q;t,r)x)<=C^m/m!*norm(x), simultaneously for B, every B_n and all (t,r) in Delta(T). Mathlib's uniform summation theorem supplies one common tail bound for B and every B_n. Uniform convergence of the finitely many original terms controls the finite sums. The three-distance estimate, with two common tails and one finite-sum error, proves uniform convergence of the original sums. The original realization identity then gives exactly the named evolution conclusion.")),
                    Paragraph(Text("The hypotheses quantify over every admissible sequence g_n, every admissible g and every mass bound C>=0, including zero controls and C=0. T=0, zero coefficients and x=0 are included. Neither the argument nor the conclusion requires norm(identity)=1 or a nonzero vector. There is no assumption of a common integrable envelope, uniform integrability of the controls, operator-norm L1 convergence, convergence at individual times, separability, finite dimension, operator-valued measurability, a common uncountable-vector exceptional set or regularity outside J. The result makes no assertion about operator-norm convergence of the evolution or uniformity over unbounded horizons or all unit vectors.")),
                    Paragraph(Text("Finite compact covers, Bochner integrability, uniform convergence of series and the exponential factorial series are Mathlib supplies. The original ordered recurrences and their measurable construction are reused from NonautonomousDysonPhillips and MeasurableNonautonomousDysonPhillips; NonautonomousEvolutionStability supplies single-control evaluated-path integrability. The finite-net mechanism is classical: compare Engel and Nagel, One-Parameter Semigroups for Linear Evolution Equations, DOI 10.1007/b97696, I.5.2. Their VI.9.19-20 treat nonautonomous perturbations under stronger continuity and lag-bound hypotheses; those statements are comparisons and are not an exact attribution of the separate-control sequence theorem here. No literature-priority assertion is made."))), DescribeRole.Theorem),
            new DocumentBlock.Section(H("Integrable forcing on the full ordered triangle"), Blocks(
            Paragraph(Text("Retain exactly the preceding Banach-space, contraction-semigroup and coefficient hypotheses, with E in any universe and CompleteSpace E. Thus T>=0, J=Icc(0,T), mu=volume restricted to J and Delta(T)={(t,r):0<=r<=t<=T}. Every fixed-vector slice of B_n and B is AE strongly measurable for mu. The separate real controls g_n and g are integrable and pointwise nonnegative on J, with norm(B_n(s))<=g_n(s) and norm(B(s))<=g(s) there. A single C>=0 bounds each integral of g_n and the integral of g over J. For every fixed y in E, the integral over J of norm((B_n(s)-B(s))y) tends to zero. The semigroup S and the absolute coefficient time s retain their original meanings.")),
            Paragraph(Text("Let f_n,f be arbitrary functions from real time to E whose restrictions to J are Bochner integrable, and assume that the integral over J of norm(f_n(s)-f(s)) tends to zero. Write V_n(t,r)=measurableEvolution(S,B_n,t,r) and V(t,r)=measurableEvolution(S,B,t,r), abbreviating the original bounded complex-linear operators. For x in E and (t,r) in Delta(T), define u_n(t,r;x)=V_n(t,r)x+integral_[r,t] V_n(t,s)f_n(s) and u(t,r;x)=V(t,r)x+integral_[r,t] V(t,s)f(s). These are vector Bochner integrals for volume restricted to Icc(r,t); since r<=t, they equal the original interval integrals from r to t. The same convention identifies the scalar integrals on J with the interval integrals from 0 to T.")),
            Paragraph(Text("For every n and every admissible 0<=r<=t<=T, the original integrands s maps to V_n(t,s)f_n(s) and s maps to V(t,s)f(s) are actually Bochner integrable on Icc(r,t). Under these hypotheses, for every fixed x in E and every epsilon>0 there exists one natural N such that norm(u_n(t,r;x)-u(t,r;x))<epsilon for every n>=N and every 0<=r<=t<=T. The index N is chosen before both endpoints. It may depend on the fixed coefficient and forcing sequences, their limits, S, T, the controls and mass bound, x and epsilon.")),
            Paragraph(Text("For the parameter correspondence, take Q=B_n with its own control g_n, or Q=B with control g, and keep the same S and horizon T. Write g_Q for that control and V_Q(t,r)=measurableEvolution(S,Q,t,r). Restrict each coefficient slice and control to an eligible subinterval when applying measurableEvolution_apply. It identifies V_Q(t,r)y with the original NonautonomousDysonPhillips.sum(S,Q,t,r,y). The original sum_bound estimate and nonnegativity of the corresponding control give norm(V_Q(t,r)y)<=exp(integral_[r,t] g_Q)*norm(y)<=exp(C)*norm(y). The original sum_joint_continuous statement, transported by this identity, gives continuity of (t,r) maps to V_Q(t,r)y on Delta(T) for each fixed y.")),
            Paragraph(Text("Fix an admissible t,r and a Bochner integrable path v on J. Restrict the preceding fixed-vector continuity to s maps to (t,s) on Icc(r,t). This supplies AE strong measurability of every fixed-vector evolution slice. Applying MeasurableNonautonomousDysonPhillips.aestronglyMeasurable_evaluation to those slices and v gives AE strong measurability of s maps to V_Q(t,s)v(s). Its norm is bounded by exp(C)*norm(v(s)), an integrable scalar function on that interval. Integrable.mono' therefore gives actual Bochner integrability. Taking (Q,v)=(B_n,f_n), (B_n,f) and (B,f) supplies the integrability needed for all subsequent integral subtractions.")),
            Paragraph(Text("For the fixed limiting forcing f, define F_(n,t,r)(s) to be V_n(t,s)f(s)-V(t,s)f(s) when s belongs to Icc(r,t), and zero otherwise. For every n and (t,r) in Delta(T), this E-valued function is AE strongly measurable for volume and its norm is bounded by b(s)=indicator_J(s)*2*exp(C)*norm(f(s)). The scalar function b is integrable on the whole real line. It follows from the two evolution bounds and the given integrability of f; it imposes no common pointwise envelope on the coefficient controls.")),
            Paragraph(Text("For each fixed s in J, apply measurable_evolution_stability_of_mass with the same S,T,B_n,B,g_n,g,C and with vector y=f(s). It gives one eventual index for the evolution difference at all endpoints (t,s) in Delta(T). Whenever s belongs to Icc(r,t) and (t,r) belongs to Delta(T), the pair (t,s) is admissible; otherwise F_(n,t,r)(s) is zero. Outside J it is also zero for every admissible endpoint pair. Thus F_(n,t,r)(s) tends to zero for each fixed real s along the filter l=atTop(Nat) times principal(Delta(T)). The index in this pointwise step may depend on s, which requires no common exceptional set for uncountably many vectors.")),
            Paragraph(Text("The filter atTop on Nat and every principal filter are countably generated, and so is their product l, even though Delta(T) is uncountable. Apply MeasureTheory.tendsto_integral_filter_of_dominated_convergence to F, the bound b and this filter, with real Lebesgue measure and limit zero in E. It yields convergence to zero of the vector integral of F along l. The product-principal uniform-convergence characterization tendsto_prod_principal_iff turns this into: for every eta>0, one eventual index makes norm(integral_[r,t] (V_n(t,s)f(s)-V(t,s)f(s)))<eta simultaneously for every (t,r) in Delta(T). Actual integrability identifies this vector integral with the difference of the two fixed-forcing integrals. This application uses the existing dominated-convergence result directly, without an additional finite-net or simple-function approximation.")),
            Paragraph(Text("Changing the forcing contributes at most exp(C)*integral_J norm(f_n(s)-f(s)): linearity of V_n(t,s), the same evolution bound and Icc(r,t) contained in J bound the norm of integral_[r,t] V_n(t,s)f_n(s)-integral_[r,t] V_n(t,s)f(s) by this scalar quantity, uniformly over Delta(T). It tends to zero by the forcing hypothesis. Decompose u_n-u into the homogeneous error (V_n(t,r)-V(t,r))x, this changed-forcing integral error and the fixed-forcing integral error. Apply the preceding homogeneous assertion to x and tolerance epsilon/3, and use tolerance epsilon/3 for each forcing error. A common eventual index and the triangle inequality give the asserted single N for the full ordered triangle.")),
            Paragraph(Text("The application includes zero Banach spaces in arbitrary universes, T=0, zero controls, C=0, x=0, zero forcing and diagonal intervals. It adds no common coefficient envelope, uniform integrability, separability, finite dimension, operator-valued measurability, common uncountable-vector exceptional set or hypothesis outside J. Its uniformity concerns the endpoints for fixed data and a fixed vector x; it makes no uniform assertion over all forcings, all unit vectors or unbounded horizons. It does not assert operator-norm convergence or convergence of the integral of the norm of the fixed-forcing evolution difference. The integrability and stability conclusions are consequences of the existing evolution and Bochner integration results; they make no assertion about physical realization, resource requirements or literature priority.")))))));

    private static DeclarationHandle Handle(string name) => DeclarationHandle.Create("D5/S3/Quantum/Analysis/SeparateMassEvolutionStability."+name);
    private static Formula R => Call("Real");
    private static Formula N => Call("Nat");
    private static Formula E => F.Id("E");
    private static Formula Z => new Formula.Number(0);
    private static Formula One => new Formula.Number(1);
    private static Formula X(string name) => F.Id(name);
    private static Formula All(string n, Formula d, Formula b) => new Formula.Bind(FormulaQuantifier.ForAll,FormulaIdentifier.Create(n),d,b);
    private static Formula Exists(string n, Formula d, Formula b) => new Formula.Bind(FormulaQuantifier.Exists,FormulaIdentifier.Create(n),d,b);
    private static Formula At(Formula f, params Formula[] xs) => new Formula.Apply(f,[.. xs]);
    private static Formula Lam(string n, Formula d, Formula b) => Seq(Grp(X(n),Colon,d),Mapsto,Sp,b);
    private static Formula Imp(Formula a,Formula b) => new Formula.Logic(a,FormulaLogicOperator.Implies,b);
    private static Formula And(Formula a,Formula b) => new Formula.Logic(a,FormulaLogicOperator.And,b);
    private static Formula Le(Formula a,Formula b) => new Formula.Relation(a,FormulaRelationOperator.LessThanOrEqual,b);
    private static Formula Lt(Formula a,Formula b) => new Formula.Relation(a,FormulaRelationOperator.LessThan,b);
    private static Formula Equal(Formula a,Formula b) => new Formula.Relation(a,FormulaRelationOperator.Equal,b);
    private static Formula Norm(Formula a) => new Formula.Norm(a);
    private static Formula Arrow(Formula a,Formula b) => new Formula.TypeArrow(a,b);
    private static Formula Clm => Call("ComplexCLM",E,E);
    private static Formula Coeff => Arrow(R,Clm);
    private static Formula J => Call("Icc",Z,X("T"));
    private static Formula Mu => Call("restrict",Call("volume"),J);
    private static Formula AE(Formula mu,Formula f) => Call("AlmostEverywhere",mu,f);
    private static Formula Int(Formula mu,Formula f) => Call("integral",mu,f);
    private static Formula Meas(Formula q) => All("x",E,Call("AEStronglyMeasurable",Lam("s",R,At(At(q,X("s")),X("x"))),Mu));
    private static Formula Dom(Formula q, Formula c) => All("s",R,Imp(Call("Mem",X("s"),J),Le(Norm(At(q,X("s"))),At(c,X("s")))));
    private static Formula Delta => And(Le(Z,X("r")),And(Le(X("r"),X("t")),Le(X("t"),X("T"))));
    private static Formula Scope(bool complete,Formula b) => All("u",Call("Universe"),All("E",Call("Type",X("u")),
        Seq(OpenBracket,Call("NormedAddCommGroup",E),CloseBracket,Sp,OpenBracket,Call("NormedSpace",Call("Complex"),E),CloseBracket,Sp,
            complete?Seq(OpenBracket,Call("CompleteSpace",E),CloseBracket,Sp,b):b)));
    private static Formula Diff(Formula y) => At(Subtract(At(X("Bseq"),X("n"),X("s")),At(X("B"),X("s"))),y);
    private static Formula L1 => All("x",E,Call("Tendsto",Lam("n",N,
        Call("intervalIntegral",Call("volume"),Z,X("T"),Lam("s",R,Norm(Diff(X("x")))))),Call("atTop"),Call("nhds",Z)));
    private static Formula Eventual(Formula body) => Call("Eventually",Call("atTop"),Lam("n",N,body));
    private static Formula Term(Formula q,Formula m,Formula t,Formula r) => Call("term",X("S"),q,m,t,r,X("x"));
    private static Formula Value(Formula q) => Call("measurableEvolution",X("S"),q,X("t"),X("r"),X("x"));

    private static Formula CompactEvaluation()
    {
        Formula a=X("alpha"), mu=X("mu"), d=X("D"), c=X("c"), v=X("v"), k=X("K");
        Formula slice=All("n",N,All("x",E,Call("AEStronglyMeasurable",Lam("s",a,At(d,X("n"),X("s"),X("x"))),mu)));
        Formula integrable=All("n",N,Call("Integrable",At(c,X("n")),mu));
        Formula nonneg=All("n",N,AE(mu,Lam("s",a,Le(Z,At(c,X("n"),X("s"))))));
        Formula bound=All("n",N,AE(mu,Lam("s",a,Le(Norm(At(d,X("n"),X("s"))),At(c,X("n"),X("s"))))));
        Formula mass=All("n",N,Le(Int(mu,Lam("s",a,At(c,X("n"),X("s")))),X("M")));
        Formula conv=All("x",E,Call("Tendsto",Lam("n",N,Int(mu,Lam("s",a,Norm(At(d,X("n"),X("s"),X("x")))))),Call("atTop"),Call("nhds",Z)));
        Formula path=And(Call("AEStronglyMeasurable",v,mu),AE(mu,Lam("s",a,Call("Mem",At(v,X("s")),k))));
        Formula eval=Lam("s",a,At(d,X("n"),X("s"),At(v,X("s"))));
        Formula actual=All("n",N,All("v",Arrow(a,E),Imp(path,Call("Integrable",eval,mu))));
        Formula uniform=All("epsilon",R,Imp(Lt(Z,X("epsilon")),Eventual(All("v",Arrow(a,E),Imp(path,Lt(Int(mu,Lam("s",a,Norm(At(d,X("n"),X("s"),At(v,X("s")))))),X("epsilon")))))));
        Formula result=All("K",Call("Set",E),Imp(Call("IsCompact",k),And(actual,uniform)));
        Formula premises=Imp(slice,Imp(integrable,Imp(nonneg,Imp(bound,All("M",R,Imp(mass,Imp(conv,result)))))));
        return Scope(false,All("a",Call("Universe"),All("alpha",Call("Type",X("a")),Seq(OpenBracket,Call("MeasurableSpace",a),CloseBracket,Sp,
            All("mu",Call("Measure",a),All("D",Arrow(N,Arrow(a,Clm)),All("c",Arrow(N,Arrow(a,R)),premises)))))));
    }

    private static Formula EvolutionStatement(bool evolution)
    {
        Formula error=evolution?Norm(Subtract(Value(At(X("Bseq"),X("n"))),Value(X("B")))):
            Norm(Subtract(Term(At(X("Bseq"),X("n")),X("m"),X("t"),X("r")),Term(X("B"),X("m"),X("t"),X("r"))));
        Formula times=All("r",R,All("t",R,Imp(Delta,Lt(error,X("epsilon")))));
        Formula convergence=evolution?Exists("N",N,All("n",N,Imp(Le(X("N"),X("n")),times))):Eventual(times);
        Formula result=All("x",E,All("epsilon",R,Imp(Lt(Z,X("epsilon")),convergence)));
        if(!evolution) result=All("m",N,result);
        Formula gn=At(X("gn"),X("n")), g=X("g");
        Formula scalarIntegral(Formula f) => Call("intervalIntegral",Call("volume"),Z,X("T"),Lam("s",R,At(f,X("s"))));
        Formula nonneg(Formula f) => All("s",R,Imp(Call("Mem",X("s"),J),Le(Z,At(f,X("s")))));
        Formula masses=Imp(All("n",N,Le(scalarIntegral(gn),X("C"))),Imp(Le(scalarIntegral(g),X("C")),Imp(L1,result)));
        if(evolution) masses=Imp(Le(Z,X("C")),masses);
        Formula controls=All("gn",Arrow(N,Arrow(R,R)),All("g",Arrow(R,R),
            Imp(All("n",N,Call("IntegrableOn",gn,J,Call("volume"))),Imp(Call("IntegrableOn",g,J,Call("volume")),
                Imp(All("n",N,nonneg(gn)),Imp(nonneg(g),
                    Imp(All("n",N,Dom(At(X("Bseq"),X("n")),gn)),Imp(Dom(X("B"),g),All("C",R,masses)))))))));
        Formula premises=Imp(All("n",N,Meas(At(X("Bseq"),X("n")))),Imp(Meas(X("B")),controls));
        return Scope(true,All("S",Call("Contraction",E),All("T",R,Imp(Le(Z,X("T")),
            All("Bseq",Arrow(N,Coeff),All("B",Coeff,premises))))));
    }

    private static Formula Recurrence()
    {
        Formula t=X("t"),r=X("r"),s=X("s"),q=X("B"),m=X("m");
        Formula baseTerm=Equal(Term(q,Z,t,r),Call("action",X("S"),Subtract(t,r),X("x")));
        Formula next=Equal(Term(q,Add(m,One),t,r),Call("intervalIntegral",Call("volume"),r,t,
            Lam("s",R,Call("action",X("S"),Subtract(t,s),At(At(q,s),Term(q,m,s,r))))));
        return Scope(true,All("S",Call("Contraction",E),All("B",Coeff,All("x",E,All("t",R,All("r",R,And(baseTerm,All("m",N,next))))))));
    }
}
