using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Analysis;

internal sealed class NonautonomousDysonPhillipsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Continuous time-dependent bounded perturbations of a strongly continuous complex Banach contraction semigroup admit an ordered Bochner series and a unique continuous mild evolution on every finite closed time triangle.",
        H("Nonautonomous Dyson–Phillips evolution"), Blocks(
            Paragraph(Text("Let E be a complex Banach space in any universe, including the zero space. Contraction consists of bounded complex-linear maps S.operator(q) for nonnegative real q, identity at zero, the additive semigroup law, operator norm at most one, and continuous vector orbits. Its auxiliary real-time action A(t)=S.operator(Real.toNNReal(t)) agrees with the given S at every nonnegative time and equals the identity at nonpositive times. Strong continuity suffices; no operator-norm continuity of S is assumed.")),
            Paragraph(Text("Fix T>=0 and B from the reals to bounded complex-linear endomorphisms, continuous in operator norm on Icc(0,T). Every M>=0 bounding norm(B(s)) there is admissible. B has no regularity or bound outside that interval. The closed triangle has coordinates (t,r) with 0<=r<=t<=T. All integrals below are E-valued Bochner interval integrals with real Lebesgue measure volume. The absolute coefficient time s and the left order A(t-s) after B(s) are retained without a commutation assumption.")),
            new DocumentBlock.DisplayFormula(Definitions()),
            Describe.Lean(
                DescribeId.Create("causal-iterate-bound"),
                DeclarationHandle.Create("D5/S3/Quantum/Analysis/NonautonomousDysonPhillips.causal_iterate_bound"),
                H("Factorial control of actual causal iterates"),
                StatementSource.FromAuthor(IterateStatement()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The estimate allows arbitrary real r<=T, B continuous on Icc(r,T), M>=0 bounding B there, and any continuous vector trajectory v there with norm(v(s))<=C. The constant C is real; its bound at the included endpoint r already implies C>=0. For every natural n and t in Icc(r,T), the actual recursively integrated G(n,t) has norm at most C*(M*(t-r))^n/n!, equivalently C*M^n*(t-r)^n/n! with the ordinary convention for the zeroth power.")),
                    Paragraph(Text("Continuity and integrability propagate through the causal integral. Interval projections extend B and v only for this local continuity argument and agree with the original functions throughout the integration interval. Induction dominates each actual integrand and integrates the preceding polynomial bound. No division by M or a vector norm occurs."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("nonautonomous-bounded-perturbation"),
                DeclarationHandle.Create("D5/S3/Quantum/Analysis/NonautonomousDysonPhillips.nonautonomous_bounded_perturbation"),
                H("Ordered series, joint continuity and unrestricted mild uniqueness"),
                StatementSource.FromAuthor(EvolutionStatement()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The function evolution(S,B,t,r), denoted U(t,r), is one bounded complex-linear map for each pair of times, defined independently of a horizon or chosen majorant. On every admissible triangle, the very D(n,t,r,x) terms in the displayed recurrence satisfy the factorial estimate and HasSum to U(t,r)x for every x. Vectorwise sums are linear and exponentially bounded, which assembles the single complex-linear map.")),
                    Paragraph(Text("For each fixed x, U(t,r)x is jointly continuous on the entire closed triangle, including its diagonal and T=0. Extend B by its interval projection, prove joint continuity of the parameterized integrals with both endpoints varying, and use equality of the actual terms on the triangle. A uniform exponential-series majorant passes joint continuity to the sum. Dominated summation inside the actual Bochner integral proves the mild equation.")),
                    Paragraph(Text("For every r in Icc(0,T), initial x and vector function X continuous on Icc(r,T), the mild identity alone implies X(t)=U(t,r)x there. No supplied bound, linearity, Lipschitz condition, derivative or family law on X is assumed. Its difference from the series is continuous on a compact interval and therefore has an internal finite norm bound. It equals all its own causal iterates. Applying the same factorial estimate to that residual and taking the factorial limit proves uniqueness. Splitting at an intermediate time and applying trajectory uniqueness proves the full three-time cocycle.")),
                    Paragraph(Text("Positive-order terms vanish on the diagonal and U(r,r) is the identity, including on the zero space. M=0, x=0 and T=0 are included. Zero B gives U(t,r)=A(t-r). The argument does not use norm(identity)=1. The output has an exponential operator-norm bound for every admissible M; no contractivity of U is asserted.")),
                    Paragraph(Text("Changing B outside Icc(r,t) leaves U(t,r) unchanged, even if the changed function is irregular there. This proves compatibility on overlapping finite horizons or coefficient extensions: their values agree wherever the connecting interval lies in the overlap and their coefficients agree there. For B(s)=Z on the horizon, the theorem identifies U(t,r)x with the original autonomous dysonSum(A,Z,t-r,x), using the same S and Z. Translation of each Bochner recurrence proves the term correspondence before summation. This identity holds for every finite horizon and every admissible M.")),
                    Paragraph(Text("The native contraction-semigroup action and the autonomous DysonPhillipsPerturbation construction supply the reused interfaces and series method. The latter retains Zayn Blore's Apache-2.0 source at revision ca3edfd7a5576d6c4e188501f9abb7c3f38ccd7f, CsdLean4/Mathlib/Analysis/Semigroup/BoundedPerturbation.lean, with its license in docs/reports/qmutualinfo/csd-lean4-LICENSE.txt. Mathlib supplies the scalar factorial integral, exponential series and Bochner convergence results. This is a nonautonomous extension of the classical bounded-perturbation construction. No originality claim or exact correspondence of the complete telescope with a single primary-source theorem is asserted.")),
                    Paragraph(Text("No bounded generator, domain, positivity, adjoint or physical interpretation enters the hypotheses or conclusions."))),
                DescribeRole.Theorem))));

    private static Formula Real => Call("Real");
    private static Formula Nat => Call("Nat");
    private static Formula E => F.Id("E");
    private static Formula S => F.Id("S");
    private static Formula B => F.Id("B");
    private static Formula T => F.Id("T");
    private static Formula M => F.Id("M");
    private static Formula R => F.Id("r");
    private static Formula Time => F.Id("t");
    private static Formula X => F.Id("x");
    private static Formula Zero => new Formula.Number(0);
    private static Formula One => new Formula.Number(1);
    private static Formula Clm => Call("ComplexCLM", E, E);
    private static Formula Family => new Formula.TypeArrow(Real, Clm);
    private static Formula Curve => new Formula.TypeArrow(Real, E);
    private static Formula Interval(Formula a, Formula b) => Call("Icc",a,b);
    private static Formula All(string n, Formula d, Formula b) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(n), d, b);
    private static Formula At(Formula f, params Formula[] xs) => new Formula.Apply(f,[.. xs]);
    private static Formula Lam(string n, Formula d, Formula b) => Seq(Grp(F.Id(n),Colon,d),Mapsto,Sp,b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a,FormulaRelationOperator.LessThanOrEqual,b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a,FormulaLogicOperator.Implies,b);
    private static Formula Conj(params Formula[] fs)
    {
        Formula r=fs[^1];
        for(int i=fs.Length-2;i>=0;--i) r=new Formula.Logic(fs[i],FormulaLogicOperator.And,r);
        return r;
    }
    private static Formula Scope(bool complete, Formula body)
    {
        Formula scoped=All("S",Call("Contraction",E),All("B",Family,body));
        if(complete) scoped=Seq(OpenBracket,Call("CompleteSpace",E),CloseBracket,Sp,scoped);
        return All("u",Call("Universe"),All("E",Call("Type",F.Id("u")),Seq(
            OpenBracket,Call("NormedAddCommGroup",E),CloseBracket,Sp,
            OpenBracket,Call("NormedSpace",Call("Complex"),E),CloseBracket,Sp,scoped)));
    }
    private static Formula InInterval(string name, Formula a, Formula b, Formula body) =>
        All(name,Real,Imp(Call("Mem",F.Id(name),Interval(a,b)),body));
    private static Formula Action(Formula t, Formula x) => At(Call("action",S,t),x);
    private static Formula Term(Formula n, Formula t, Formula r, Formula x) => Call("term",S,B,n,t,r,x);
    private static Formula U(Formula t, Formula r) => Call("evolution",S,B,t,r);
    private static Formula Value(Formula t, Formula r, Formula x) => At(U(t,r),x);
    private static Formula Triangle(Formula t, Formula r) => Conj(Le(Zero,r),Le(r,t),Le(t,T));
    private static Formula OnTriangle(Formula body) => All("t",Real,All("r",Real,Imp(Triangle(Time,R),body)));
    private static Formula Bound(Formula a, Formula b) => InInterval("s",a,b,
        Le(new Formula.Norm(At(B,F.Id("s"))),M));
    private static Formula Integral(Formula t, Formula r, Formula values) => Call("intervalIntegral",Call("volume"),r,t,
        Lam("s",Real,Action(Subtract(t,F.Id("s")),At(At(B,F.Id("s")),values))));
    private static Formula Majorant(Formula n, Formula t, Formula r, Formula x) => Multiply(
        new Formula.Fraction(Multiply(new Formula.Power(M,n),new Formula.Power(Subtract(t,r),n)),Call("factorial",n)),
        new Formula.Norm(x));
    private static Formula Definitions()
    {
        Formula n=F.Id("n"),s=F.Id("s"),v=F.Id("v");
        Formula body=Conj(
            Equal(Call("causal",S,B,R,v,Time),Integral(Time,R,At(v,s))),
            Equal(Call("causalIterate",S,B,R,v,Zero,Time),At(v,Time)),
            Equal(Call("causalIterate",S,B,R,v,Add(n,One),Time),
                Call("causal",S,B,R,Lam("s",Real,Call("causalIterate",S,B,R,v,n,s)),Time)),
            Equal(Term(Zero,Time,R,X),Action(Subtract(Time,R),X)),
            Equal(Term(Add(n,One),Time,R,X),Integral(Time,R,Term(n,s,R,X))),
            Equal(Call("sum",S,B,Time,R,X),Call("tsum",Lam("n",Nat,Term(n,Time,R,X)))));
        return Scope(true,All("r",Real,All("t",Real,All("n",Nat,All("x",E,All("v",Curve,body))))));
    }
    private static Formula IterateStatement()
    {
        Formula c=F.Id("C"),v=F.Id("v"),n=F.Id("n");
        Formula premises=Conj(Le(R,T),Call("ContinuousOn",B,Interval(R,T)),Le(Zero,M),Bound(R,T),
            Call("ContinuousOn",v,Interval(R,T)),InInterval("s",R,T,Le(new Formula.Norm(At(v,F.Id("s"))),c)));
        Formula conclusion=All("n",Nat,InInterval("t",R,T,
            Le(new Formula.Norm(Call("causalIterate",S,B,R,v,n,Time)),Multiply(c,
                new Formula.Fraction(new Formula.Power(Multiply(M,Subtract(Time,R)),n),Call("factorial",n))))));
        return Scope(false,All("r",Real,All("T",Real,All("M",Real,All("C",Real,All("v",Curve,
            Imp(premises,conclusion)))))));
    }
    private static Formula EvolutionStatement()
    {
        Formula n=F.Id("n"),s=F.Id("s"),other=F.Id("Q"),bz=F.Id("Z");
        Formula estimate=All("n",Nat,OnTriangle(All("x",E,
            Le(new Formula.Norm(Term(n,Time,R,X)),Majorant(n,Time,R,X)))));
        Formula series=OnTriangle(All("x",E,Call("HasSum",Lam("n",Nat,Term(n,Time,R,X)),Value(Time,R,X))));
        Formula joint=All("x",E,Call("ContinuousOn",Lam("p",Call("Prod",Real,Real),
            Value(Call("fst",F.Id("p")),Call("snd",F.Id("p")),X)),Call("triangle",T)));
        Formula mild=OnTriangle(All("x",E,Equal(Value(Time,R,X),
            Add(Action(Subtract(Time,R),X),Integral(Time,R,Value(s,R,X))))));
        Formula diagonal=InInterval("r",Zero,T,Equal(U(R,R),Call("id",Call("Complex"),E)));
        Formula competitor=Conj(Call("ContinuousOn",F.Id("X"),Interval(R,T)),
            InInterval("t",R,T,Equal(At(F.Id("X"),Time),
                Add(Action(Subtract(Time,R),X),Integral(Time,R,At(F.Id("X"),s))))));
        Formula unique=InInterval("r",Zero,T,All("X",Curve,All("x",E,Imp(competitor,
            InInterval("t",R,T,Equal(At(F.Id("X"),Time),Value(Time,R,X)))))));
        Formula cocycle=All("r",Real,All("s",Real,All("t",Real,Imp(
            Conj(Le(Zero,R),Le(R,s),Le(s,Time),Le(Time,T)),Equal(Call("comp",U(Time,s),U(s,R)),U(Time,R))))));
        Formula growth=OnTriangle(Le(new Formula.Norm(U(Time,R)),Call("exp",Multiply(M,Subtract(Time,R)))));
        Formula positiveDiagonal=All("n",Nat,All("r",Real,All("x",E,Equal(Term(Add(n,One),R,R,X),Zero))));
        Formula locality=All("Q",Family,OnTriangle(Imp(Call("EqOn",B,other,Interval(R,Time)),
            Equal(U(Time,R),Call("evolution",S,other,Time,R)))));
        Formula constant=All("Z",Clm,Imp(Call("EqOn",B,Lam("s",Real,bz),Interval(Zero,T)),
            OnTriangle(All("x",E,Equal(Value(Time,R,X),
                Call("dysonSum",Call("action",S),bz,Subtract(Time,R),X))))));
        Formula zero=Imp(Call("EqOn",B,Lam("s",Real,Zero),Interval(Zero,T)),
            OnTriangle(Equal(U(Time,R),Call("action",S,Subtract(Time,R)))));
        return Scope(true,All("T",Real,All("M",Real,Imp(
            Conj(Le(Zero,T),Call("ContinuousOn",B,Interval(Zero,T)),Le(Zero,M),Bound(Zero,T)),
            Conj(estimate,series,joint,mild,diagonal,unique,cocycle,growth,positiveDiagonal,locality,constant,zero)))));
    }
}
