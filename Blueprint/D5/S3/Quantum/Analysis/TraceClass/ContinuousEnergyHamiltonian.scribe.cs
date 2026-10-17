using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Analysis.TraceClass;

internal sealed class ContinuousEnergyHamiltonianDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Analysis/TraceClass/ContinuousEnergyHamiltonian.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Entropy/shirokov2012entropycontinuity");
    private static readonly Formula Hh=F.Id("H"), I=F.Id("iota"), B=F.Id("b"), H=F.Id("h"), A=F.Id("A"),
        S=F.Id("sigma"), R=F.Id("r"), C=F.Id("code"), W=F.Id("w"), J=F.Id("i"), N=F.Id("n"),
        P=F.Id("rho"), G=F.Id("gamma"), Delta=F.Id("delta"), X=F.Id("x"), Y=F.Id("y"), V=F.Id("v"),
        T=F.Id("t"), Beta=F.Id("beta");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Continuous singular reference energy constructs one full-space all-temperature Hamiltonian.",
        Hdr(), Blocks(
            Item("thermalBaseLevel", "Finite levels on the complete spectral basis", BaseFormula(),
                "H is a complete complex Hilbert space, sigma is a positive trace-class contraction, and r is an actual full SpectralResolution of sigma. For an arbitrary code from r.index to the natural numbers, thermalBaseLevel(r,code,i) is (code(i)+1)*log(2) when r.values(i)=0 and -log(r.values(i)) otherwise. Every level is a finite real number. No basis vectors are removed and no unused natural coordinate becomes a physical mode.", DescribeRole.Definition),
            Item("ThermalOn", "Joint conclusions for one literal operator", ThermalFormula(),
                "ThermalOn(b,h,A) abbreviates the following conjunction for the literal K=DiagonalHeat.hamiltonian(b,h) and the literal positive-time heat DiagonalHeat.heat(b,h,hh,t), with hh the proof that every h(i) is nonnegative. All real coefficients are at least one; for every real beta>0, exp(-beta*h(i)) is genuinely summable. K is self-adjoint and has dense domain in the entire H. Its graph is exactly the coefficient equation b.repr(y)(i)=h(i)*b.repr(x)(i), and its operator domain is exactly the weighted-l2 condition Memlp(i maps to h(i)*b.repr(x)(i),2). The heat coefficients are exp(-t*h(i))*b.repr(x)(i), and the actual bounded heat operator is positive for every nonnegative time.",
                "There is a strongly continuous contraction semigroup S equal to the real scalar restriction of this literal heat. For every x,v in H, its right difference quotient at zero tends to v if and only if (x,-v) belongs to K.graph. Any strongly continuous contraction semigroup with that same full generator graph equals S. For every x in the operator domain, norm(x)^2 is at most Re inner(x,K(x)). For every positive NNReal beta, the literal heat is trace class, and both its complex and real coefficient series have HasSum equal to its actual complex trace and real trace, respectively.",
                "The mixed-state energy is exactly DiagonalEnergy.stateEnergy(b,h,hh,rho.1,TraceClass.isTraceClass_coe(rho)), defined by the actual bounded resolvent-cap traces. It is finite on A, and both this ENNReal-valued function and its real value are ContinuousOn A in trace norm. Operator domain, quadratic-form domain and mixed-state energy remain distinct. No unbounded product K*rho is formed; no trace-class assertion at beta=0 is made.", DescribeRole.Definition),
            Item("exists_thermalHamiltonian_of_continuous_spectralEnergy", "Thermal construction from continuous singular energy", ConditionalFormula(),
                "H is complete and separable over the complex numbers. The actual positive trace-class contraction sigma additionally has actual real trace one; normalization is not a field of Reference. The supplied r is any complete full Set-index spectral resolution of sigma, including nativeResolution(sigma). A is a nonempty compact subset of the actual trace-class Banach space. Every rho in A is positive and has actual real trace one. The actual singular spectralEnergy(sigma,rho) is finite on A and its real value is continuous there. No convexity assumption is used. For every strictly positive NNReal delta, one injective code, one natural weight w, and one real h on the original index satisfy the displayed joint conclusion. The weight is at least one, monotone, and tends to infinity; h(i)=1+w(code(i))*thermalBaseLevel(r,code,i).",
                "Separability and orthonormality make the full index countable. Only scalar energy terms are extended by zero along its injection into the natural numbers. Finite singular energy implies that each rho kills every zero-eigenvalue vector of sigma; those diagonal masses therefore vanish. Thus the actual energy is the sum of ofReal(a(i)*diagonal(b,rho,i)), with a=thermalBaseLevel. Actual normalization gives HasSum of the reference eigenvalues equal to one. The estimate exp(-a(i))<=s(i)+(1/2)^(code(i)+1) yields a summable majorant, including the full kernel.",
                "First prove finiteness of the extended nonnegative energy series, then pass to its genuine real sum. The real finite prefixes are continuous and increase to the assumed finite continuous real spectral energy. Dini's theorem on compact A gives precisely uniform shifted ENNReal tails. UniformTailAmplification supplies both the weighted cost and uniform weighted tails. The original generic summable_of_uniform_ennreal_tails and continuous_of_uniform_ennreal_tails in OrliczCommonEnergy apply directly to the weighted real scalar family, giving its actual finiteness and continuity.",
                "For each beta>0, eventually beta*w(n)>=1. Injectivity makes the preimage of any finite initial code segment finite. On its complement exp(-beta*h(i))<=exp(-a(i)); the remaining finite contribution proves summability. This requires no cofinal image, eigenvalue ordering, infinite index, faithful reference or finite ambient dimension. DiagonalHeat.diagonal_heat supplies the full graph, domain, heat, generator iff and uniqueness; DiagonalEnergy supplies the actual state-energy identity and lower form bound. AmplifiedDiagonalSeries(r,code,w,rho) denotes exactly the sum over the original i of ofReal((w(code(i)):Real)*thermalBaseLevel(r,code,i)*diagonal(r.basis,rho,i)). The constant one in the state energy comes from the actual trace-one diagonal HasSum. That same energy equals one plus this genuine amplified diagonal series and is at most 1+spectralEnergy(sigma,rho)+delta, with the corresponding finite real inequality."),
            Item("exists_thermalHamiltonian_of_continuous_entropy", "Full-space energy bound from the original entropy premises", EntropyFormula(),
                "H is complete and separable over the complex numbers. A is nonempty, trace-norm closed and real convex; its operators are positive and have actual real trace one. Every actual spectral entropy is finite and actual realEntropy is ContinuousOn A. Compactness, bounded entropy, maximizing centers, a common reference, uniform tails, thermal coefficients and a Hamiltonian are not premises.",
                "exists_unique_entropy_maximizer first supplies gamma0 in A. Bundle gamma0 as a positive contraction g0. Finiteness identifies spectralEntropy(g0) with ofReal(realEntropy(gamma0)), and the real value is nonnegative. Apply spectralEnergy_le_entropy_of_isMaxOn to get an energy bound on every rho in A. Hence A lies in the entire energySublevel(g0,realEntropy(gamma0)). isCompact_energySublevel and the original closedness make A compact. Apply fullCompactCommonReference to obtain gamma in A maximizing entropy and sigma in A with finite actual reference energy bounded by realEntropy(gamma)+log(2), with the corresponding finite real bound and both ENNReal and real continuity on A. All of these common-reference conclusions are retained in the endpoint.",
                "Membership gives sigma its separate trace-one premise. Apply the new conditional construction to the native full basis with delta=1. The result is one literal full-space K, heat, strong generator and mixed-state energy satisfying ThermalOn, together with the strictly positive finite real bound 2+realEntropy(gamma)+log(2). Every rho in A satisfies the ENNReal bound by ofReal of this number and the same real inequality. All original kernel directions remain finite physical Hamiltonian modes. This is the mathematical Conjecture 1 endpoint under the explicit separable-H premises. No genuine relative-entropy D definition, continuity conclusion or Conjecture 2 conclusion is asserted. The relation to the source conjecture is stated without a literature-priority or official-acceptance claim."))));
    private static Heading Hdr() => DefinitionDsl.H("Full-space thermal Hamiltonians");
    private static DocumentBlock Item(string name,string title,Formula formula,string text,DescribeRole role) =>
        Describe.Lean(DescribeId.Create("thermal-"+name.Replace('_','-').ToLowerInvariant()),
            DeclarationHandle.Create(Module+name), DefinitionDsl.H(title), StatementSource.FromAuthor(formula),
            AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text(text))),role);
    private static DocumentBlock Item(string name,string title,Formula formula,params string[] text) =>
        Describe.Lean(DescribeId.Create("thermal-"+name.Replace('_','-').ToLowerInvariant()),
            DeclarationHandle.Create(Module+name), DefinitionDsl.H(title), StatementSource.FromAuthor(formula),
            AssessedProvenance.FromRepo(Source), Blocks(System.Array.ConvertAll(text,p=>Paragraph(Text(p)))),DescribeRole.Theorem);
    private static DocumentBlock Item(string name,string title,Formula formula,string a,string b,string c,DescribeRole role) =>
        Describe.Lean(DescribeId.Create("thermal-"+name.Replace('_','-').ToLowerInvariant()),
            DeclarationHandle.Create(Module+name), DefinitionDsl.H(title), StatementSource.FromAuthor(formula),
            AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text(a)),Paragraph(Text(b)),Paragraph(Text(c))),role);
    private static Formula All(string n,Formula ty,Formula body) => new Formula.Bind(FormulaQuantifier.ForAll,FormulaIdentifier.Create(n),ty,body);
    private static Formula Ex(string n,Formula ty,Formula body) => new Formula.Bind(FormulaQuantifier.Exists,FormulaIdentifier.Create(n),ty,body);
    private static Formula And(params Formula[] xs) { var y=xs[^1]; for(var i=xs.Length-2;i>=0;i--) y=new Formula.Logic(xs[i],FormulaLogicOperator.And,y); return y; }
    private static Formula Imp(Formula a,Formula b) => new Formula.Logic(a,FormulaLogicOperator.Implies,b);
    private static Formula Iff(Formula a,Formula b) => new Formula.Logic(a,FormulaLogicOperator.Iff,b);
    private static Formula Le(Formula a,Formula b) => new Formula.Relation(a,FormulaRelationOperator.LessThanOrEqual,b);
    private static Formula Lt(Formula a,Formula b) => new Formula.Relation(a,FormulaRelationOperator.LessThan,b);
    private static Formula Fn(Formula x,Formula y) => Call("Function",x,y);
    private static Formula At(Formula f,Formula x) => Call("apply",f,x);
    private static Formula Add(Formula x,Formula y) => Call("add",x,y);
    private static Formula Mul(Formula x,Formula y) => Call("multiply",x,y);
    private static Formula Index() => Call("index",R);
    private static Formula Basis() => Call("basis",R);
    private static Formula Energy(Formula b) => Call("stateEnergy",b,H,P);
    private static Formula RefEnergy() => Call("spectralEnergy",S,P);
    private static Formula Level() => Call("thermalBaseLevel",R,C,J);
    private static Formula UniformBound() => Add(Add(D(2),Call("realEntropy",G)),Call("log",D(2)));
    private static Formula BaseFormula() => All("H",F.Id("CompleteComplexHilbertSpace"),
        All("sigma",Call("Reference",Hh),All("r",Call("SpectralResolution",S),
        All("code",Fn(Index(),F.Id("Nat")),All("i",Index(),Equal(Level(),
        Call("ifZero",Call("valuesAt",R,J),Mul(Add(At(C,J),D(1)),Call("log",D(2))),
            Call("negate",Call("log",Call("valuesAt",R,J))))))))));
    private static Formula ThermalFormula()
    {
        Formula k=Call("hamiltonian",B,H), heat=Call("heat",B,H), e=Energy(B);
        Formula graph=All("x",Hh,All("y",Hh,Iff(Call("MemGraph",X,Y,k),
            All("i",I,Equal(Call("coefficient",B,Y,J),Mul(At(H,J),Call("coefficient",B,X,J)))))));
        Formula domain=All("x",Hh,Iff(Call("MemDomain",X,k),Call("WeightedLtwo",B,H,X)));
        Formula generator=All("x",Hh,All("v",Hh,Iff(Call("RightDerivativeAtZero",heat,X,V),
            Call("MemGraph",X,Call("negate",V),k))));
        Formula semigroup=Ex("Q",Call("StronglyContinuousContractionSemigroup",Hh),And(
            Equal(F.Id("Q"),Call("RealRestriction",heat)),generator,
            All("U",Call("StronglyContinuousContractionSemigroup",Hh),
                Imp(Call("HasFullGeneratorGraph",F.Id("U"),k),Equal(F.Id("U"),F.Id("Q"))))));
        Formula body=And(All("i",I,Le(D(1),At(H,J))),
            All("beta",F.Id("Real"),Imp(Lt(D(0),Beta),Call("SummableBoltzmann",H,Beta))),
            Call("SelfAdjoint",k),Call("DenseDomain",k),graph,domain,
            All("t",F.Id("NNReal"),All("x",Hh,All("i",I,
                Equal(Call("coefficient",B,Call("applyHeat",heat,T,X),J),
                    Mul(Call("exp",Call("negate",Mul(T,At(H,J)))),Call("coefficient",B,X,J)))))),
            All("t",F.Id("NNReal"),Call("Positive",At(heat,T))),semigroup,
            All("x",Call("Domain",k),Le(Call("normSquared",X),Call("RealInner",X,At(k,X)))),
            All("beta",F.Id("NNReal"),Imp(Lt(D(0),Beta),And(Call("TraceClass",At(heat,Beta)),
                Call("ComplexCoefficientHasSumActualTrace",B,H,Beta),Call("RealCoefficientHasSumActualTrace",B,H,Beta)))),
            All("rho",Call("TraceClass",Hh),Imp(Call("Mem",P,A),Lt(e,F.Id("Infinity")))),
            Call("ContinuousStateEnergyOn",B,H,A),Call("ContinuousRealStateEnergyOn",B,H,A));
        return All("H",F.Id("CompleteComplexHilbertSpace"),All("iota",F.Id("Type"),
            All("b",Call("HilbertBasis",I,F.Id("Complex"),Hh),All("h",Fn(I,F.Id("Real")),
            Imp(Call("Nonnegative",H),All("A",Call("Set",Call("TraceClass",Hh)),
                Iff(Call("ThermalOn",B,H,A),body)))))));
    }
    private static Formula ConditionalFormula()
    {
        Formula e=Energy(Basis()), series=Call("AmplifiedDiagonalSeries",R,C,W,P);
        Formula cost=All("rho",Call("TraceClass",Hh),Imp(Call("Mem",P,A),And(
            Equal(e,Add(D(1),series)),Le(e,Add(Add(D(1),RefEnergy()),Delta)),
            Le(Call("toReal",e),Add(Add(D(1),Call("toReal",RefEnergy())),Delta)))));
        Formula answer=Ex("code",Fn(Index(),F.Id("Nat")),And(Call("Injective",C),
            Ex("w",Fn(F.Id("Nat"),F.Id("Nat")),And(All("n",F.Id("Nat"),Le(D(1),At(W,N))),
            Call("Monotone",W),Call("TendsToInfinity",W),Ex("h",Fn(Index(),F.Id("Real")),And(
                Call("Nonnegative",H),All("i",Index(),Equal(At(H,J),Add(D(1),Mul(At(W,At(C,J)),Level())))),
                Call("ThermalOn",Basis(),H,A),cost))))));
        Formula hypotheses=And(Call("TraceOne",S),Call("Nonempty",A),Call("IsCompact",A),
            Call("PositiveTraceOneFamily",A),All("rho",Call("TraceClass",Hh),
            Imp(Call("Mem",P,A),Lt(RefEnergy(),F.Id("Infinity")))),Call("ContinuousRealSpectralEnergyOn",S,A),Lt(D(0),Delta));
        return All("H",F.Id("CompleteSeparableComplexHilbertSpace"),All("sigma",Call("Reference",Hh),
            All("r",Call("SpectralResolution",S),All("A",Call("Set",Call("TraceClass",Hh)),
            All("delta",F.Id("NNReal"),Imp(hypotheses,answer))))));
    }
    private static Formula EntropyFormula()
    {
        Formula b=Call("nativeBasis",S), e=Energy(b);
        Formula answer=Ex("gamma",Call("TraceClass",Hh),And(Call("Mem",G,A),
            Call("IsMaxOn",F.Id("realEntropy"),A,G),Ex("sigma",Call("Reference",Hh),And(Call("Mem",Call("underlyingTraceClass",S),A),
            And(Call("CommonReferenceEnergyBounds",S,A,G),
            Call("ContinuousSpectralEnergyOn",S,A),Call("ContinuousRealSpectralEnergyOn",S,A),
            Ex("h",Fn(Call("nativeIndex",S),F.Id("Real")),And(Call("Nonnegative",H),
                Call("ThermalOn",b,H,A),Lt(D(0),UniformBound()),All("rho",Call("TraceClass",Hh),
                    Imp(Call("Mem",P,A),And(Le(e,Call("ofReal",UniformBound())),Le(Call("toReal",e),UniformBound())))))))))));
        Formula premises=And(Call("Nonempty",A),Call("IsClosed",A),Call("RealConvex",A),
            Call("PositiveTraceOneFamily",A),Call("FiniteSpectralEntropyOn",A),Call("ContinuousOn",F.Id("realEntropy"),A));
        return All("H",F.Id("CompleteSeparableComplexHilbertSpace"),All("A",Call("Set",Call("TraceClass",Hh)),Imp(premises,answer)));
    }
}
