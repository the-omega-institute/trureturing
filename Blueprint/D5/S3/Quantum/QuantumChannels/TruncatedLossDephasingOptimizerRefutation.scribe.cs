using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.QuantumChannels;

internal sealed class TruncatedLossDephasingOptimizerRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/QuantumChannels/TruncatedLossDephasingOptimizerRefutation.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/QuantumStates/memarzadeh2016minimum");
    private const string Quote = "In a truncated Hilbert space of dimension K+1, the minimal output entropy of the quantum channel (3) is achieved either by binomial states of Eq.(14) or by states |κ_α⟩ of Eq. (11), depending on the values of ε and t.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The loss-dephasing channel of Memarzadeh and Mancini has a qutrit input with strictly smaller output entropy than every binomial or kappa candidate at the same input energy. The channel is defined by the Kraus equations, including the infinite phase-Kraus series.",
        H("Binomial and kappa states do not exhaust truncated entropy minimizers"),
        Blocks(
            Node("amplitudeKraus", "Amplitude damping Kraus operator", AmplitudeFormula(),
                "Equation (4), pp. 1–2: indices range over Fin(K+1). val is the natural-number value of a finite index, choose is the natural binomial coefficient, toReal is the natural-to-real cast, ofReal is the real-to-complex cast, and NatSub is truncated natural subtraction. Integer powers of square roots express the half-integer powers in the source for f in [0,1]."),
            Node("phaseKraus", "Phase damping Kraus operator", PhaseFormula(),
                "Equation (5), p. 2: k is an arbitrary natural number; the phase-Kraus family remains infinite after space truncation. factorial is the natural factorial, cast to the reals before division."),
            Node("lossDephasingChannel", "The composed loss-dephasing channel", ChannelFormula(),
                "Equation (3), p. 1, with E_jk=A_j P_k: the amplitude index j is finite after truncation, and the k sum is the infinite series. adjoint is conjugate transpose. The phase factor is obtained by summing that series, rather than assuming a matrix of output entries."),
            Node("numberOperator", "Truncated number observable", NumberFormula(),
                "The truncated Fock number observable is diagonal with entries 0,...,K. toComplex is the natural-to-complex cast."),
            Node("vonNeumannEntropy", "Spectral entropy in nats", EntropyFormula(),
                "For a Hermitian matrix, use the existing finite Shannon entropy sum of its real eigenvalues, counted with multiplicity: shannonEntropy(p)=sum_i -p_i log(p_i), with the continuous zero convention. The displayed dependent conditional binds the Hermiticity proof h in its true branch. For a non-Hermitian raw matrix the extension is zero. All outputs used below are Hermitian and positive. Natural logarithms differ from the source's base-two entropy by a positive constant and give the same ordering."),
            Node("admissible", "Fixed-energy density inputs", AdmissibleFormula(),
                "Equation (9), p. 2: admissible inputs are positive semidefinite matrices of trace one with number expectation N. PosSemidef is Mathlib's matrix predicate, trace is the complex matrix trace, and Re takes its real part."),
            Node("binomialKet", "Binomial state amplitudes", BinomialFormula(),
                "Equation (14), p. 3: the binomial amplitudes are supported on 0,...,M. Natural subtraction M-val(i) is NatSub; the probability powers have natural exponents."),
            Node("kappaKet", "The kappa state family", KappaFormula(),
                "Equation (11), p. 2: for K>=1 the state has support at 0 and K and relative phase exp(i alpha K). The conditional order agrees with Lean, including its extension at K=0, which the claim excludes. ComplexI is the imaginary unit; real quotients use the real cast of K."),
            Node("candidate", "The two proposed optimizer families", CandidateFormula(),
                "The binomial candidates obey 1<=M<=K, 0<=mu<=1 and M mu=N. The other candidates are kappaKet(K,N,alpha) for any real alpha. Equality here is equality of ket functions; the conjecture tests their outer-product matrices."),
            Node("claim", "Conjecture 1", ClaimFormula(),
                "Conjecture 1, section IV, arXiv v1 PDF p. 4: \"" + Quote + "\" The encoding quantifies over K>=1, N in [0,K], epsilon in [0,1] and t>=0. A candidate attains the minimum if its output entropy is no greater than the output entropy of every fixed-energy density input."),
            Node("result", "Qutrit refutation", Disp(new Formula.Not(F.Id("claim"))),
                "Take K=2, N=3/2, epsilon=6/7, t=(7/2)log(2), and psi=(|1>+|2>)/sqrt(2). The only binomial candidate is M=2, mu=3/4. Every kappa phase is covered by diagonal unitary conjugation. The psi output has an eigenvalue above 1/2 and one below 1/8, whereas all eigenvalues of each candidate output lie strictly between 1/8 and 1/2. Trace-one strict majorization and strict concavity of -x log(x) give smaller entropy for psi. The defining Kraus equations give the kappa output's off-diagonal coefficient sqrt(3)/32768; the displayed section-III coefficient in the source differs from those equations. The result excludes these candidate families as minimizers; it does not assert global optimality of psi. The proof has proof_shape: bind-only and escape_witness: none; it applies the exponential-series, positive-definiteness and strict-concavity results to the displayed instance.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(ProblemSlugRef.Create("memarzadeh-mancini-2016-truncated-loss-dephasing-optimizer-refutation"), ResolutionKind.Refuted))),
        []));

    private static DocumentBlock Node(string declaration, string title, Formula formula, string prose,
        DescribeRole role = DescribeRole.Definition, AssessedProvenance? provenance = null,
        OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
            DescribeId.Create("qutritmoe-" + declaration.ToLowerInvariant()), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(formula), provenance ?? AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula Parenthesized(Formula x) => Seq(Open, x, Close);
    private static Formula Call(string name, params Formula[] xs) => new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. xs]);
    private static Formula At(Formula f, params Formula[] xs) => new Formula.Apply(f, [.. xs]);
    private static Formula All(string v, Formula type, Formula body) => Seq(Forall, Sp, F.Id(v), Sp, Colon, Sp, type, Comma, Sp, body);
    private static Formula Ex(string v, Formula type, Formula body) => Seq(Exists, Sp, F.Id(v), Sp, Colon, Sp, type, Comma, Sp, body);
    private static Formula Eqn(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.Equal, y);
    private static Formula LeqOf(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.LessThanOrEqual, y);
    private static Formula And(Formula x, Formula y) => new Formula.Logic(Parenthesized(x), FormulaLogicOperator.And, Parenthesized(y));
    private static Formula Or(Formula x, Formula y) => new Formula.Logic(Parenthesized(x), FormulaLogicOperator.Or, Parenthesized(y));
    private static Formula Imp(Formula x, Formula y) => new Formula.Logic(Parenthesized(x), FormulaLogicOperator.Implies, Parenthesized(y));
    private static Formula IffOf(Formula x, Formula y) => new Formula.Logic(x, FormulaLogicOperator.Iff, Parenthesized(y));
    private static Formula Add(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Add, y);
    private static Formula Sub(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Subtract, y);
    private static Formula Mul(Formula x, Formula y) => new Formula.Binary(Parenthesized(x), FormulaBinaryOperator.Multiply, Parenthesized(y));
    private static Formula Pow(Formula x, Formula y) => Seq(Parenthesized(x), Caret, Grp(y));
    private static Formula Div(Formula x, Formula y) => new Formula.Fraction(x, y);
    private static Formula Nat() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Real() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Complex() => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula Fin(Formula k) => Call("Fin", Add(k, D(1)));
    private static Formula Ket(Formula k) => Seq(Fin(k), Sp, To, Sp, Complex());
    private static Formula State(Formula k) => Call("Matrix", Fin(k), Fin(k), Complex());
    private static Formula Val(Formula i) => Call("val", i);
    private static Formula Cast(Formula x) => Call("toReal", x);
    private static Formula C(Formula x) => Call("ofReal", x);
    private static Formula Rt(Formula x) => Call("sqrt", x);
    private static Formula ExpOf(Formula x) => Call("exp", x);
    private static Formula Adj(Formula x) => Call("adjoint", x);
    private static Formula SumOver(string i, Formula domain, Formula body) => Seq(Sum, Underscore,
        Grp(F.Id(i), Sp, Colon, Sp, domain), Sp, Parenthesized(body));
    private static Formula Tsum(string i, Formula body) => Seq(Sum, Apos, Underscore,
        Grp(F.Id(i), Sp, Colon, Sp, Nat()), Sp, Parenthesized(body));
    private static Formula K => F.Id("K");
    private static Formula N => F.Id("N");
    private static Formula E => F.Id("epsilon");
    private static Formula T => F.Id("t");
    private static Formula R => F.Id("rho");
    private static Formula Phi => F.Id("phi");
    private static Formula Fof => Sub(D(1), ExpOf(Mul(Mul(new Formula.Negate(D(2)), Sub(D(1), E)), T)));
    private static Formula Channel(Formula rho) => Call("lossDephasingChannel", K, E, T, rho);
    private static Formula Entropy(Formula rho) => Call("vonNeumannEntropy", K, rho);

    private static Formula AmplitudeFormula()
    {
        Formula j=F.Id("j"), f=F.Id("f"), r=F.Id("r"), c=F.Id("c");
        Formula value=C(Mul(Mul(Rt(Cast(Call("choose", Val(c), Val(j)))),
            Pow(Rt(Sub(D(1), f)), Call("NatSub", Val(c), Val(j)))), Pow(Rt(f), Val(j))));
        Formula rhs=Call("ite", Eqn(Add(Val(r),Val(j)),Val(c)), Call("ite", LeqOf(Val(j),Val(c)),value,D(0)),D(0));
        return Disp(All("K",Nat(),All("j",Fin(K),All("f",Real(),All("r",Fin(K),All("c",Fin(K),
            Eqn(At(Call("amplitudeKraus",K,j,f),r,c),rhs)))))));
    }
    private static Formula PhaseFormula()
    {
        Formula k=F.Id("k"), eta=F.Id("eta"), r=F.Id("r"), c=F.Id("c");
        Formula square=Pow(Cast(Val(r)),D(2));
        Formula value=C(Mul(Rt(Div(Pow(Mul(Mul(D(2),square),eta),k),Cast(Call("factorial",k)))),
            ExpOf(new Formula.Negate(Mul(square,eta)))));
        return Disp(All("K",Nat(),All("k",Nat(),All("eta",Real(),All("r",Fin(K),All("c",Fin(K),
            Eqn(At(Call("phaseKraus",K,k,eta),r,c),Call("ite",Eqn(r,c),value,D(0)))))))));
    }
    private static Formula ChannelFormula()
    {
        Formula j=F.Id("j"), k=F.Id("k");
        Formula product=Mul(Call("amplitudeKraus",K,j,Fof),Call("phaseKraus",K,k,Mul(E,T)));
        Formula value=SumOver("j",Fin(K),Tsum("k",Mul(Mul(product,R),Adj(product))));
        return Disp(All("K",Nat(),All("epsilon",Real(),All("t",Real(),All("rho",State(K),Eqn(Channel(R),value))))));
    }
    private static Formula NumberFormula() => Disp(All("K",Nat(),Eqn(Call("numberOperator",K),
        Call("diagonal",Seq(LambdaLower,Sp,F.Id("i"),Sp,Colon,Sp,Fin(K),Comma,Sp,Call("toComplex",Val(F.Id("i"))))))));
    private static Formula EntropyFormula()
    {
        Formula h=F.Id("h");
        Formula branch=Seq(F.Id("if"),Sp,h,Sp,Colon,Sp,Call("IsHermitian",R),Sp,F.Id("then"),Sp,
            Call("shannonEntropy",Call("eigenvalues",R,h)),Sp,F.Id("else"),Sp,D(0));
        return Disp(All("K",Nat(),All("rho",State(K),Eqn(Entropy(R),branch))));
    }
    private static Formula AdmissibleFormula() => Disp(All("K",Nat(),All("N",Real(),All("rho",State(K),
        IffOf(Call("admissible",K,N,R),And(Call("PosSemidef",R),And(Eqn(Call("trace",R),D(1)),
            Eqn(Call("Re",Call("trace",Mul(R,Call("numberOperator",K)))),N))))))));
    private static Formula BinomialFormula()
    {
        Formula m=F.Id("M"), mu=F.Id("mu"), i=F.Id("i");
        Formula value=C(Rt(Mul(Mul(Cast(Call("choose",m,Val(i))),Pow(mu,Val(i))),
            Pow(Sub(D(1),mu),Call("NatSub",m,Val(i))))));
        return Disp(All("K",Nat(),All("M",Nat(),All("mu",Real(),All("i",Fin(K),
            Eqn(At(Call("binomialKet",K,m,mu),i),Call("ite",LeqOf(Val(i),m),value,D(0))))))));
    }
    private static Formula KappaFormula()
    {
        Formula alpha=F.Id("alpha"), i=F.Id("i"), ratio=Div(N,Cast(K));
        Formula top=Mul(C(Rt(ratio)),Call("ComplexExp",Mul(Call("ComplexI"),C(Mul(alpha,Cast(K))))));
        Formula value=Call("ite",Eqn(Val(i),D(0)),C(Rt(Sub(D(1),ratio))),Call("ite",Eqn(Val(i),K),top,D(0)));
        return Disp(All("K",Nat(),All("N",Real(),All("alpha",Real(),All("i",Fin(K),
            Eqn(At(Call("kappaKet",K,N,alpha),i),value))))));
    }
    private static Formula CandidateBody()
    {
        Formula m=F.Id("M"), mu=F.Id("mu"), alpha=F.Id("alpha");
        Formula binomial=Ex("M",Nat(),And(LeqOf(D(1),m),And(LeqOf(m,K),Ex("mu",Real(),
            And(LeqOf(D(0),mu),And(LeqOf(mu,D(1)),And(Eqn(Mul(Cast(m),mu),N),Eqn(Phi,Call("binomialKet",K,m,mu)))))))));
        return Or(binomial,Ex("alpha",Real(),Eqn(Phi,Call("kappaKet",K,N,alpha))));
    }
    private static Formula CandidateFormula() => Disp(All("K",Nat(),All("N",Real(),All("phi",Ket(K),
        IffOf(Call("candidate",K,N,Phi),CandidateBody())))));
    private static Formula ClaimFormula()
    {
        Formula minimum=All("rho",State(K),Imp(Call("admissible",K,N,R),
            LeqOf(Entropy(Channel(Call("rankOneDensity",Phi))),Entropy(Channel(R)))));
        Formula choice=Ex("phi",Ket(K),And(Call("candidate",K,N,Phi),minimum));
        Formula conditions=Imp(LeqOf(D(1),K),Imp(LeqOf(D(0),N),Imp(LeqOf(N,Cast(K)),
            Imp(LeqOf(D(0),E),Imp(LeqOf(E,D(1)),Imp(LeqOf(D(0),T),choice))))));
        return Disp(IffOf(F.Id("claim"),All("K",Nat(),All("N",Real(),All("epsilon",Real(),All("t",Real(),conditions))))));
    }
}
