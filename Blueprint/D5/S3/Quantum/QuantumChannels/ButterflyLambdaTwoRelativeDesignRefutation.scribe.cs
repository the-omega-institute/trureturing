using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.QuantumChannels;

internal sealed class ButterflyLambdaTwoRelativeDesignRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/QuantumChannels/ButterflyLambdaTwoRelativeDesignRefutation.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/QuantumStates/kerenidis2026scalablequantumml");
    private const string CircuitQuote = "An n-qubit unitary butterfly circuit of depth K = log₂ n consists of K layers. Layer ℓ ∈ {1,…,K} applies a full-width layer of n single-qubit phase gates followed by RBS gates on each of the n/2 disjoint pairs with stride 2^(ℓ−1):";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A minor of every single-pass stride-doubling unitary butterfly vanishes. Its fourth-power Haar average is positive, so the lower relative completely positive bound forces error at least one in every dimension 2^K with K at least two.",
        H("The single-pass butterfly fails the relative exterior-square two-design bound"),
        Blocks(
            Node("Mode", "Binary modes", All("K", Nat(), Eqn(Mode(K), Fn(Fin(K), Fin(D(2))))),
                "Bit l has stride 2^l. Mathlib's finFunctionFinEquiv identifies these modes with Fin(2^K), with bit zero the least significant bit."),
            Node("Rest", "A layer's pair labels", All("K", Nat(), All("l", Fin(K), Eqn(Rest(K,L),
                Fn(Call("Subtype", Lam("i", Fin(K), Ne(F.Id("i"),L))), Fin(D(2)))))),
                "A pair is specified by every bit other than l; its two modes differ in bit l."),
            Node("AngleIndex", "Independent parameter labels", All("K", Nat(), Eqn(Call("AngleIndex",K),
                Call("Sum", Call("Sigma", Lam("l",Fin(K),Rest(K,L))), Prod(Fin(K),Mode(K))))),
                "Sum is the disjoint sum of types and Sigma is the dependent sum. The left summand labels one RBS angle for each layer and pair; the right summand labels one phase for each layer and mode."),
            Node("Parameters", "Real parameter assignments", All("K",Nat(),Eqn(Params(K),Fn(Call("AngleIndex",K),Real()))),
                "All layer/pair and layer/mode coordinates are independent real angles."),
            Node("rbs", "Disjoint RBS blocks", LayerBind(And(Eqn(Call("rbs",K,P,L),
                Call("submatrix",Call("blockDiagonal",Lam("q",Rest(K,L),
                    Plane(At(P,Call("inl",new Formula.Apply(Seq(Operatorname,Grp(F.Id("Sigma"),Dot,F.Id("mk"))),[L,F.Id("q")])))))),
                    Call("piSplitAt",L,Call("const",Fin(K),Fin(D(2)))),
                    Call("piSplitAt",L,Call("const",Fin(K),Fin(D(2)))))),PlaneEntries())),
                "piSplitAt splits a binary mode into its bit l and its remaining-bit function. const denotes the constant family with value Fin(2). The same equivalence reindexes both matrix coordinates of the block diagonal. Sigma.mk constructs the dependent layer/pair label. The blocks are the underlying matrices of Matrix.planeConformalMatrix(cos(theta), -sin(theta)); its nonzero premise follows from cos²(theta)+sin²(theta)=1. The four displayed entries use ofReal casts."),
            Node("phase", "The full-width Rz phase layer", LayerBind(Eqn(Call("phase",K,P,L),PhaseDiagonal())),
                "PDF p. 10: “The R_z gate acts as R_z(φ)|0⟩ = e^(iφ/2)|0⟩, R_z(φ)|1⟩ = e^(−iφ/2)|1⟩: a diagonal one-body unitary, hence passive FLO and particle-number preserving.” Circle.exp(a) is exp(i a) on the unit circle and val is its complex subtype value. Prod.mk constructs the layer/mode label. The sum/2 term retains the common vacuum phase of the literal full Rz layer."),
            Node("layer", "One butterfly layer", LayerBind(Eqn(Call("layer",K,P,L),
                Mul(Call("rbs",K,P,L),Call("phase",K,P,L)))),
                "Phase gates act first and the disjoint RBS gates act second, exactly in the source's order."),
            Node("circuit", "The single-pass butterfly", All("K",Nat(),All("p",Params(K),Eqn(Call("circuit",K,P),
                new Formula.Apply(Seq(Operatorname,Grp(F.Id("List"),Dot,F.Id("prod"))),[Call("map",Lam("l",Fin(K),Call("layer",K,P,L)),Call("reverse",Call("finRange",K)))])))),
                "Section IV, PDF p. 10: “" + CircuitQuote + "” The source displays U(θ,φ) = U^(K)⋯U^(1) and U^(ℓ) = [tensor_j RBS(θ_ℓ^(j))] · tensor_i R_z(φ_ℓ^(i)). Lean indices l=0,…,K−1 correspond to ℓ=l+1, so List.prod multiplies the reversed increasing index list."),
            Node("parameterMeasure", "Uniform product measure", All("K",Nat(),Eqn(Call("parameterMeasure",K),
                new Formula.Apply(Seq(Operatorname,Grp(F.Id("MeasureTheory"),Dot,F.Id("Measure"),Dot,F.Id("pi"))),[Call("const",Call("AngleIndex",K),
                    Call("cond",Call("volume"),Call("Ico",D(0),Mul(D(2),Call("pi")))))]))),
                "cond is normalized restriction of real Lebesgue measure. MeasureTheory.Measure.pi takes the independent product over all coordinates. The interval is [0,2π); the endpoints have zero measure. This is the uniform parameter-torus expectation in the source."),
            Node("Wedge", "The ordered exterior basis", All("K",Nat(),Eqn(Wedge(K),Call("Subtype",
                Lam("p",Prod(Mode(K),Mode(K)),Lt(Call("finFunctionFinEquiv",Call("fst",P)),
                    Call("finFunctionFinEquiv",Call("snd",P))))))),
                "The basis is e_i wedge e_j for i<j in binary mode order."),
            Node("exteriorSquare", "The second exterior representation", ExteriorFormula(),
                "Expanding (W e_i) wedge (W e_j) gives coefficient W_ai W_bj − W_aj W_bi in e_a wedge e_b. These coefficients define the induced second exterior representation, rather than a restriction of two independent single-particle copies. fst and snd select the two modes of an ordered pair."),
            Node("TwoCopy", "Two exterior copies", All("K",Nat(),Eqn(Two(K),Prod(Wedge(K),Wedge(K)))),
                "This indexes the tensor product of two copies of the second exterior space."),
            Node("secondAction", "The Kronecker-square action", All("K",Nat(),All("W",M(Mode(K)),
                Eqn(Call("secondAction",K,W),Call("kronecker",Call("exteriorSquare",K,W),Call("exteriorSquare",K,W))))),
                "kronecker is Mathlib's matrix Kronecker product. Its row and column indices are ordered pairs of exterior-basis elements."),
            Node("twirl", "Second-moment matrix action", TwirlFormula(),
                "Each entry is a complex Bochner integral. The index set is finite; for the butterfly and Haar actions the integrands are continuous and integrable, so this agrees with the full finite-dimensional matrix Bochner integral. adjoint is conjugate transpose."),
            Node("butterflyMoment", "The butterfly second moment", All("K",Nat(),Eqn(Call("butterflyMoment",K),
                Call("twirl",K,Call("parameterMeasure",K),Call("circuit",K)))),
                "This is Φ₂^(Λ²,Wₙ) with n=2^K and independent uniform circuit parameters."),
            Node("Unitary", "The compact unitary group", All("K",Nat(),Eqn(Unitary(K),Call("unitary",Call("CStarMatrix",Mode(K),Mode(K),Complex())))),
                "CStarMatrix is Mathlib's operator-norm type copy of complex matrices. Its unitary group has the same elements and multiplication as Matrix.unitaryGroup on these modes. The measurable space is its Borel space."),
            Node("haarProbability", "Normalized Haar probability", All("K",Nat(),Eqn(Call("haarProbability",K),
                Call("haarMeasure",Seq(Open,Seq(Operatorname,Grp(F.Id("Top"),Dot,F.Id("top"))),Sp,Colon,Sp,Call("PositiveCompacts",Unitary(K)),Close)))),
                "The unitary group is compact: it is a closed subset of the radius-one ball in a finite-dimensional proper normed space. Top.top at type PositiveCompacts (Unitary K) is the whole compact group, so Mathlib's Haar normalization assigns it mass one."),
            Node("haarMoment", "The Haar second moment", All("K",Nat(),Eqn(Call("haarMoment",K),
                Call("twirl",K,Call("haarProbability",K),Lam("U",Unitary(K),new Formula.Apply(Seq(Operatorname,Grp(F.Id("CStarMatrix"),Dot,F.Id("ofMatrix"),Dot,F.Id("symm"))),[Call("val",F.Id("U"))]))))),
                "CStarMatrix.ofMatrix.symm returns the raw matrix of a unitary-group element; val is its subtype value."),
            Node("CPLe", "Completely positive order", CPFormula(),
                "F ⪯ G means that G−F is the raw action of a canonical completely positive map H. Mathlib's bundled type contains complex linearity and positivity under every finite matrix amplification, acting entrywise on the matrix of blocks. This is the completely positive order on the Kronecker-square action; it is stronger than testing only positive inputs without amplification."),
            Node("claim", "Conjecture 20: the relative design bound", ClaimFormula(),
                "The displayed claim encodes the relative bound that this conjecture asserts. A real c and natural threshold N precede every K with N≤2^K, followed by a nonnegative ε≤c/(2^K). Both lower and upper inequalities use CPLe. The fixed-point-space sentence is quoted as part of the source; refuting the relative bound refutes its full conjecture without asserting a separate fixed-point dimension result.",
                sourceQuote: ConjectureQuotation()),
            Node("result", "Refutation in arbitrary dimension", new Formula.Not(F.Id("claim")),
                "For every K≥2 and every parameter assignment the minor W₀₀W₂₁−W₀₁W₂₀ vanishes. The first layer has stride-one support; the later product preserves bit zero, so the selected columns are proportional on rows zero and two. For Haar unitaries, the continuous fourth power of the minor is nonnegative and equals one at the permutation exchanging modes one and two; Haar positivity on nonempty open sets makes its integral positive. Apply the lower CP bound to the rank-one projector at x=(e₀ wedge e₁) tensor (e₀ wedge e₁) and read the diagonal at u=(e₀ wedge e₂) tensor (e₀ wedge e₂). Its butterfly value is zero, while its Haar value is positive, forcing ε≥1. Powers 2^K exceed any fixed c and threshold, contradicting ε≤c/(2^K). The additive one-copy design statement and the independent-halves ensemble are outside this conclusion.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                resolution: new OpenProblemResolutionClaim(ProblemSlugRef.Create("kerenidis-2026-butterfly-lambda-two-relative-design-refutation"), ResolutionKind.Refuted))),
        []));

    private static DocumentBlock Node(string declaration, string title, Formula formula, string prose,
        DescribeRole role = DescribeRole.Definition, AssessedProvenance? provenance = null,
        DocumentBlock? sourceQuote = null, OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
            DescribeId.Create("butterfly-" + declaration.ToLowerInvariant()), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(Disp(formula)), provenance ?? AssessedProvenance.FromLiterature(Source),
            sourceQuote is null ? Blocks(Paragraph(Text(prose))) : Blocks(sourceQuote, Paragraph(Text(prose))), role, resolution);

    private static Formula Parenthesized(Formula x) => Seq(Open, x, Close);
    private static Formula Call(string name, params Formula[] xs) => new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. xs]);
    private static Formula At(Formula x, params Formula[] xs) => new Formula.Apply(x, [.. xs]);
    private static Formula All(string v, Formula type, Formula body) => Seq(Forall,Sp,F.Id(v),Sp,Colon,Sp,type,Comma,Sp,body);
    private static Formula Ex(string v, Formula type, Formula body) => Seq(Exists,Sp,F.Id(v),Sp,Colon,Sp,type,Comma,Sp,body);
    private static Formula Lam(string v, Formula type, Formula body) => Parenthesized(Seq(LambdaLower,Sp,F.Id(v),Sp,Colon,Sp,type,Comma,Sp,body));
    private static Formula Eqn(Formula x, Formula y) => new Formula.Relation(x,FormulaRelationOperator.Equal,y);
    private static Formula Lt(Formula x, Formula y) => new Formula.Relation(x,FormulaRelationOperator.LessThan,y);
    private static Formula Le(Formula x, Formula y) => new Formula.Relation(x,FormulaRelationOperator.LessThanOrEqual,y);
    private static Formula Ne(Formula x, Formula y) => new Formula.Relation(x,FormulaRelationOperator.NotEqual,y);
    private static Formula And(Formula x, Formula y) => new Formula.Logic(Parenthesized(x),FormulaLogicOperator.And,Parenthesized(y));
    private static Formula Imp(Formula x, Formula y) => new Formula.Logic(Parenthesized(x),FormulaLogicOperator.Implies,Parenthesized(y));
    private static Formula IffOf(Formula x, Formula y) => new Formula.Logic(x,FormulaLogicOperator.Iff,Parenthesized(y));
    private static Formula Sub(Formula x, Formula y) => new Formula.Binary(x,FormulaBinaryOperator.Subtract,y);
    private static Formula Mul(Formula x, Formula y) => new Formula.Binary(Parenthesized(x),FormulaBinaryOperator.Multiply,Parenthesized(y));
    private static Formula Pow(Formula x, Formula y) => new Formula.Power(x,y);
    private static Formula Fn(Formula x, Formula y) => Seq(Parenthesized(x),Sp,To,Sp,Parenthesized(y));
    private static Formula Prod(Formula x, Formula y) => Call("Prod",x,y);
    private static Formula Nat() => Seq(Mathbb,Grp(F.Id("N")));
    private static Formula Real() => Seq(Mathbb,Grp(F.Id("R")));
    private static Formula Complex() => Seq(Mathbb,Grp(F.Id("C")));
    private static Formula Fin(Formula x) => Call("Fin",x);
    private static Formula C(Formula x) => Call("ofReal",x);
    private static Formula M(Formula x) => Call("Matrix",x,x,Complex());
    private static Formula Mode(Formula k) => Call("Mode",k);
    private static Formula Rest(Formula k, Formula l) => Call("Rest",k,l);
    private static Formula Params(Formula k) => Call("Parameters",k);
    private static Formula Wedge(Formula k) => Call("Wedge",k);
    private static Formula Two(Formula k) => Call("TwoCopy",k);
    private static Formula Unitary(Formula k) => Call("Unitary",k);
    private static Formula Adj(Formula x) => Call("adjoint",x);
    private static Formula SumOver(string v, Formula type, Formula body) => Seq(Sum,Underscore,Grp(F.Id(v),Sp,Colon,Sp,type),Sp,Parenthesized(body));
    private static Formula K => F.Id("K");
    private static Formula L => F.Id("l");
    private static Formula P => F.Id("p");
    private static Formula W => F.Id("W");
    private static Formula Y => F.Id("Y");
    private static Formula LayerBind(Formula body) => All("K",Nat(),All("p",Params(K),All("l",Fin(K),body)));
    private static Formula Entry(Formula x, Formula row, Formula col) => At(x,row,col);

    private static Formula PhaseDiagonal()
    {
        Formula i=F.Id("i"),j=F.Id("j");
        Formula pi=At(P,Call("inr",new Formula.Apply(Seq(Operatorname,Grp(F.Id("Prod"),Dot,F.Id("mk"))),[L,i])));
        Formula pj=At(P,Call("inr",new Formula.Apply(Seq(Operatorname,Grp(F.Id("Prod"),Dot,F.Id("mk"))),[L,j])));
        Formula a=Sub(new Formula.Fraction(SumOver("i",Mode(K),pi),D(2)),pj);
        Formula exponential=new Formula.Apply(Seq(Operatorname,Grp(F.Id("Circle"),Dot,F.Id("exp"))),[a]);
        return Call("diagonal",Lam("j",Mode(K),Call("val",exponential)));
    }

    private static Formula Plane(Formula theta) => Call("val",new Formula.Apply(
        Seq(Operatorname,Grp(F.Id("Matrix"),Dot,F.Id("planeConformalMatrix"))),
        [C(Call("cos",theta)),new Formula.Negate(C(Call("sin",theta)))]));
    private static Formula PlaneEntries()
    {
        Formula theta=F.Id("theta"),m=Plane(theta),c=C(Call("cos",theta)),s=C(Call("sin",theta));
        return All("theta",Real(),And(Eqn(Entry(m,D(0),D(0)),c),And(Eqn(Entry(m,D(0),D(1)),s),
            And(Eqn(Entry(m,D(1),D(0)),new Formula.Negate(s)),Eqn(Entry(m,D(1),D(1)),c)))));
    }

    private static Formula ExteriorFormula()
    {
        Formula i=F.Id("i"),j=F.Id("j");
        Formula a=Call("fst",Call("val",i)),b=Call("snd",Call("val",i));
        Formula c=Call("fst",Call("val",j)),d=Call("snd",Call("val",j));
        return All("K",Nat(),All("W",M(Mode(K)),All("i",Wedge(K),All("j",Wedge(K),
            Eqn(Entry(Call("exteriorSquare",K,W),i,j),Sub(Mul(Entry(W,a,c),Entry(W,b,d)),Mul(Entry(W,a,d),Entry(W,b,c))))))));
    }
    private static Formula TwirlFormula()
    {
        Formula x=F.Id("X"),mu=F.Id("mu"),i=F.Id("i"),j=F.Id("j");
        Formula a=Call("secondAction",K,At(W,P));
        Formula rhs=Call("integral",mu,Lam("p",x,Entry(Mul(Mul(a,Y),Adj(a)),i,j)));
        Formula body=All("mu",Call("Measure",x),All("W",Fn(x,M(Mode(K))),All("Y",M(Two(K)),
            All("i",Two(K),All("j",Two(K),Eqn(Entry(Call("twirl",K,x,mu,W,Y),i,j),rhs))))));
        return All("K",Nat(),All("X",Call("Type"),Seq(OpenBracket,Call("MeasurableSpace",x),CloseBracket,Sp,body)));
    }
    private static Formula CPFormula()
    {
        Formula i=F.Id("iota"),f=F.Id("F"),g=F.Id("G"),h=F.Id("H");
        Formula cs=Call("CStarMatrix",i,i,Complex()),map=Fn(M(i),M(i));
        Formula equality=Eqn(new Formula.Apply(Seq(Operatorname,Grp(F.Id("CStarMatrix"),Dot,F.Id("ofMatrix"),Dot,F.Id("symm"))),[At(h,Call("ofMatrix",Y))]),Sub(At(g,Y),At(f,Y)));
        Formula body=All("F",map,All("G",map,IffOf(Call("CPLe",i,f,g),
            Ex("H",Call("CompletelyPositiveMap",cs,cs),All("Y",M(i),equality)))));
        return All("iota",Call("Type"),Seq(OpenBracket,Call("Fintype",i),CloseBracket,Sp,
            OpenBracket,Call("DecidableEq",i),CloseBracket,Sp,body));
    }
    private static Formula ClaimFormula()
    {
        Formula c=F.Id("c"),n=F.Id("N"),e=F.Id("epsilon"),size=Pow(D(2),K);
        Formula lower=Call("CPLe",Two(K),Lam("Y",M(Two(K)),Call("smul",Sub(D(1),e),Call("haarMoment",K,Y))),Call("butterflyMoment",K));
        Formula upper=Call("CPLe",Two(K),Call("butterflyMoment",K),Lam("Y",M(Two(K)),
            Call("smul",new Formula.Binary(D(1),FormulaBinaryOperator.Add,e),Call("haarMoment",K,Y))));
        Formula bound=And(Le(D(0),e),And(Le(e,new Formula.Fraction(c,Seq(Open,new Formula.Apply(Seq(Operatorname,Grp(F.Id("Nat"),Dot,F.Id("cast"))),[size]),Sp,Colon,Sp,Real(),Close))),And(lower,upper)));
        return IffOf(F.Id("claim"),Ex("c",Real(),Ex("N",Nat(),All("K",Nat(),Imp(Le(n,size),Ex("epsilon",Real(),bound))))));
    }

    private static DocumentBlock ConjectureQuotation() => Paragraph(Text(
        "Conjecture 20, PDF p. 16, equations (38)–(39): “The unitary butterfly W<sub>n</sub> at uniformly random parameters is an ε-approximate unitary 2-design on U(n) in the antisymmetric 2-particle representation Λ² ℂ<sup>n</sup>, in the *relative* (multiplicative) sense, with ε = O(1/n): writing Φ₂<sup>Λ²,W<sub>n</sub></sup>[Y] := E<sub>W<sub>n</sub></sub>[Λ²(W<sub>n</sub>)<sup>⊗ 2</sup> Y Λ²(W<sub>n</sub>)<sup>†⊗ 2</sup>], for Y ∈ End(Λ²ℂ<sup>n</sup> ⊗ Λ²ℂ<sup>n</sup>), and Φ₂<sup>Λ²,Haar</sup> for the corresponding Haar second moment, (1−ε) Φ₂<sup>Λ²,Haar</sup> ⪯ Φ₂<sup>Λ²,W<sub>n</sub></sup> ⪯ (1+ε) Φ₂<sup>Λ²,Haar</sup> as completely positive maps. In particular Φ₂<sup>Λ²,W<sub>n</sub></sup> has fixed-point space of dimension 3, matching the Haar decomposition Λ² ⊗ Λ² = V<sub>(2,2)</sub> ⊕ V<sub>(2,1,1)</sub> ⊕ V<sub>(1,1,1,1)</sub> into three irreducible U(n)-representations.”"));
}
