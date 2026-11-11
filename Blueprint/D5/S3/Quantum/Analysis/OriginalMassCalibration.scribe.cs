using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Analysis;

internal sealed class OriginalMassCalibrationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()=>DocumentDefinition.Create(ScribeNode.Create("Strictly positive factorization of the actual masses precedes original scale calibration.",H("The two original masses and the same readout twice"),Blocks(
        Paragraph(Text("All mathematical definitions below use precisely source (79.2): K(a)=pL(omega,a), M(a,b)=pL(K(a),b), Q(a,b,c)=L(M(a,b),c). The normalization functionals are the original uA,uD,uE. The actual M and L spans imply that the actual Q spans E, by linear extension in its D input. The completed mass theorem is the pre-classification corollary (79.8), independent of Jordan coordinates. Positive constants are obtained from cone positivity and nonzero original mass functionals; they are not extra hypotheses. The scale theorem is an explicitly conditional successor using the source full recovery law, whose derivation from complete PRE is not supplied here. Neither it nor the mass theorem asserts Cjoint, common orientation, H13, event CP, physical resets, physical tensor copies, a time group or the complete source 81.8 quantum candidate. These applications and their proof organization are repository-derived; no novelty or independent-review claim is made.")),
        Describe.Lean(DescribeId.Create("mass-originalmasscalibration-K"),DeclarationHandle.Create("D5/S3/Quantum/Analysis/OriginalMassCalibration.K"),H("The first use of the original readout"),StatementSource.FromAuthor(Disp(DefinitionK())),AssessedProvenance.FromRepo(),Blocks(Paragraph(Text("OriginalData contains only the original bilinear L from D times A to E, the original real linear p from E to D, and the original omega in D. K(a)=p(L(omega,a)). No independent preparation K is supplied."))),DescribeRole.Definition),
        Describe.Lean(DescribeId.Create("mass-originalmasscalibration-M"),DeclarationHandle.Create("D5/S3/Quantum/Analysis/OriginalMassCalibration.M"),H("The second use of the same original readout"),StatementSource.FromAuthor(Disp(DefinitionM())),AssessedProvenance.FromRepo(),Blocks(Paragraph(Text("M(a,b)=p(L(p(L(omega,a)),b)). The p at both occurrences is the same field of OriginalData. There is no independently supplied M."))),DescribeRole.Definition),
        Describe.Lean(DescribeId.Create("mass-originalmasscalibration-Q"),DeclarationHandle.Create("D5/S3/Quantum/Analysis/OriginalMassCalibration.Q"),H("The actual three-input preparation"),StatementSource.FromAuthor(Disp(DefinitionQ())),AssessedProvenance.FromRepo(),Blocks(Paragraph(Text("Q(a,b,c)=L(M(a,b),c), using the same original bilinear L. The mass is uE applied to this actual Q."))),DescribeRole.Definition),
        Describe.Lean(DescribeId.Create("mass-originalmasscalibration-original-mass-factorization"),DeclarationHandle.Create("D5/S3/Quantum/Analysis/OriginalMassCalibration.original_mass_factorization"),H("Both actual masses factor with strictly positive constants"),StatementSource.FromAuthor(Disp(OriginalFactorization())),AssessedProvenance.FromRepo(),Blocks(Paragraph(Text("This is Corollary 79.4 for arbitrary nonzero finite-dimensional real A,D,E, closed generating cones and their strictly positive original masses. L is positive on the entire original D cone times the entire A cone, p is positive on the entire original E cone, and omega is positive. The actual M spans D and L spans E over the reals. Phi is positive and mass preserving and has no real fixed dual functional outside the line of uA. The two identities hold on every positive input, including zero and unequal masses, with weights (t,1-t) and (s*t,s*(1-t),1-s). Nothing assumes either mass factorization. The proof applies the new arbitrary-slot maximum principle to the actual two- and three-linear masses, extends to all real inputs, and obtains strict positivity from positive normalized states and real spanning. Real span is never identified with positive generation of an entangled cone."))),DescribeRole.Theorem),
        Describe.Lean(DescribeId.Create("mass-originalmasscalibration-original-mass-calibration"),DeclarationHandle.Create("D5/S3/Quantum/Analysis/OriginalMassCalibration.original_mass_calibration"),H("The same readout twice fixes the first scalar"),StatementSource.FromAuthor(Disp(OriginalCalibration())),AssessedProvenance.FromRepo(),Blocks(Paragraph(Text("This successor derives both mass factorizations from the same original cone data and positive asynchronous laws. Its additional assumptions are the original omega of mass one and the full real recovery identity p(Q(a,b,c))=uA(a)*M(b,c). No factorization or fixed-tensor conclusion is assumed. Span extension gives uD composed with p=(lambda/kappa)*uE and uE(L(d,c))=(kappa/lambda)*uD(d)*uA(c). Their composition calibrates pL. Applying that calibration twice to the original omega gives lambda=1. The theorem does not prove the PRE-to-recovery bridge, the pre-C13 classification, the Cjoint equivalence, the original scalar anchor, H13, or the whole quantum consumer. It is a conditional successor to the complete mass-factorization theorem, not a claim of completion of source Theorem 79.5."))),DescribeRole.Theorem))));

    private static Formula V(string s)=>F.Id(s);
    private static Formula R=>Call("Real");
    private static Formula One=>D(1);
    private static Formula Zero=>D(0);
    private static Formula Call(string s,params Formula[] a)=>new Formula.FunctionCall(FormulaIdentifier.Create(s),[..a]);
    private static Formula At(Formula f,params Formula[] a)=>new Formula.Apply(f,[..a]);
    private static Formula App(string s,params Formula[] a)=>At(V(s),a);
    private static Formula All(string s,Formula t,Formula b)=>new Formula.Bind(FormulaQuantifier.ForAll,FormulaIdentifier.Create(s),t,b);
    private static Formula Ex(string s,Formula t,Formula b)=>new Formula.Bind(FormulaQuantifier.Exists,FormulaIdentifier.Create(s),t,b);
    private static Formula Lam(string s,Formula t,Formula b)=>Seq(Grp(V(s),Colon,t),Mapsto,Sp,b);
    private static Formula And(Formula a,Formula b)=>new Formula.Logic(a,FormulaLogicOperator.And,b);
    private static Formula Imp(Formula a,Formula b)=>new Formula.Logic(a,FormulaLogicOperator.Implies,b);
    private static Formula Iff(Formula a,Formula b)=>new Formula.Logic(a,FormulaLogicOperator.Iff,b);
    private static Formula Eqf(Formula a,Formula b)=>Equal(a,b);
    private static Formula Lt(Formula a,Formula b)=>new Formula.Relation(a,FormulaRelationOperator.LessThan,b);
    private static Formula Ne(Formula a,Formula b)=>Seq(a,Sp,Neq,Sp,b);
    private static Formula Mul(Formula a,Formula b)=>new Formula.Binary(a,FormulaBinaryOperator.Multiply,b);
    private static Formula Addf(Formula a,Formula b)=>new Formula.Binary(a,FormulaBinaryOperator.Add,b);
    private static Formula Smul(Formula a,Formula b)=>Call("smul",a,b);
    private static Formula Arrow(Formula a,Formula b)=>new Formula.TypeArrow(a,b);
    private static Formula In(Formula x,Formula s)=>Call("Mem",x,s);
    private static Formula Chain(params Formula[] a){var b=a[^1];for(var i=a.Length-2;i>=0;i--)b=And(a[i],b);return b;}
    private static Formula Assuming(Formula b,params Formula[] p){for(var i=p.Length-1;i>=0;i--)b=Imp(p[i],b);return b;}
    private static Formula Lm(Formula a,Formula b)=>Call("LinearMap",R,a,b);
    private static Formula Dual(Formula a)=>Call("Dual",R,a);
    private static Formula Span(Formula s)=>Call("span",R,s);
    private static Formula Top(Formula a)=>Call("top",Call("Submodule",R,a));
    private static Formula Space(string n,Formula b,bool nontrivial=false){var a=V(n);var body=Seq(OpenBracket,Call("NormedAddCommGroup",a),CloseBracket,Sp,OpenBracket,Call("NormedSpace",R,a),CloseBracket,Sp,OpenBracket,Call("FiniteDimensional",R,a),CloseBracket,Sp,nontrivial?Seq(OpenBracket,Call("Nontrivial",a),CloseBracket,Sp,b):b);return All("v"+n,Call("Universe"),All(n,Call("Type",V("v"+n)),body));}
    private static Formula Indices(Formula b)=>All("vI",Call("Universe"),All("I",Call("Type",V("vI")),Seq(OpenBracket,Call("Fintype",V("I")),CloseBracket,Sp,OpenBracket,Call("DecidableEq",V("I")),CloseBracket,Sp,b)));
    private static Formula Strict(string c,string u,string a)=>All("x",V(a),Assuming(Lt(Zero,App(u,V("x"))),In(V("x"),V(c)),Ne(V("x"),Zero)));
    private static Formula FullDual(string p,string u,string a)=>All("f",Dual(V(a)),Imp(Eqf(Call("comp",V("f"),V(p)),V("f")),Ex("c",R,Eqf(V("f"),Smul(V("c"),V(u))))));
    private static Formula Base(string c,string u)=>Call("base",V(c),V(u));
    private static Formula Cube=>Call("pi",Call("univ",V("I")),Lam("i",V("I"),V("K")));
    private static Formula WeightPos=>All("i",V("I"),Lt(Zero,App("alpha",V("i"))));
    private static Formula WeightSum=>Eqf(Call("sum",V("alpha")),One);
    private static Formula ProductMass(string u,Formula a)=>Call("prod",Lam("i",V("I"),App(u,At(a,V("i")))));
    private static Formula Update(Formula a,Formula i)=>Call("update",a,i,App("Phi",At(a,i)));

    private static Formula AD=>Call("OriginalData",V("A"),V("D"),V("E"));
    private static Formula Preparation(string n,params Formula[] a){Formula[] all=[V("data"),..a];return Call(n,all);}
    private static Formula Scope(Formula b,bool nt=false)=>Space("A",Space("D",Space("E",All("data",AD,b),nt),nt),nt);
    private static Formula KA(Formula a)=>Preparation("K",a);
    private static Formula MM(Formula a,Formula b)=>Preparation("M",a,b);
    private static Formula QQ(Formula a,Formula b,Formula c)=>Preparation("Q",a,b,c);
    private static Formula LL(Formula d,Formula a)=>At(Call("L",V("data")),d,a);
    private static Formula PP(Formula z)=>At(Call("p",V("data")),z);
    private static Formula Omega=>Call("omega",V("data"));
    private static Formula DefinitionK()=>Scope(All("a",V("A"),Eqf(KA(V("a")),PP(LL(Omega,V("a"))))));
    private static Formula DefinitionM()=>Scope(All("a",V("A"),All("b",V("A"),Eqf(MM(V("a"),V("b")),PP(LL(KA(V("a")),V("b")))))));
    private static Formula DefinitionQ()=>Scope(All("a",V("A"),All("b",V("A"),All("c",V("A"),Eqf(QQ(V("a"),V("b"),V("c")),LL(MM(V("a"),V("b")),V("c")))))));
    private static Formula SpanM=>Eqf(Span(Call("range",Lam("ab",Call("Prod",V("A"),V("A")),MM(Call("fst",V("ab")),Call("snd",V("ab")))))),Top(V("D")));
    private static Formula SpanL=>Eqf(Span(Call("range",Lam("dc",Call("Prod",V("D"),V("A")),LL(Call("fst",V("dc")),Call("snd",V("dc")))))),Top(V("E")));
    private static Formula SpanQ=>Eqf(Span(Call("range",Lam("abc",Call("Prod",V("A"),Call("Prod",V("A"),V("A"))),QQ(Call("fst",V("abc")),Call("fst",Call("snd",V("abc"))),Call("snd",Call("snd",V("abc"))))))),Top(V("E")));
    private static Formula TwoFactor=>All("a",V("A"),All("b",V("A"),Eqf(App("uD",MM(V("a"),V("b"))),Mul(Mul(V("lambda"),App("uA",V("a"))),App("uA",V("b"))))));
    private static Formula ThreeFactor=>All("a",V("A"),All("b",V("A"),All("c",V("A"),Eqf(App("uE",QQ(V("a"),V("b"),V("c"))),Mul(Mul(Mul(V("kappa"),App("uA",V("a"))),App("uA",V("b"))),App("uA",V("c")))))));
    private static Formula Masses(Formula b)=>All("uA",Dual(V("A")),All("uD",Dual(V("D")),All("uE",Dual(V("E")),b)));
    private static Formula PosInput(string n,Formula b)=>All(n,V("A"),Imp(In(V(n),V("CA")),b));
    private static Formula TwoLaw=>PosInput("a",PosInput("b",Eqf(App("uD",MM(V("a"),V("b"))),Addf(Mul(V("t"),App("uD",MM(App("Phi",V("a")),V("b")))),Mul(Subtract(One,V("t")),App("uD",MM(V("a"),App("Phi",V("b")))))))));
    private static Formula ThreeLaw=>PosInput("a",PosInput("b",PosInput("c",Eqf(App("uE",QQ(V("a"),V("b"),V("c"))),Addf(Addf(Mul(Mul(V("s"),V("t")),App("uE",QQ(App("Phi",V("a")),V("b"),V("c")))),Mul(Mul(V("s"),Subtract(One,V("t"))),App("uE",QQ(V("a"),App("Phi",V("b")),V("c"))))),Mul(Subtract(One,V("s")),App("uE",QQ(V("a"),V("b"),App("Phi",V("c"))))))))));
    private static Formula OriginalFactorization()=>OriginalStatement(Ex("lambda",R,Ex("kappa",R,Chain(Lt(Zero,V("lambda")),Lt(Zero,V("kappa")),TwoFactor,ThreeFactor))));
    private static Formula OriginalStatement(Formula result,params Formula[] more)
    {
        Formula body=Assuming(result,
            Eqf(Span(V("CA")),Top(V("A"))),Eqf(Span(V("CD")),Top(V("D"))),Eqf(Span(V("CE")),Top(V("E"))),
            Strict("CA","uA","A"),Strict("CD","uD","D"),Strict("CE","uE","E"),
            All("d",V("D"),Imp(In(V("d"),V("CD")),PosInput("a",In(LL(V("d"),V("a")),V("CE"))))),
            All("z",V("E"),Imp(In(V("z"),V("CE")),In(PP(V("z")),V("CD")))),
            In(Omega,V("CD")),SpanM,SpanL,Call("MapsTo",V("Phi"),V("CA"),V("CA")),
            Eqf(Call("comp",V("uA"),V("Phi")),V("uA")),FullDual("Phi","uA","A"),
            Lt(Zero,V("t")),Lt(V("t"),One),Lt(Zero,V("s")),Lt(V("s"),One),TwoLaw,ThreeLaw);
        // Additional source premises precede the common implication telescope.
        body=Assuming(body,more);
        body=All("t",R,All("s",R,body));
        body=All("Phi",Lm(V("A"),V("A")),body);
        body=All("CA",Call("ProperCone",R,V("A")),All("CD",Call("ProperCone",R,V("D")),All("CE",Call("ProperCone",R,V("E")),body)));
        return Scope(Masses(body),true);
    }
    private static Formula Recovery=>All("a",V("A"),All("b",V("A"),All("c",V("A"),Eqf(PP(QQ(V("a"),V("b"),V("c"))),Smul(App("uA",V("a")),MM(V("b"),V("c")))))));
    private static Formula CalibrationResult=>Chain(
        Lt(Zero,V("kappa")),
        All("a",V("A"),All("b",V("A"),Eqf(App("uD",MM(V("a"),V("b"))),Mul(App("uA",V("a")),App("uA",V("b")))))),
        ThreeFactor,
        All("z",V("E"),Eqf(App("uD",PP(V("z"))),Mul(Call("inv",V("kappa")),App("uE",V("z"))))),
        All("d",V("D"),All("c",V("A"),Eqf(App("uE",LL(V("d"),V("c"))),Mul(Mul(V("kappa"),App("uD",V("d"))),App("uA",V("c")))))),
        All("d",V("D"),All("c",V("A"),Eqf(App("uD",PP(LL(V("d"),V("c")))),Mul(App("uD",V("d")),App("uA",V("c")))))));
    private static Formula OriginalCalibration()=>OriginalStatement(Ex("kappa",R,CalibrationResult),Eqf(App("uD",Omega),One),Recovery);
}
