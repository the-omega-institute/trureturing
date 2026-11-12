using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Analysis;

internal sealed class AsynchronousTensorMassDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()=>DocumentDefinition.Create(ScribeNode.Create("The asynchronous algebraic tensor sum has only the original tensor mass as fixed functional.",H("The full algebraic tensor fixed dual"),Blocks(
        Paragraph(Text("This is the original arbitrary finite asynchronous tensor carrier of Quantum Origin V, Lemma 79.3. Finite I with positive weights summing to one is necessarily nonempty, so it includes every r at least one without restricting r. The normalized set is the entire CircuitBalancedConfirmation.base of C.toPointedCone and the original u, with compactness, convexity and spanning given by the same normalized base geometry. All dual functionals are real algebraic functionals. The tensor product is used only for its universal property and its pure-tensor spanning property. The full complex spectral disk, peripheral semisimplicity and algebraic multiplicity-one assertions remain separate obligations.")),
        Describe.Lean(DescribeId.Create("mass-asynchronoustensormass-asynchronous"),DeclarationHandle.Create("D5/S3/Quantum/Analysis/AsynchronousTensorMass.asynchronous"),H("The algebraic asynchronous sum"),StatementSource.FromAuthor(Disp(AsyncDefinition())),AssessedProvenance.FromRepo(),Blocks(Paragraph(Text("The carrier is the actual finite algebraic real PiTensorProduct. The sum updates one slot by Phi and leaves every other slot unchanged. Alpha may be arbitrary in this definition; the theorem imposes strict positivity and total mass one. No positive cone on this tensor product and no physical copies are supplied."))),DescribeRole.Definition),
        Describe.Lean(DescribeId.Create("mass-asynchronoustensormass-tensormass"),DeclarationHandle.Create("D5/S3/Quantum/Analysis/AsynchronousTensorMass.tensorMass"),H("The original tensor mass functional"),StatementSource.FromAuthor(Disp(MassDefinition())),AssessedProvenance.FromRepo(),Blocks(Paragraph(Text("The universal-property lift of the multilinear product of the original u is the tensor mass. Its value on each pure tensor is the product of the original slot masses."))),DescribeRole.Definition),
        Describe.Lean(DescribeId.Create("mass-asynchronoustensormass-asynchronous-tprod"),DeclarationHandle.Create("D5/S3/Quantum/Analysis/AsynchronousTensorMass.asynchronous_tprod"),H("The action on every pure tensor"),StatementSource.FromAuthor(Disp(PureAction())),AssessedProvenance.FromRepo(),Blocks(Paragraph(Text("Apply PiTensorProduct.map_tprod to each slot map and distribute the finite linear sum. This formula is the step used to pass between a fixed tensor functional and its multilinear form."))),DescribeRole.Theorem),
        Paragraph(Text("The classical flip qualification in Corollary 79.4 follows directly from this action formula. Let v be any nonzero real vector with Phi(v)=-v and let the finite weights sum to one. Multilinearity gives tprod(update(const(v),j,-v))=-tprod(const(v)) for every slot j. The weighted sum is therefore -tprod(const(v)). This is an eigenvalue -1 for every positive tensor order. To check that the tensor is nonzero, choose a real dual f with f(v)=1, using Module.Projective.exists_dual_eq_one. Applying tensorMass(f) to tprod(const(v)) gives the product of ones, hence one. If u(v)=0 and the index type is nonempty, tensorMass(u) evaluates to zero. For the classical two-state flip, v=(1,-1) is precisely such a zero-mass vector. Thus fixed-dual rigidity does not imply convergence of asynchronous iterates, loss of all correlations, a decay rate or a physical continuous time evolution. This is an algebraic consequence of the displayed action and the multilinear laws; it needs no cone on the tensor space.")),
        Disp(FlipConsequence()),
        Describe.Lean(DescribeId.Create("mass-asynchronoustensormass-fixed-tensor-dual"),DeclarationHandle.Create("D5/S3/Quantum/Analysis/AsynchronousTensorMass.fixed_tensor_dual"),H("All real fixed functionals, with an exact converse"),StatementSource.FromAuthor(Disp(TensorTheorem())),AssessedProvenance.FromRepo(),Blocks(Paragraph(Text("For arbitrary nonzero finite-dimensional real proper-cone data and every finite positive weight family, a real linear functional on the full algebraic tensor carrier is fixed exactly when it is a scalar multiple of the original tensor mass. Evaluating on pure tensors gives the asynchronous multilinear identity; the proved maximum principle gives factorization, and the universal property gives equality on the whole tensor space. The converse uses u composed with Phi equals u and the sum of the weights. This establishes only the fixed-space clause of (79.6), not algebraic simplicity or the complex spectral clauses of Lemma 79.3."))),DescribeRole.Theorem))));

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
    private static Formula Imp(Formula a,Formula b)=>new Formula.Logic(a,FormulaLogicOperator.Implies,b);
    private static Formula Iff(Formula a,Formula b)=>new Formula.Logic(a,FormulaLogicOperator.Iff,b);
    private static Formula Eqf(Formula a,Formula b)=>Equal(a,b);
    private static Formula Lt(Formula a,Formula b)=>new Formula.Relation(a,FormulaRelationOperator.LessThan,b);
    private static Formula Ne(Formula a,Formula b)=>Seq(a,Sp,Neq,Sp,b);
    private static Formula Smul(Formula a,Formula b)=>Call("smul",a,b);
    private static Formula Arrow(Formula a,Formula b)=>new Formula.TypeArrow(a,b);
    private static Formula In(Formula x,Formula s)=>Call("Mem",x,s);
    private static Formula Assuming(Formula b,params Formula[] p){for(var i=p.Length-1;i>=0;i--)b=Imp(p[i],b);return b;}
    private static Formula Lm(Formula a,Formula b)=>Call("LinearMap",R,a,b);
    private static Formula Dual(Formula a)=>Call("Dual",R,a);
    private static Formula Span(Formula s)=>Call("span",R,s);
    private static Formula Top(Formula a)=>Call("top",Call("Submodule",R,a));
    private static Formula Space(string n,Formula b,bool nontrivial=false,bool finite=true)
    {
        var a=V(n);
        if(nontrivial) b=Seq(OpenBracket,Call("Nontrivial",a),CloseBracket,Sp,b);
        if(finite) b=Seq(OpenBracket,Call("FiniteDimensional",R,a),CloseBracket,Sp,b);
        b=Seq(OpenBracket,Call("NormedAddCommGroup",a),CloseBracket,Sp,OpenBracket,Call("NormedSpace",R,a),CloseBracket,Sp,b);
        return All("v"+n,Call("Universe"),All(n,Call("Type",V("v"+n)),b));
    }
    private static Formula Indices(Formula b,bool decidable=true)
    {
        if(decidable) b=Seq(OpenBracket,Call("DecidableEq",V("I")),CloseBracket,Sp,b);
        return All("vI",Call("Universe"),All("I",Call("Type",V("vI")),Seq(OpenBracket,Call("Fintype",V("I")),CloseBracket,Sp,b)));
    }
    private static Formula Strict(string c,string u,string a)=>All("x",V(a),Assuming(Lt(Zero,App(u,V("x"))),In(V("x"),V(c)),Ne(V("x"),Zero)));
    private static Formula FullDual(string p,string u,string a)=>All("f",Dual(V(a)),Imp(Eqf(Call("comp",V("f"),V(p)),V("f")),Ex("c",R,Eqf(V("f"),Smul(V("c"),V(u))))));
    private static Formula WeightPos=>All("i",V("I"),Lt(Zero,App("alpha",V("i"))));
    private static Formula WeightSum=>Eqf(Call("sum",V("alpha")),One);
    private static Formula ProductMass(string u,Formula a)=>Call("prod",Lam("i",V("I"),App(u,At(a,V("i")))));
    private static Formula Tensor=>Call("PiTensorProduct",R,Call("constantFamily",V("I"),V("A")));
    private static Formula TMass=>Call("tensorMass",V("u"));
    private static Formula Async=>Call("asynchronous",V("Phi"),V("alpha"));
    private static Formula AsyncDefinition()=>Space("A",Indices(All("Phi",Lm(V("A"),V("A")),All("alpha",Arrow(V("I"),R),Eqf(Async,Call("sum",Lam("j",V("I"),Smul(App("alpha",V("j")),Call("tensorMap",Lam("i",V("I"),Call("ifThenElse",Eqf(V("i"),V("j")),V("Phi"),Call("identity",V("A")))))))))))),finite:false);
    private static Formula MassDefinition()=>Space("A",Indices(All("u",Dual(V("A")),All("a",Arrow(V("I"),V("A")),Eqf(At(TMass,Call("tprod",R,V("a"))),ProductMass("u",V("a"))))),decidable:false),finite:false);
    private static Formula FlipConsequence()
    {
        var v=V("v");
        var tensor=Call("tprod",R,Lam("i",V("I"),v));
        var negative=Smul(Subtract(Zero,One),tensor);
        var result=new Formula.Logic(Eqf(At(Async,tensor),negative),FormulaLogicOperator.And,Ne(tensor,Zero));
        return Space("A",Indices(All("Phi",Lm(V("A"),V("A")),All("alpha",Arrow(V("I"),R),All("v",V("A"),Assuming(result,WeightSum,Ne(v,Zero),Eqf(App("Phi",v),Subtract(Zero,v))))))),finite:false);
    }
    private static Formula PureAction()=>Space("A",Indices(All("Phi",Lm(V("A"),V("A")),All("alpha",Arrow(V("I"),R),All("a",Arrow(V("I"),V("A")),Eqf(At(Async,Call("tprod",R,V("a"))),Call("sum",Lam("j",V("I"),Smul(App("alpha",V("j")),Call("tprod",R,Call("update",V("a"),V("j"),App("Phi",At(V("a"),V("j"))))))))))))),finite:false);
    private static Formula TensorTheorem()=>Space("A",Indices(All("C",Call("ProperCone",R,V("A")),All("u",Dual(V("A")),All("Phi",Lm(V("A"),V("A")),All("alpha",Arrow(V("I"),R),All("g",Dual(Tensor),Assuming(Iff(Eqf(Call("comp",V("g"),Async),V("g")),Ex("c",R,Eqf(V("g"),Smul(V("c"),TMass)))),Eqf(Span(V("C")),Top(V("A"))),Strict("C","u","A"),Call("MapsTo",V("Phi"),V("C"),V("C")),Eqf(Call("comp",V("u"),V("Phi")),V("u")),FullDual("Phi","u","A"),WeightPos,WeightSum))))))),true);

}
