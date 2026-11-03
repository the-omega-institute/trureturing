using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Algebra;

internal sealed class PauliFixedProductFamilyDocument : IScribeDocumentDefinition
{

    private static DocumentBlock Display(Formula x) => new DocumentBlock.DisplayFormula(x);
    private static Formula V(string name) => F.Id(name);
    private static Formula R => Seq(Mathbb, Grp(V("R")));
    private static Formula J => V("J");
    private static Formula Joint => V("V");
    private static Formula Index => Call("Fin", D(4));
    private static Formula P(Formula x) => Seq(Open, x, Close);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula All(string names, Formula type, Formula body)
    {
        foreach (var name in names.Split(' ').Reverse())
            body = new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
        return body;
    }
    private static Formula Some(string names, Formula type, Formula body)
    {
        foreach (var name in names.Split(' ').Reverse())
            body = new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
        return body;
    }
    private static Formula Rel(Formula x, FormulaRelationOperator op, Formula y) => new Formula.Relation(x, op, y);
    private static Formula Eql(Formula x, Formula y) => Rel(x, FormulaRelationOperator.Equal, y);
    private static Formula Ne(Formula x, Formula y) => Rel(x, FormulaRelationOperator.NotEqual, y);
    private static Formula Leq(Formula x, Formula y) => Rel(x, FormulaRelationOperator.LessThanOrEqual, y);
    private static Formula Less(Formula x, Formula y) => Rel(x, FormulaRelationOperator.LessThan, y);
    private static Formula Mem(Formula x, Formula y) => Rel(x, FormulaRelationOperator.MemberOf, y);
    private static Formula Logic(Formula x, FormulaLogicOperator op, Formula y) => new Formula.Logic(P(x), op, P(y));
    private static Formula And(params Formula[] xs) => xs.Reverse().Aggregate((x,y) => Logic(y, FormulaLogicOperator.And, x));
    private static Formula Or(params Formula[] xs) => xs.Reverse().Aggregate((x,y) => Logic(y, FormulaLogicOperator.Or, x));
    private static Formula Imp(Formula x, Formula y) => Logic(x, FormulaLogicOperator.Implies, y);
    private static Formula IffEq(Formula x, Formula y) => Logic(x, FormulaLogicOperator.Iff, y);
    private static Formula Add(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Add, y);
    private static Formula Sub(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Subtract, y);
    private static Formula Mul(params Formula[] xs) => xs.Aggregate((x,y) => new Formula.Binary(x, FormulaBinaryOperator.Multiply, y));
    private static Formula Pow(Formula x) => new Formula.Power(P(x), D(2));
    private static Formula Fr(Formula x, Formula y) => new Formula.Fraction(x, y);
    private static Formula Root(Formula x) => Seq(Sqrt, Grp(x));
    private static Formula Norm(Formula x) => Seq(Vert, Sp, x, Vert);
    private static Formula Abs(Formula x) => Seq(Lvert, Sp, x, Rvert);
    private static Formula Tuple(params Formula[] xs) => P(Seq(xs.SelectMany((x,i) => i == 0 ? new[] {x} : new[] {Comma,Sp,x}).ToArray()));
    private static Formula At(Formula a, byte i) => new Formula.Subscript(a, D(i));
    private static Formula Basis(byte i) => Call("e", D(i));
    private static Formula Tensor(Formula x, Formula y) => Call("T", x, y);
    private static Formula Inner(Formula x, Formula y) => Seq(Langle, Sp, x, Comma, y, Rangle);
    private static Formula Spin(Formula x, Formula y) => Call("S", x, y);
    private static Formula Action(Formula t, Formula x, Formula y) => Call("D", t, x, y);
    private static Formula Product(Formula x, Formula y) => Call("M", x, y);
    private static Formula GammaAt(Formula t, Formula h, Formula x) => Call("Gamma", t, h, x);
    private static Formula SetOf(string name, Formula type, Formula condition) =>
        Seq(OpenBrace, Sp, V(name), Colon, Sp, type, Sp, Mid, Sp, condition, Sp, CloseBrace);
    private static Formula Greatest(Formula set, Formula value) => And(Mem(value, set),
        All("r", R, Imp(Mem(V("r"), set), Leq(V("r"), value))));
    private static Formula Least(Formula set, Formula value) => And(Mem(value, set),
        All("r", R, Imp(Mem(V("r"), set), Leq(value, V("r")))));
    private static Formula Unit(Formula a) => Eql(Norm(a), D(1));
    private static Formula Spatial(Formula a) => Tuple(At(a,1), At(a,2), At(a,3));
    private static Formula Dmap(Formula t, Formula a) => Call("D", t, a);
    private static Formula Report(Formula t) => Call("R", t);
    private static Formula LocalBound(Formula t) => Root(Add(D(1), Pow(t)));
    private static Formula Gram(Formula t, Formula a) => Call("G", t, a);
    private static Formula LabelGram(Formula t, Formula a) => Call("H", t, a);
    private static Formula Support(Formula t) => Call("W", t);
    private static Formula Fixed(Formula t) => Call("Z", t);
    private static Formula Spectrum(Formula t) => Call("Lambda", t);
    private static Formula Eigen(Formula t, Formula lam, bool label) => Some("a", J,
        And(Ne(V("a"), D(0)), Eql(label ? LabelGram(t,V("a")) : Gram(t,V("a")), Mul(lam,V("a")))));
    private static Formula FamilyContract(Formula t)
    {
        var a=V("a"); var b=V("b"); var c=V("c"); var d=V("d");
        var x=V("X"); var y=V("Y"); var z=V("Z"); var i=V("i"); var j=V("j");
        return And(
            Eql(Call("dim", R, J), D(4)), Eql(Call("dim", R, Joint), D(1,6)),
            All("i",Index,Eql(Call("b",i),Call("e",i))),
            All("i j",Index,Eql(Call("B",i,j),Tensor(Call("e",i),Call("e",j)))),
            All("a b",J,Eql(Spin(a,b),Spin(b,a))), All("a",J,Eql(Spin(Basis(0),a),a)),
            All("a b c",J,Eql(Inner(Spin(a,b),c),Inner(a,Spin(b,c)))),
            All("a b c",J,Eql(Action(t,a,Spin(b,c)),Add(Spin(Action(t,a,b),c),Spin(b,Action(t,a,c))))),
            Eql(Action(t,Basis(1),Basis(2)),Basis(3)),
            All("X Y",Joint,Eql(Product(x,y),Product(y,x))),
            All("X",Joint,Eql(Product(Tensor(Basis(0),Basis(0)),x),x)),
            All("X Y Z",Joint,Eql(Inner(Product(x,y),z),Inner(x,Product(y,z)))),
            All("X",Joint,And(Leq(D(0),Inner(x,x)),IffEq(Eql(Inner(x,x),D(0)),Eql(x,D(0))))),
            All("a b c d",J,And(
                Eql(Product(Tensor(a,Basis(0)),Tensor(c,d)),Tensor(Spin(a,c),d)),
                Eql(Product(Tensor(Basis(0),b),Tensor(c,d)),Tensor(c,Spin(b,d))),
                Eql(GammaAt(t,Tensor(a,b),Tensor(c,Basis(0))),Tensor(Action(t,a,c),b)),
                Eql(GammaAt(t,Tensor(a,b),Tensor(Basis(0),d)),Tensor(a,Action(t,b,d))))),
            Eql(Report(t),Mul(D(2,8,8),Pow(t))));
    }
    private static Formula Defects(Formula t)
    {
        var a=V("a"); var b=V("b"); var r=V("s");
        return And(
            Greatest(SetOf("s",R,Some("a",J,And(Unit(a),Eql(r,Norm(Action(t,a,a)))))),Fr(Abs(t),D(2))),
            Greatest(SetOf("s",R,Some("b",J,And(Unit(b),Eql(r,Norm(Action(t,Basis(0),b)))))),Abs(t)),
            All("a b",J,Leq(Norm(Spin(a,b)),Mul(Root(D(2)),Norm(a),Norm(b)))),
            All("a b",J,Leq(Norm(Action(t,a,b)),Mul(LocalBound(t),Norm(a),Norm(b)))),
            Eql(new Formula.Subscript(Norm(Call("U",t)),V("op")),Abs(t)));
    }
    private static Formula Constants(Formula t)
    {
        var a=V("a"); var b=V("b"); var r=V("s");
        return And(Unit(Basis(0)),
            Greatest(SetOf("s",R,Some("a b",J,And(Unit(a),Unit(b),Eql(r,Norm(Spin(a,b)))))),Root(D(2))),
            Greatest(SetOf("s",R,Some("a b",J,And(Unit(a),Unit(b),Eql(r,Norm(Action(t,a,b)))))),LocalBound(t)),
            Greatest(SetOf("s",R,Some("i j k",Index,
                Eql(r,Norm(Call("kappa",V("i"),V("j"),V("k")))))),D(1)));
    }
    private static Formula ActionData(Formula t)
    {
        var a=V("a"); var r=V("r"); var lam=V("lambda");
        return And(All("a",J,Eql(Gram(t,a),Tuple(D(0),Mul(Add(D(2),Pow(t)),At(a,1)),
                Mul(Add(D(2),Pow(t)),At(a,2)),Mul(D(2),At(a,3))))),
            All("a",J,IffEq(All("i",Index,Eql(Action(t,Call("e",V("i")),a),D(0))),
                Some("r",R,Eql(a,Mul(r,Basis(0)))))),
            All("a",J,IffEq(Mem(a,Support(t)),Eql(At(a,0),D(0)))),
            All("a",J,IffEq(Eql(Dmap(t,a),D(0)),Some("r",R,Eql(a,Mul(r,P(Sub(Basis(0),Mul(t,Basis(3))))))))),
            All("lambda",R,IffEq(Eigen(t,lam,false),Or(Eql(lam,D(0)),Eql(lam,Add(D(2),Pow(t))),Eql(lam,D(2))))));
    }
    private static Formula LabelData(Formula t)
    {
        var a=V("a"); var lam=V("lambda");
        return And(All("a",J,Eql(LabelGram(t,a),Tuple(Add(Mul(D(2),Pow(t),At(a,0)),Mul(D(2),t,At(a,3))),
                Mul(D(2),At(a,1)),Mul(D(2),At(a,2)),Add(Mul(D(2),t,At(a,0)),Mul(D(2),At(a,3)))))),
            All("lambda",R,IffEq(Eigen(t,lam,true),Or(Eql(lam,D(0)),Eql(lam,D(2)),Eql(lam,Mul(D(2),P(Add(D(1),Pow(t)))))))),
            Least(Spectrum(t),D(2)),Eql(Call("sigma",t),Root(D(2))));
    }
    private static Formula DiagonalActive(Formula t) => Some("a",J,Ne(Action(t,V("a"),V("a")),D(0)));
    private static Formula UnitActive(Formula t) => Ne(Dmap(t,Basis(0)),D(0));
    private static Formula SupportGap(Formula t)
    {
        var a=V("a");
        return And(Eql(Support(t),new Formula.Power(P(Fixed(t)),Perp)),
            All("a",J,Imp(Mem(a,Support(t)),Leq(Mul(D(2),Pow(Norm(a))),Inner(a,Gram(t,a))))),
            And(Mem(Basis(3),Support(t)),Unit(Basis(3)),Eql(Gram(t,Basis(3)),Mul(D(2),Basis(3)))),
            Ne(Call("D",t),D(0)),
            Imp(Ne(t,D(0)),And(DiagonalActive(t),UnitActive(t),Ne(Call("ker",Call("D",t)),Fixed(t)))),
            All("a",J,Eql(Action(D(0),a,a),D(0))),Eql(Dmap(D(0),Basis(0)),D(0)));
    }
    private static DocumentBlock[] Notation()
    {
        var t=V("t"); var a=V("a"); var b=V("b"); var c=V("c"); var d=V("d");
        var x=V("X"); var y=V("Y"); var h=V("H"); var i=V("i"); var j=V("j"); var k=V("k");
        Formula SumI(Formula body) => Seq(new Formula.Subscript(Sum,Seq(i,Colon,Sp,Index)),body);
        Formula SpatialAction(Formula u, Formula v) => Tuple(D(0),Call("cross",Spatial(u),Spatial(v)));
        return [
            Paragraph(Text("Notation is shared by every display below. J is EuclideanSpace over the reals on Fin 4, identified with a scalar and a spatial vector in real three-space; V is its real Hilbert tensor product. T(a,b) denotes a tensor b. Coordinates a_i have i in Fin 4. All inner products and norms are the fixed Euclidean and positive tensor-product ones. Scalar juxtaposition denotes real scalar multiplication. The cross and dot operations are the usual real three-dimensional cross and dot products. An ordered pair (scalar, spatial triple) denotes its four-vector in J. The vectors e(i) are EuclideanSpace.single i 1; e(0) is the unit, e(1), e(2), e(3) are x, y, z. b is localBasis and B is jointBasis, the complete orthonormal bases. Every displayed parameter and vector is explicitly quantified.")),
            Display(And(Eql(J,Call("EuclideanSpace",R,Index)),Eql(Joint,Call("TensorProduct",R,J,J)),
                All("i",Index,Eql(Call("e",i),Call("single",i,D(1)))))),
            Display(All("a b",J,And(
                Eql(Spin(a,b),Tuple(Add(Mul(At(a,0),At(b,0)),Call("dot",Spatial(a),Spatial(b))),
                    Add(Mul(At(a,0),Spatial(b)),Mul(At(b,0),Spatial(a))))),
                Eql(Call("C",a,b),SpatialAction(a,b))))),
            Display(All("t",R,All("a b",J,Eql(Action(t,a,b),Tuple(D(0),Call("cross",
                Tuple(At(a,1),At(a,2),Add(At(a,3),Mul(t,At(a,0)))),Spatial(b))))))),
            Display(All("a b c d",J,Eql(Product(Tensor(a,b),Tensor(c,d)),
                Sub(Tensor(Spin(a,c),Spin(b,d)),Tensor(Call("C",a,c),Call("C",b,d)))))),
            Display(All("t",R,All("a b c d",J,Eql(GammaAt(t,Tensor(a,b),Tensor(c,d)),
                Add(Tensor(Action(t,a,c),Spin(b,d)),Tensor(Spin(a,c),Action(t,b,d))))))),
            Paragraph(Text("S, C and D(t) denote the existing bilinear maps S, C, D t; M and Gamma(t) are the existing fixed joint product and actual joint action, extended linearly from pure tensors. E(t,H,X,Y) is E t H X Y. R(t) is reportSquared t, with all six basis indices summed independently. Each output norm includes every coordinate; there is no averaging.")),
            Display(All("t",R,All("H X Y",Joint,Eql(Call("E",t,h,x,y),
                Sub(Sub(GammaAt(t,h,Product(x,y)),Product(GammaAt(t,h,x),y)),Product(x,GammaAt(t,h,y))))))),
            Display(All("t",R,Eql(Report(t),Seq(new Formula.Subscript(Sum,
                Seq(V("i"),Comma,V("j"),Comma,V("k"),Comma,V("l"),Comma,V("m"),Comma,V("n"),Colon,Sp,Index)),
                Pow(Norm(Call("E",t,Tensor(Call("e",V("i")),Call("e",V("j"))),
                    Tensor(Call("e",V("k")),Call("e",V("l"))),Tensor(Call("e",V("m")),Call("e",V("n")))))))))),
            Paragraph(Text("U(t) means unitOperator t, the continuous linear map b mapped to D(t,e(0),b); its norm with subscript op is the operator norm. G(t) means actionGram t, H(t) means labelGram t. Adjoint is taken for the same Euclidean inner product. W(t) means actionSupport t, the real span of all actual D(t,e(i),e(j)); Z(t) means commonFixed t, the intersection of the four action kernels. ker D(t) is the kernel of the label-linear map a mapped to D(t,a), whereas D(t,a)=0 is equality of linear operators. Orthogonal complement always uses the fixed Euclidean inner product.")),
            Display(All("t",R,And(All("b",J,Eql(Call("U",t,b),Action(t,Basis(0),b))),
                Eql(Call("G",t),SumI(Call("compose",Call("adj",Dmap(t,Call("e",i))),Dmap(t,Call("e",i))))),
                Eql(Call("H",t),SumI(Call("compose",Call("adj",Call("flipD",t,Call("e",i))),Call("flipD",t,Call("e",i))))),
                All("a b",J,Eql(Call("flipD",t,b,a),Action(t,a,b))),
                Eql(Support(t),Call("span",R,SetOf("v",J,Some("i j",Index,Eql(V("v"),Action(t,Call("e",i),Call("e",j))))))),
                Eql(Fixed(t),SetOf("a",J,All("i",Index,Eql(Action(t,Call("e",i),a),D(0)))))))),
            Paragraph(Text("Lambda(t) is positiveActionSpectrum t; sigma(t) is actionGap t, the square root of the infimum of that set. Membership and universal inequalities are both displayed for every greatest or least value below, so attainment and the full domain are retained. kappa(i,j,k) is curvature i j k on precisely the original finite basis, not a redefined unit-ball maximum.")),
            Display(All("t",R,And(Eql(Spectrum(t),SetOf("lambda",R,And(Less(D(0),V("lambda")),Eigen(t,V("lambda"),false)))),
                Eql(Call("sigma",t),Root(Call("inf",Spectrum(t))))))),
            Display(All("i j k",Index,Eql(Call("kappa",i,j,k),
                Sub(Spin(Call("e",i),Spin(Call("e",j),Call("e",k))),Spin(Call("e",j),Spin(Call("e",i),Call("e",k)))))))
        ];
    }

    private static DocumentBlock Theorem(string name, string heading, Formula formula, string prose) =>
        Describe.Lean(DescribeId.Create(name.Replace('_','-')),
            DeclarationHandle.Create("D5/S3/Quantum/Algebra/PauliFixedProductFamily." + name),
            H(heading), StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);
    public DocumentDefinition Create()
    {
        var t=V("t");
        var blocks=Notation().Concat(new DocumentBlock[] {
            Theorem("residual_scaling", "The actual residual scales on all joint inputs",
                All("t",R,All("H X Y",Joint,Eql(Call("E",t,V("H"),V("X"),V("Y")),
                    Mul(t,Call("E",D(1),V("H"),V("X"),V("Y")))))),
                "The actual action and residual are affine in the real parameter. The zero-parameter residual vanishes on the complete product basis, and multilinearity extends this equality through the basis span in every slot, including arbitrary sums of pure tensors."),
            Theorem("full_report", "All ordered labels and every output coordinate",
                All("t",R,Eql(Report(t),Mul(D(2,8,8),Pow(t)))),
                "The complete unaveraged report uses 4096 ordered triples of the sixteen-element joint basis. At parameter one, six complete first-label blocks contribute 48 each; the other ten blocks vanish. Each squared norm includes every output coordinate. All-input scaling gives the displayed identity for every real parameter."),
            Theorem("family_contract", "The complete fixed realization and all four original identities",
                All("t",R,FamilyContract(t)),
                "These are the complete fifteen conjuncts of the realization contract. The fixed products and positive inner products serve every parameter. No alternation, Jacobi, vanishing unit generator or global joint derivation law is assumed."),
            Theorem("exact_defects", "Attained defects, all-input bounds and operator norm",
                All("t",R,Defects(t)),
                "The diagonal maximum is attained at (e(0)+e(1))/sqrt(2); the unit-generator maximum is attained at e(1). The universal estimates follow from nonnegative square decompositions on arbitrary real coordinates, and the last conjunct is the norm of the actual continuous unit-generator operator."),
            Theorem("exact_constants", "Every original local constant is sharp",
                All("t",R,Constants(t)),
                "The unit length is one. The spin bound is attained with both inputs (e(0)+e(1))/sqrt(2), and the action bound at (t e(0)+e(3))/sqrt(1+t squared) and e(1). For arbitrary local a,b,c, the spin commutator is minus C(C(a,b),c), by the general vector triple-product identity. Two applications of the all-input cross-channel bound, obtained from the existing action estimate at parameter zero, give commutator norm at most norm(a) norm(b) norm(c). Specialization to the original unit basis gives the curvature upper bound without enumerating its entries. The same identity and orthonormal normalization give kappa(1,2,2)=e(1), attaining one on the original finite domain. This calibration supplies no new report escape or numeric consumer."),
            Theorem("exact_action_data", "The full action Gram, both kernels, support and eigenvalues",
                All("t",R,ActionData(t)),
                "The coordinate identity holds on every vector. The label kernel and common fixed kernel are distinguished as actual operator statements. The exact coordinates retain eigenvalue multiplicities and their collision at zero parameter."),
            Theorem("exact_label_data", "The label Gram and attained positive action minimum",
                All("t",R,LabelData(t)),
                "H is the label Gram, distinct from the action Gram G. The displayed eigenvalue equivalence includes all real eigenvalues, including collisions. The positive action eigenvalue minimum is attained at e(3), and its square-root gap is uniform."),
            Theorem("exact_support_gap", "Complete support, uniform gap, activity and zero boundary",
                All("t",R,SupportGap(t)),
                "Every support and activity conjunct concerns the same actual maps. At parameter zero the diagonal and unit-generator defects vanish, while the spatial action remains nonzero and the positive support gap remains sqrt(2). These are algebraic conclusions for this realization; no physical acquisition or general reconstruction conclusion follows.")
        }).ToArray();
        return DocumentDefinition.Create(ScribeNode.Create(
            "Fixed spin products, the actual real Pauli action and complete unaveraged residual with exact local data.",
            H("Fixed positive products and the complete actual Pauli family"), Blocks(blocks)));
    }
}
