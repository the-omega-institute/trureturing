using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Algebra;

internal sealed class PauliFixedProductLinearDocument : IScribeDocumentDefinition
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

    private static Formula Constant => Add(D(1),Mul(D(2),Root(D(2))));
    private static Formula Eps(Formula t) => Call("epsilon",t);
    private static Formula Endpoint => Fr(D(1),Mul(D(1,9,2),Root(D(2)),P(Constant)));
    private static Formula Linear(Formula t) => Call("L",t);
    private static Formula Old(Formula t) => Call("O",t);
    private static Formula Denominator(Formula t) => Sub(Root(D(2)),Mul(D(2),P(Constant),Eps(t)));
    private static Formula Interval(Formula t) => And(Less(D(0),Abs(t)),Less(Abs(t),Endpoint));
    private static DocumentBlock Theorem(string name, string heading, Formula formula, string prose) =>
        Describe.Lean(DescribeId.Create(name.Replace('_','-')),
            DeclarationHandle.Create("D5/S3/Quantum/Algebra/PauliFixedProductLinear." + name),
            H(heading), StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);
    public DocumentDefinition Create()
    {
        var t=V("t"); var a=V("a");
        var blocks=Notation().Concat(new DocumentBlock[] {
            Paragraph(Text("All definitions above are the actual fixed-product family, reproduced here so that the existential realization statement is closed and complete. Cstar is PauliLinearCertificate.constant = 1+2sqrt(2). epsilon(t) is epsilon t, d(t) is localBound t, eta is smallEndpoint. L(t) means PauliLinearCertificate.linear (epsilon t) (localBound t); O(t) means PauliLinearCertificate.old at those same arguments. q(t) below is its original quadratic root; O retains the independent local cap. The computed report yields epsilon(t)=12sqrt(2)|t|, rather than a selected-block readout.")),
            Display(And(Eql(Call("Cstar"),Constant),Eql(Call("eta"),Endpoint),
                All("t",R,And(Eql(Eps(t),Root(Report(t))),Eql(Call("d",t),LocalBound(t)),
                    Eql(Linear(t),Fr(Mul(D(2),P(Constant),LocalBound(t),Eps(t)),Denominator(t))),
                    Eql(Call("q",t),Fr(Add(Mul(P(Constant),Eps(t)),Root(Add(Mul(Pow(Constant),Pow(Eps(t))),
                        Mul(D(4),P(Constant),LocalBound(t),Eps(t))))),D(2))),
                    Eql(Old(t),Call("min",LocalBound(t),Call("q",t))))))),
            Theorem("small_interval_nonempty", "The literal interval contains a nonzero real parameter",
                Some("t",R,Interval(t)),
                "The endpoint is positive, and half of it is an explicit positive member. The ambient family still includes the zero parameter."),
            Theorem("actual_strict_improvement", "The actual defect lies below both the original root and cap",
                All("t",R,Imp(Interval(t),And(
                    Less(D(0),Denominator(t)),DiagonalActive(t),UnitActive(t),
                    All("a",J,Imp(Unit(a),Leq(Norm(Action(t,a,a)),Linear(t)))),
                    Leq(Fr(Abs(t),D(2)),Linear(t)),Less(Linear(t),Old(t))))),
                "The six conjuncts include denominator positivity, both activity statements and domination for every unit vector. Since O(t) is the displayed minimum, strict inequality means strict improvement below both d(t) and q(t). The complete report gives epsilon in (0,1/(16 Cstar)); the literal interval also gives |t|<1 and hence 1<=d(t)<=sqrt(2). With x=Cstar epsilon, the linear certificate is at most 4x, strictly below sqrt(x), at most the quadratic root, and strictly below one and thus the cap. The exact attained diagonal defect gives domination. This proves the family-specific comparison; the general stability theorem for arbitrary products and actions is not asserted."),
            Theorem("nonempty_improvement", "One actual parameter realizes all data and strict improvement together",
                Some("t",R,And(FamilyContract(t),Defects(t),Constants(t),ActionData(t),LabelData(t),SupportGap(t),
                    Less(D(0),Abs(t)),Less(Abs(t),Endpoint),DiagonalActive(t),UnitActive(t),
                    Leq(Fr(Abs(t),D(2)),Linear(t)),Less(Linear(t),Old(t)))),
                "The full six Family proposition bodies are displayed in this same-t existential conjunction, followed by the six interval, activity and comparison clauses. This particular declaration does not output denominator positivity or all-unit domination as additional conjuncts; those are outputs of actual_strict_improvement. The source realization, exact constants, both Gram operators, both kernels, spectra, support, uniform gap and zero-boundary data all belong to the same fixed-product family. No physical acquisition or general noisy-reconstruction conclusion is supplied.")
        }).ToArray();
        return DocumentDefinition.Create(ScribeNode.Create(
            "The complete actual Pauli report gives strict improvement on the literal nonempty real interval.",
            H("A strict certificate for the same fixed-product Pauli realization"), Blocks(blocks)));
    }
}
