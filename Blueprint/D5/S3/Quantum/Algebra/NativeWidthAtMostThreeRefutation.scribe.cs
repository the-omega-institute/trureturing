using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Algebra;

internal sealed class NativeWidthAtMostThreeRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Algebra/NativeWidthAtMostThreeRefutation.";
    private static Formula V(string name) => F.Id(name);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(name))), [.. args]);
    private static Formula App(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula Par(Formula x) => Seq(Open, x, Close);
    private static Formula All(string n, Formula t, Formula b) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(n), t, b);
    private static Formula Ex(string n, Formula t, Formula b) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(n), t, b);
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(Par(a), FormulaLogicOperator.And, Par(b));
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(Par(a), FormulaLogicOperator.Implies, Par(b));
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Smul(Formula a, Formula b) => Call("smul", a, b);
    private static Formula Fin(Formula a) => Call("Fin", a);
    private static Formula Mat(Formula a, Formula b) => Call("Matrix", Fin(a), Fin(b), V("Complex"));
    private static Formula Family(Formula k, Formula a, Formula b) => new Formula.TypeArrow(Fin(k), Mat(a, b));
    private static Formula Identity(Formula a, Formula b) => Call("identity", Call("prod", Fin(a), Fin(b)));
    private static Formula Star(Formula a) => Call("conjTranspose", a);
    private static Formula Sum(Formula k) => Seq(new Formula.Subscript(F.Sum,
        Seq(V("r"), Sp, Colon, Sp, Fin(k))), Sp,
        Par(Call("kronecker", App(V("M"), V("r")), App(V("N"), V("r")))));
    private static DocumentBlock Node(string id, string title, Formula formula, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(id.Replace("_", "-")), DeclarationHandle.Create(Prefix + id), H(title),
            StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The original universal inner-cone event is false: unrestricted native width-three factors cannot have a positive scalar column Gram at dimensions (3,5,3,5).",
        H("The original inner-cone flat-spectrum event is false"),
        Blocks(
            Node("claim", "The complete original universal event", ClaimFormula(),
                "All four dimensions are natural numbers. The eight premises are 0<a, a<=b, 0<c, c<=d, a*a+b*b<=3*a*b, c*c+d*d<=3*c*d, b<=2*a and d<=2*c. The existential M and N are unrestricted complex triples of a-by-b and d-by-c matrices. One real lambda>0 and the same M,N witness both implications. F=QuantumMaxFlowBound.flow M N has native rows Fin a times Fin d and columns Fin b times Fin c. At equality of a*d and b*c, both column and row Gram identities are required with that same lambda. No independence, normalization, coefficient-kernel, plane or classification premise is present.", DescribeRole.Definition),
            Node("positive_scalar_obstruction", "Unrestricted native positive-scalar obstruction", ScalarFormula(),
                "For arbitrary M:Fin 3->Matrix(Fin 3)(Fin 5) Complex and N:Fin 3->Matrix(Fin 5)(Fin 3) Complex, and every real lambda>0, the native column Gram cannot equal lambda times I on Fin 5 times Fin 3. Choose a least-width decomposition of the original Kronecker sum. If either family is dependent, select a nonzero relation coefficient and delete that index using Fin.succAbove, absorbing its right or left factor into the other factors; the sum is unchanged. Minimality therefore supplies independent families A,D of width k<=3, including k=0. Multiply A by c=((sqrt lambda) inverse:Real):Complex. The compiled scalar identity star(c)*c*lambda=1 gives an identity Gram without changing either native product carrier. Scaling by nonzero c preserves independence. This is a derived reduction, not a new hypothesis.", DescribeRole.Theorem),
            Node("native_three_refutation", "The simultaneous complex-plane consumer", NativeFormula(),
                "For independent native triples the Gram identity is impossible. Define H_rs=(1/3)*trace(N(r)* N(s)), where the star denotes conjugate transpose. Flattening N proves H positive definite. Its invertible factorization H=B*B gives M'=BM and N'=B inverse transpose N. The coefficient contraction B transpose times B inverse transpose equals I, so the Kronecker sum is preserved. Partial trace of the original Gram identity derives sum_r M'(r)* M'(r)=I_5. Independence of M is preserved. The coefficient-first stack S is therefore injective. Apply CommonCoefficientPlane.common_plane to this actual M', obtaining one complex two-dimensional plane neutral for every Hermitian coefficient-kernel form. For every physical column pair l,m, expansion of the Gram identity places T_lm(r,s)=(N'(r)* N'(s))_lm-delta_rs delta_lm in the complex compression kernel. Compression commutes with conjugate transpose, so the Hermitian real and imaginary parts both lie in that kernel. The same plane annihilates their full pairings, hence also T_lm, including off-diagonal l,m and the zero-kernel case. Transport the plane by WithLp to EuclideanSpace and choose an orthonormal basis V with V*V=I_2. Set W_j,(r,l)=N'(r)_j,l, P=W*W and C=V tensor I_3. The neutral block equations prove C*PC=I_6. Rank inequalities yield 6<=rank(W)<=5.", DescribeRole.Theorem),
            Node("result", "Literal refutation of the original event", new Formula.Not(V("claim")),
                "Apply the original universal claim at (a,b,c,d)=(3,5,3,5). Both quadratic premises read 34<=45 and both ratio premises read 5<=6; all eight premises hold. Both products are 15, so both original implications apply to the same witnesses and scalar. The column implication alone contradicts positive_scalar_obstruction. All reduced widths are discharged: k=0 gives zero Gram versus identity; k=1 has a nonzero native tensor-kernel vector because a 3-by-5 map is not injective; k=2 is whitened and its 6-by-5 injective stack has trivial coefficient compression kernel, forcing N'(r)*N'(s)=delta_rs I_3. Its concatenation would then have six orthonormal columns in five rows. The rank-Kronecker helper used for k=2 has a genuinely arbitrary coefficient width; the Fin 3-only supplier is not applied to Fin 2. The k=3 contradiction is the simultaneous complex-plane argument above. This proves the stated universal event false. No optimal threshold, minimal counterexample or physical realization is asserted.", DescribeRole.Theorem))));

    private static Formula ClaimFormula()
    {
        Formula a=V("a"), b=V("b"), c=V("c"), d=V("d"), lambda=V("lambda");
        Formula flow=Call("flow", V("M"), V("N"));
        Formula body=Ex("M", Family(D(3), a,b), Ex("N", Family(D(3),d,c), Ex("lambda", V("Real"),
            And(Lt(D(0),lambda), And(
                Imp(Le(Mul(b,c),Mul(a,d)), Eq(Mul(Star(flow),flow),Smul(Call("ofReal",lambda),Identity(b,c)))),
                Imp(Le(Mul(a,d),Mul(b,c)), Eq(Mul(flow,Star(flow)),Smul(Call("ofReal",lambda),Identity(a,d)))))))));
        Formula[] premises=[Lt(D(0),a),Le(a,b),Lt(D(0),c),Le(c,d),
            Le(Add(Mul(a,a),Mul(b,b)),Mul(Mul(D(3),a),b)),
            Le(Add(Mul(c,c),Mul(d,d)),Mul(Mul(D(3),c),d)),Le(b,Mul(D(2),a)),Le(d,Mul(D(2),c))];
        for(int i=premises.Length-1;i>=0;i--) body=Imp(premises[i],body);
        return Eq(V("claim"),All("a",V("Nat"),All("b",V("Nat"),All("c",V("Nat"),All("d",V("Nat"),body)))));
    }
    private static Formula ScalarFormula()
    {
        Formula f=Sum(D(3));
        Formula ne=new Formula.Relation(Mul(Star(f),f),FormulaRelationOperator.NotEqual,
            Smul(Call("ofReal",V("lambda")),Identity(D(5),D(3))));
        return All("M",Family(D(3),D(3),D(5)),All("N",Family(D(3),D(5),D(3)),
            All("lambda",V("Real"),Imp(Lt(D(0),V("lambda")),ne))));
    }
    private static Formula NativeFormula()
    {
        Formula f=Sum(D(3));
        Formula ne=new Formula.Relation(Mul(Star(f),f),FormulaRelationOperator.NotEqual,Identity(D(5),D(3)));
        return All("M",Family(D(3),D(3),D(5)),All("N",Family(D(3),D(5),D(3)),
            Imp(Call("LinearIndependent",V("Complex"),V("M")),
                Imp(Call("LinearIndependent",V("Complex"),V("N")),ne))));
    }
}
