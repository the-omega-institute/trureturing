using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.RandomCircuits;

internal sealed class HaarTwoCopyTwirlDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/RandomCircuits/HaarTwoCopyTwirl.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/QuantumStates/belkinallenclark2025secondmoments");
    private static DocumentBlock Node(string id,string title,Formula formula,string prose,string declaration,DescribeRole role) =>
        Describe.Lean(DescribeId.Create("haar-"+id),DeclarationHandle.Create(Prefix+declaration),H(title),StatementSource.FromAuthor(Disp(formula)),
            AssessedProvenance.FromLiterature(Source),Blocks(Paragraph(DefinitionDsl.Text(prose))),role);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The normalized two-copy Haar average is Hermitian and idempotent. Its action on two-site identity/swap vectors has coefficient q/(q squared + 1).",
        H("The two-copy Haar moment and its local rule"),
        Blocks(
            Node("compact","Compact unitary matrices",Generic(Call("CompactSpace",Unit(F.Id("n")))),"The unitary group is closed, and every matrix entry has norm at most one, so the finite-dimensional group is compact.","unitaryCompactSpace",DescribeRole.Definition),
            Node("measurable","The Borel measurable structure",Generic(Eqn(Call("unitaryMeasurableSpace",F.Id("n")),Call("borel",Unit(F.Id("n"))))),"The measurable sets are the Borel sets of the topology on unitary matrices.","unitaryMeasurableSpace",DescribeRole.Definition),
            Node("borel","Compatibility with the topology",Generic(Call("BorelSpace",Unit(F.Id("n")))),"The measurable structure is the Borel structure by definition.","unitaryBorelSpace",DescribeRole.Definition),
            Node("probability","Normalized Haar law",Generic(Call("IsProbabilityMeasure",Haar(F.Id("n")))),"The compact Haar construction is normalized on the whole group. The top element of PositiveCompacts is the whole compact unitary group.","haar_probability",DescribeRole.Definition),
            Node("literal","The literal four-replica action",Literal(),"Section 2.1 (page 3) writes vec(Phi_epsilon) = E[U* tensor U* tensor U tensor U]. Here Matrix.map star is entrywise conjugation. The factors are barred replica one, barred replica two, unbarred replica one, unbarred replica two; Matrix.vec stacks columns first.","literalMoment",DescribeRole.Definition),
            Node("average","The Haar expectation",Average(),"The expectation is the entrywise Bochner integral of the literal four-factor action under normalized Haar law, not a projection substituted into the definition.","haarAverage",DescribeRole.Definition),
            Node("site","One-site permutation vectors",Site(),"The normalized identity vector pairs barred replica one with unbarred replica one, and likewise for replica two. The swap vector crosses those pairings. Their norm is one for positive local dimension.","sitePermutation",DescribeRole.Definition),
            Node("local","Two-site permutation vectors",LocalFormula(),"On the two sites of a gate the one-site identity or swap vector is chosen independently on each site. The matrix indices retain the original four-replica order.","localPermutation",DescribeRole.Definition),
            Node("hermitian","Haar averaging is Hermitian",Generic(QCall("Matrix","IsHermitian",Call("haarAverage",F.Id("n")))),"Inversion preserves normalized Haar law, and the four-factor action of the inverse is the conjugate transpose of the original action.","haarAverage_hermitian",DescribeRole.Theorem),
            Node("idempotent","Haar averaging is idempotent",Generic(Eqn(Mul(Call("haarAverage",F.Id("n")),Call("haarAverage",F.Id("n"))),Call("haarAverage",F.Id("n")))),"Left invariance fixes the averaged action under every unitary action, hence a second Haar average leaves it fixed.","haarAverage_idempotent",DescribeRole.Theorem),
            Node("gram","The physical two-site Gram matrix",Gram(),"The one-site overlap of equal identity/swap choices is one; distinct choices have overlap 1/q. The two-site overlap is the product of the two one-site overlaps.","localPermutation_gram",DescribeRole.Theorem),
            Node("identity","The identity vector is fixed",Fixed(D(0)),"The identity commutes with the two-copy unitary action, so the Haar expectation fixes it.","local_identity_fixed",DescribeRole.Theorem),
            Node("swap","The swap vector is fixed",Fixed(D(1)),"The replica swap commutes with the two-copy unitary action, so the Haar expectation fixes it.","local_swap_fixed",DescribeRole.Theorem),
            Node("mixed","The exact mixed local rule",Mixed(),"Quarter phases force the two-copy commutant to have only identity and swap support. Permutations make its coefficients uniform; a two-coordinate Hadamard forces the remaining diagonal coefficient to be their sum. Haar invariance puts the image in this span. Hermitian pairing with the two fixed vectors then yields q/(q squared + 1) for each mixed input.","gate_mixed_rule",DescribeRole.Theorem)
        ),[]));
    private static Formula Literal()
    {
        Formula n=F.Id("n"),u=F.Id("U");
        Formula barred=QCall("Matrix","map",u,F.Id("star"));
        return All("n",F.Id("Type"),All("U",MatrixOf(n),Eqn(Call("literalMoment",u),Kron(Kron(barred,barred),Kron(u,u)))));
    }
    private static Formula Average()
    {
        Formula n=F.Id("n"),u=F.Id("U");
        Formula integral=Seq(Int,Sp,Parenthesized(At(Call("literalMoment",Call("val",u)),R,C)),Sp,F.Id("d"),Parenthesized(Haar(n)),Parenthesized(u));
        return Generic(All("r",Replica(n),All("c",Replica(n),Eqn(At(Call("haarAverage",n),R,C),Seq(Int,Underscore,Grp(u,Colon,Sp,Unit(n)),Sp,Parenthesized(At(Call("literalMoment",Call("val",u)),R,C)),Sp,F.Id("d"),Parenthesized(Haar(n)))))));
    }
    private static Formula Site()
    {
        Formula qcomplex=Cast(Q,Complex());
        Formula direct=And(Eqn(Proj(Proj(R,1),1),Proj(Proj(R,2),1)),Eqn(Proj(Proj(R,1),2),Proj(Proj(R,2),2)));
        Formula crossed=And(Eqn(Proj(Proj(R,1),1),Proj(Proj(R,2),2)),Eqn(Proj(Proj(R,1),2),Proj(Proj(R,2),1)));
        return All("q",Nat(),All("b",Fin(D(2)),All("r",Replica(Fin(Q)),Eqn(Perm(Q,B,R),Call("ite",Eqn(B,D(0)),Call("ite",direct,Inv(qcomplex),D(0)),Call("ite",crossed,Inv(qcomplex),D(0)))))));
    }
    private static Formula SiteSlice(byte site) => Pair(Pair(Proj(Proj(Proj(R,1),1),site),Proj(Proj(Proj(R,1),2),site)),Pair(Proj(Proj(Proj(R,2),1),site),Proj(Proj(Proj(R,2),2),site)));
    private static Formula LocalFormula() => All("q",Nat(),All("b",Product(Fin(D(2)),Fin(D(2))),All("r",Replica(Product(Fin(Q),Fin(Q))),Eqn(At(Local(Q,B),R),Mul(Perm(Q,Proj(B,1),SiteSlice(1)),Perm(Q,Proj(B,2),SiteSlice(2)))))));
    private static Formula Gram()
    {
        Formula o1=Call("ite",Eqn(Proj(B,1),Proj(C,1)),D(1),Inv(Cast(Q,Complex())));
        Formula o2=Call("ite",Eqn(Proj(B,2),Proj(C,2)),D(1),Inv(Cast(Q,Complex())));
        return All("q",Nat(),Implies(Lt(D(0),Q),All("b",Product(Fin(D(2)),Fin(D(2))),All("c",Product(Fin(D(2)),Fin(D(2))),Eqn(DotProduct(Star(Local(Q,B)),Local(Q,C)),Mul(o1,o2))))));
    }
    private static Formula Fixed(Formula bit) => All("q",Nat(),Eqn(MulVec(Gate(Q),Local(Q,Pair(bit,bit))),Local(Q,Pair(bit,bit))));
    private static Formula Mixed()
    {
        Formula a=new Formula.Fraction(Cast(Q,Complex()),Add(new Formula.Power(Cast(Q,Complex()),D(2)),D(1)));
        return All("q",Nat(),Implies(Leq(D(2),Q),All("b",Product(Fin(D(2)),Fin(D(2))),Implies(Ne(Proj(B,1),Proj(B,2)),Eqn(MulVec(Gate(Q),Local(Q,B)),Smul(a,Add(Local(Q,Pair(D(0),D(0))),Local(Q,Pair(D(1),D(1))))))))));
    }

    private static Formula Nat() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Complex() => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula Fin(Formula n) => Call("Fin", n);
    private static Formula Product(Formula x, Formula y) => Parenthesized(Seq(x, Sp, Times, Sp, y));
    private static Formula Replica(Formula n) => Product(Product(n,n),Product(n,n));
    private static Formula MatrixOf(Formula n) => Call("Matrix",n,n,Complex());
    private static Formula At(Formula f, params Formula[] a) => new Formula.Apply(f,[.. a]);
    private static Formula Qualified(string owner, string name) => Seq(Operatorname,Grp(F.Id(owner),Dot,F.Id(name)));
    private static Formula QCall(string owner,string name,params Formula[] a) => At(Qualified(owner,name),a);
    private static Formula Parenthesized(Formula x) => Seq(Open,x,Close);
    private static Formula Pair(Formula x,Formula y) => Parenthesized(Seq(x,Comma,Sp,y));
    private static Formula All(string x,Formula type,Formula body) => new Formula.Bind(FormulaQuantifier.ForAll,FormulaIdentifier.Create(x),type,body);
    private static Formula Implies(Formula p,Formula q) => new Formula.Logic(Parenthesized(p),FormulaLogicOperator.Implies,Parenthesized(q));
    private static Formula And(Formula p,Formula q) => new Formula.Logic(Parenthesized(p),FormulaLogicOperator.And,Parenthesized(q));
    private static Formula Eqn(Formula x,Formula y) => new Formula.Relation(x,FormulaRelationOperator.Equal,y);
    private static Formula Ne(Formula x,Formula y) => new Formula.Relation(x,FormulaRelationOperator.NotEqual,y);
    private static Formula Lt(Formula x,Formula y) => new Formula.Relation(x,FormulaRelationOperator.LessThan,y);
    private static Formula Leq(Formula x,Formula y) => new Formula.Relation(x,FormulaRelationOperator.LessThanOrEqual,y);
    private static Formula Mul(Formula x,Formula y) => new Formula.Binary(x,FormulaBinaryOperator.Multiply,y);
    private static Formula Proj(Formula x,byte i) => Seq(x,Dot,D(i));
    private static Formula Inv(Formula x) => new Formula.Power(Parenthesized(x),new Formula.Negate(D(1)));
    private static Formula Smul(Formula x,Formula y) => Seq(Parenthesized(x),Sp,Cdot,Sp,Parenthesized(y));
    private static Formula Cast(Formula x,Formula type) => Parenthesized(Seq(x,Colon,Sp,type));
    private static Formula Q => F.Id("q");
    private static Formula B => F.Id("b");
    private static Formula R => F.Id("r");
    private static Formula C => F.Id("c");
    private static Formula Unit(Formula n) => QCall("Matrix","unitaryGroup",n,Complex());
    private static Formula Haar(Formula n) => QCall("Measure","haarMeasure",Cast(Qualified("Top","top"),QCall("TopologicalSpace","PositiveCompacts",Unit(n))));
    private static Formula Kron(Formula x,Formula y) => QCall("Matrix","kronecker",x,y);
    private static Formula MulVec(Formula x,Formula y) => QCall("Matrix","mulVec",x,y);
    private static Formula DotProduct(Formula x,Formula y) => Call("dotProduct",x,y);
    private static Formula Star(Formula x) => Call("star",x);
    private static Formula Perm(Formula q,Formula b,Formula r) => Call("sitePermutation",q,b,r);
    private static Formula Local(Formula q,Formula b) => Call("localPermutation",q,b);
    private static Formula Gate(Formula q) => Call("haarAverage",Product(Fin(q),Fin(q)));
    private static Formula Generic(Formula body) => All("n",F.Id("Type"),Seq(OpenBracket,Call("Fintype",F.Id("n")),CloseBracket,Sp,OpenBracket,Call("DecidableEq",F.Id("n")),CloseBracket,Sp,body));
}
