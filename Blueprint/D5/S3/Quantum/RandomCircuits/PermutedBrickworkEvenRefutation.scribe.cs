using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.RandomCircuits;

internal sealed class PermutedBrickworkEvenRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/RandomCircuits/PermutedBrickworkEvenRefutation.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/QuantumStates/belkinallenclark2025secondmoments");
    private static DocumentBlock Node(string id,string title,Formula formula,string prose,string declaration,DescribeRole role) =>
        Describe.Lean(DescribeId.Create("pbeven-"+id),DeclarationHandle.Create(Prefix+declaration),H(title),StatementSource.FromAuthor(Disp(formula)),
            declaration is "restrictReplica" or "physicalWitness" or "claim" or "result" ? AssessedProvenance.FromRepo(Source) : AssessedProvenance.FromLiterature(Source),Blocks(Paragraph(DefinitionDsl.Text(prose))),role);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For four sites, every local dimension q at least two and every even depth at least two give a permuted-brickwork Haar moment with a strictly negative quadratic form.",
        H("Even-depth permuted brickwork fails positive semidefiniteness"),
        Blocks(
            Node("matching","The three complete matchings",Matching(),"Section 5.2 (page 12): \"Suppose we draw a random two-sided matching of the sites, then apply a layer of Haar-random 2-site gates to those pairs in parallel.\" The source sites are numbered 0,1,2,3 here. Matching indices 0,1,2 denote A,B,C, respectively.","matching",DescribeRole.Definition),
            Node("restriction","Restricting the replicas to one edge",Restriction(),"Each of the four replicas is restricted to the two endpoints in their displayed order. Their order remains barred one, barred two, unbarred one, unbarred two.","restrictReplica",DescribeRole.Definition),
            Node("layer","A layer of independent Haar gates",Layer(),"The two disjoint pairs in a matching receive independent normalized Haar gates on Matrix.unitaryGroup (Fin q times Fin q) over the complex numbers. The matrix entry is the product of their literal four-factor expectations.","layerMoment",DescribeRole.Definition),
            Node("word","A circuit word",Word(),"The circuit product is U_(d-1) ... U_0. The layer-moment matrices therefore multiply in reverse index order, as in the actual circuit.","wordMoment",DescribeRole.Definition),
            Node("norepeat","The connected-block condition on four sites",NoRepeatFormula(),"Section 5.2 (page 12): \"Suppose we draw layers as in the parallel complete-graph architecture, except that we require each adjacent pair of layers to form a connected block.\" On four sites, two equal matchings have two connected components, while any two distinct matchings have a four-cycle as their union. Thus connected union is exactly the condition that adjacent matching indices differ. The Fin.mk arguments retain the bounds supplied by i+1 < d.","NoRepeat",DescribeRole.Definition),
            Node("words","The admissible words",Words(),"All matching words of length d are filtered by the connected-block condition. For positive depth their number is 3 times 2 to the power d-1.","admissibleWords",DescribeRole.Definition),
            Node("moment","The uniform circuit expectation",Moment(),"Section 2.1 (page 3) gives vec(Phi_epsilon) = E[U* tensor U* tensor U tensor U]. Here the expectation is the uniform average of the circuit-ordered layer-moment products over all admissible matching words; independent gates have already been integrated inside each layer. The reciprocal cardinality is taken in the complex numbers.","vecPhi",DescribeRole.Definition),
            Node("permutation","Four-site permutation vectors",Permutation(),"The four-site physical vector is the tensor product of the normalized one-site identity or swap vectors. No orthonormal coefficient basis is substituted for these physical vectors.","permutationVector",DescribeRole.Definition),
            Node("vector","The antisymmetric physical vector",Witness(),"The vector is (|01>-|10>) on sites 0,1 tensored with (|01>-|10>) on sites 2,3, expressed in the nonorthogonal physical identity/swap vectors. Its squared norm is 4(1-q^(-2)) squared, which is positive for q at least two.","physicalWitness",DescribeRole.Definition),
            Node("claim","The even-depth question",Eqn(F.Id("claim"),Claim()),"Section 5.2 (page 12): \"Like the brickwork, this architecture can be shown to have a PSD vectorization if the depth is odd. It is unclear if the vectorization is PSD at even depths.\" The displayed claim is the negative answer on four sites: all q at least two and all even d at least two fail Matrix.PosSemidef.","claim",DescribeRole.Definition),
            Node("result","Failure at every even depth",Claim(),"Put a=q/(q squared + 1) and h=(q to the fourth + 1)/(q squared + 1) squared. The sum of the three layer projections has eigenvalue h on the physical vector. The unnormalized no-repeat word sum R obeys R_(d+1)=(S-I)R_d, while the word count is 3 times 2 to the power d-1. The average therefore has eigenvalue (h/3)(-a squared) to the power d-1 on this vector. Multiplying by its strictly positive squared norm gives a negative real quadratic form at every even depth. At q=2,d=2 this form is -51/625. A positive semidefinite matrix must have nonnegative quadratic forms, giving the contradiction.","result",DescribeRole.Theorem)
        ),[]));
    private static Formula Dp => F.Id("d");
    private static Formula M => F.Id("m");
    private static Formula W => F.Id("w");
    private static Formula Sites() => Fn(Fin(D(4)),Fin(Q));
    private static Formula Physical() => Replica(Sites());
    private static Formula Matching() => All("m",Fin(D(3)),Eqn(Call("matching",M),Call("ite",Eqn(M,D(0)),Array(Pair(D(0),D(1)),Pair(D(2),D(3))),Call("ite",Eqn(M,D(1)),Array(Pair(D(0),D(2)),Pair(D(1),D(3))),Array(Pair(D(0),D(3)),Pair(D(1),D(2)))))));
    private static Formula EdgeSlice(byte half,byte replica) => Pair(At(Proj(Proj(R,half),replica),Proj(F.Id("p"),1)),At(Proj(Proj(R,half),replica),Proj(F.Id("p"),2)));
    private static Formula Restriction() => All("q",Nat(),All("p",Product(Fin(D(4)),Fin(D(4))),All("r",Physical(),Eqn(Call("restrictReplica",F.Id("p"),R),Pair(Pair(EdgeSlice(1,1),EdgeSlice(1,2)),Pair(EdgeSlice(2,1),EdgeSlice(2,2)))))));
    private static Formula Layer()
    {
        Formula e=F.Id("e"),edge=At(Call("matching",M),e);
        Formula row=Call("restrictReplica",edge,R),col=Call("restrictReplica",edge,C);
        return All("q",Nat(),All("m",Fin(D(3)),All("r",Physical(),All("c",Physical(),Eqn(At(Call("layerMoment",Q,M),R,C),ProdOver("e",Fin(D(2)),At(Gate(Q),row,col)))))));
    }
    private static Formula Word()
    {
        Formula indices=QCall("List","reverse",QCall("List","finRange",Dp));
        Formula layers=QCall("List","map",Lam("i",Fin(Dp),Call("layerMoment",Q,At(W,F.Id("i")))),indices);
        return All("q",Nat(),All("d",Nat(),All("w",Fn(Fin(Dp),Fin(D(3))),Eqn(Call("wordMoment",Q,Dp,W),QCall("List","prod",layers)))));
    }
    private static Formula NoRepeatFormula()
    {
        Formula i=F.Id("i"),next=Add(i,D(1));
        Formula first=QCall("Fin","mk",i,new Formula.Placeholder());
        Formula second=QCall("Fin","mk",next,new Formula.Placeholder());
        Formula condition=All("i",Nat(),Implies(Lt(next,Dp),Ne(At(W,first),At(W,second))));
        return All("d",Nat(),All("w",Fn(Fin(Dp),Fin(D(3))),Eqn(Call("NoRepeat",Dp,W),condition)));
    }
    private static Formula Words() => All("d",Nat(),Eqn(Call("admissibleWords",Dp),QCall("Finset","filter",Call("NoRepeat",Dp),Cast(Qualified("Finset","univ"),Call("Finset",Fn(Fin(Dp),Fin(D(3))))))));
    private static Formula Moment()
    {
        Formula words=Call("admissibleWords",Dp);
        Formula sum=Seq(Sum,Underscore,Grp(W,Sp,InMacro,Sp,words),Sp,Call("wordMoment",Q,Dp,W));
        return All("q",Nat(),All("d",Nat(),Eqn(Call("vecPhi",Q,Dp),Smul(Inv(Cast(QCall("Finset","card",words),Complex())),sum))));
    }
    private static Formula Permutation()
    {
        Formula s=F.Id("s"),b=At(B,s);
        Formula r=Pair(Pair(At(Proj(Proj(R,1),1),s),At(Proj(Proj(R,1),2),s)),Pair(At(Proj(Proj(R,2),1),s),At(Proj(Proj(R,2),2),s)));
        return All("q",Nat(),All("b",Fn(Fin(D(4)),Fin(D(2))),All("r",Physical(),Eqn(At(Call("permutationVector",Q,B),R),ProdOver("s",Fin(D(4)),Perm(Q,b,r))))));
    }
    private static Formula Witness()
    {
        Formula v1=Call("permutationVector",Q,Array(D(0),D(1),D(0),D(1)));
        Formula v2=Call("permutationVector",Q,Array(D(0),D(1),D(1),D(0)));
        Formula v3=Call("permutationVector",Q,Array(D(1),D(0),D(0),D(1)));
        Formula v4=Call("permutationVector",Q,Array(D(1),D(0),D(1),D(0)));
        return All("q",Nat(),Eqn(Call("physicalWitness",Q),Add(Sub(Sub(v1,v2),v3),v4)));
    }
    private static Formula Claim() => All("q",Nat(),Implies(Leq(D(2),Q),All("d",Nat(),Implies(Leq(D(2),Dp),Implies(Call("Even",Dp),new Formula.Not(QCall("Matrix","PosSemidef",Call("vecPhi",Q,Dp))))))));

    private static Formula Nat() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Complex() => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula Fin(Formula n) => Call("Fin", n);
    private static Formula Product(Formula x, Formula y) => Parenthesized(Seq(x, Sp, Times, Sp, y));
    private static Formula Replica(Formula n) => Product(Product(n,n),Product(n,n));
    private static Formula Fn(Formula x, Formula y) => Parenthesized(new Formula.TypeArrow(x,y));
    private static Formula At(Formula f, params Formula[] a) => new Formula.Apply(f,[.. a]);
    private static Formula Qualified(string owner, string name) => Seq(Operatorname,Grp(F.Id(owner),Dot,F.Id(name)));
    private static Formula QCall(string owner,string name,params Formula[] a) => At(Qualified(owner,name),a);
    private static Formula Parenthesized(Formula x) => Seq(Open,x,Close);
    private static Formula Pair(Formula x,Formula y) => Parenthesized(Seq(x,Comma,Sp,y));
    private static Formula All(string x,Formula type,Formula body) => new Formula.Bind(FormulaQuantifier.ForAll,FormulaIdentifier.Create(x),type,body);
    private static Formula Lam(string x,Formula type,Formula body) => Seq(LambdaLower,Sp,F.Id(x),Colon,Sp,type,Comma,Sp,body);
    private static Formula Implies(Formula p,Formula q) => new Formula.Logic(Parenthesized(p),FormulaLogicOperator.Implies,Parenthesized(q));
    private static Formula Eqn(Formula x,Formula y) => new Formula.Relation(x,FormulaRelationOperator.Equal,y);
    private static Formula Ne(Formula x,Formula y) => new Formula.Relation(x,FormulaRelationOperator.NotEqual,y);
    private static Formula Lt(Formula x,Formula y) => new Formula.Relation(x,FormulaRelationOperator.LessThan,y);
    private static Formula Leq(Formula x,Formula y) => new Formula.Relation(x,FormulaRelationOperator.LessThanOrEqual,y);
    private static Formula Sub(Formula x,Formula y) => new Formula.Binary(x,FormulaBinaryOperator.Subtract,y);
    private static Formula Proj(Formula x,byte i) => Seq(x,Dot,D(i));
    private static Formula Inv(Formula x) => new Formula.Power(Parenthesized(x),new Formula.Negate(D(1)));
    private static Formula Smul(Formula x,Formula y) => Seq(Parenthesized(x),Sp,Cdot,Sp,Parenthesized(y));
    private static Formula Cast(Formula x,Formula type) => Parenthesized(Seq(x,Colon,Sp,type));
    private static Formula Array(params Formula[] a)
    {
        Formula body=a[0];
        for(var i=1;i<a.Length;i++) body=Seq(body,Comma,Sp,a[i]);
        return Seq(Bang,OpenBracket,body,CloseBracket);
    }
    private static Formula Q => F.Id("q");
    private static Formula B => F.Id("b");
    private static Formula R => F.Id("r");
    private static Formula C => F.Id("c");
    private static Formula Perm(Formula q,Formula b,Formula r) => Call("sitePermutation",q,b,r);
    private static Formula Gate(Formula q) => Call("haarAverage",Product(Fin(q),Fin(q)));
    private static Formula ProdOver(string x,Formula type,Formula body) => Seq(Prod,Underscore,Grp(F.Id(x),Colon,Sp,type),Sp,Parenthesized(body));
}
