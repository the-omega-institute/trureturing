using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Divisors.ErdosNicolas;

internal sealed class ErdosNicolasChainBoundDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Divisors/ErdosNicolas/ChainBound.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuadraticForms/erdosnicolas1989functions");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Divisor chain averages", H("Divisor chain averages"), Blocks(
            Node("divisor_chain_average_coprime", "Local non-strict chain bounds", false, true,
                "The empty divisor set n=0 needs no multiplier or p-free restriction. For " +
                "nonzero n, q is either one or prime and p does not divide n. The unit q=1 " +
                "case follows pointwise from the pair test. For prime q dividing n, split " +
                "the divisors into q-power chains, each of length at least two. Pair tests " +
                "are required only when q*r belongs to n.divisors, and triple tests only when " +
                "q^2*r belongs to n.divisors. Every chain term is p-free, without primality " +
                "of p. Decomposing each chain length into twos and threes gives the bound. " +
                "Constant weights c attain equality, so uniform strictness is impossible."),
            Node("divisor_chain_average_lt", "Strict local chain bounds", true, false,
                "For nonzero n, let q be one or a prime divisor of n. With q=1 the pair test " +
                "gives a strict pointwise bound. For prime q, strict pair and triple tests " +
                "on complete blocks give strict chain sums. The divisor set is nonempty, " +
                "so summing remains strict. The nonzero condition is necessary: n=0 has " +
                "no divisors. Composite q can leave isolated divisors; q=n=4 permits a large " +
                "weight at 2 despite all the local block tests. Lengths two and three " +
                "both occur, and weights c-epsilon show that c is a sharp supremum."))));

    private static DocumentBlock Node(string name, string title, bool strict, bool coprime,
        string prose) => Describe.Lean(
        DescribeId.Create("erdosnicolas-chainbound-" + name.Replace('_', '-')),
        DeclarationHandle.Create(Prefix + name), H(title),
        StatementSource.FromAuthor(Disp(Statement(strict,coprime))),
        AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);
    private static Formula Statement(bool strict, bool coprime)
    {
        var p=F.Id("p"); var q=F.Id("q"); var n=F.Id("n"); var c=F.Id("c");
        var r=F.Id("r"); var d=F.Id("d");
        var qr=Mul(q,r); var qrr=Mul(new Formula.Power(q,D(2)),r);
        Formula Phi(Formula x) => Call("phi",x);
        Formula Check(Formula x, Formula y) => new Formula.Relation(x,
            strict ? FormulaRelationOperator.LessThan : FormulaRelationOperator.LessThanOrEqual,y);
        Formula Block(Formula endpoint, Formula bound) => All("r",Field("N"),
            Imp(coprime ? new Formula.Relation(endpoint,FormulaRelationOperator.MemberOf,
                Call("divisors",n)) : Divides(endpoint,n),
                coprime ? Imp(new Formula.Not(Divides(p,r)),bound) : bound));
        var pair=Block(qr,Check(Add(Phi(r),Phi(qr)),Mul(D(2),c)));
        var triple=Block(qrr,Check(Add(Add(Phi(r),Phi(qr)),Phi(qrr)),Mul(D(3),c)));
        var sum=Seq(Sum,Underscore,
            Grp(new Formula.Relation(d,FormulaRelationOperator.MemberOf,Call("divisors",n))),
            Phi(d));
        Formula body=Check(sum,Mul(c,Call("card",Call("divisors",n))));
        body=Imp(pair,Imp(triple,body));
        body=All("c",Field("Q"),body);
        body=All("phi",new Formula.TypeArrow(Field("N"),Field("Q")),body);
        Formula nonzero=new Formula.Relation(n,FormulaRelationOperator.NotEqual,D(0));
        if(coprime)
        {
            var free=new Formula.Not(Divides(p,n));
            body=Imp(strict ? free : Imp(nonzero,free),body);
        }
        else body=Imp(nonzero,body);
        var unitOrPrime=new Formula.Logic(
            new Formula.Relation(q,FormulaRelationOperator.Equal,D(1)),
            FormulaLogicOperator.Or,Call("Prime",q));
        body=Imp(coprime ? Imp(nonzero,unitOrPrime) : unitOrPrime,Imp(Divides(q,n),body));
        body=All("q",Field("N"),All("n",Field("N"),body));
        return coprime ? All("p",Field("N"),body) : body;
    }

    private static Formula Field(string name) => Seq(Mathbb,Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname,Grp(F.Id(name))),[.. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll,FormulaIdentifier.Create(name),type,body);
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(a,FormulaLogicOperator.Implies,b);
    private static Formula Divides(Formula a, Formula b) =>
        new Formula.Relation(a,FormulaRelationOperator.Divides,b);
    private static Formula Add(Formula a, Formula b) =>
        new Formula.Binary(a,FormulaBinaryOperator.Add,b);
    private static Formula Mul(Formula a, Formula b) =>
        new Formula.Binary(a,FormulaBinaryOperator.Multiply,b);
}
