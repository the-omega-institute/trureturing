using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.Blueprint.D5.S3.Quantum.Approximate.SolovayKitaevNotation;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Approximate;

internal sealed class ArbitraryAlphabetSolovayKitaevDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Approximate/ArbitraryAlphabetSolovayKitaev.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every finite inverse-closed dense alphabet in SU(2) approximates all targets by ordinary lists with a uniform polylogarithmic length bound.",
        H("Ordinary-word Solovay–Kitaev approximation"), Blocks(
            Paragraph(Text("Mat denotes complex 2 by 2 matrices, with the complex Euclidean L2 operator norm. Words(m) is List(Fin m), including m=0. SU(U) means U is unitary and det(U)=1. Evaluation is ordered: eval(Gamma,[]) is the identity and eval(Gamma,i::w)=Gamma(i)*eval(Gamma,w). Every length below is the actual length of that list.")),
            Entry("ordinary-word-evaluation", "evalGamma", "Ordered evaluation", Evaluation(),
                "The head letter multiplies the evaluation of the tail on the left. Appending lists multiplies their evaluations in the same order.", DescribeRole.Definition),
            Entry("inverse-word", "inverseWord", "A chosen inverse letter", InverseDefinition(),
                "inv(sigma,w)=map(sigma,reverse(w)). The inverse selector need only satisfy Gamma(sigma(i))=star(Gamma(i)); it need not be involutive and letters need not be distinct.", DescribeRole.Definition),
            Entry("successor-word", "successorWord", "The five-piece successor", SuccessorDefinition(),
                "The successor is the literal concatenation v ++ w ++ inv(v) ++ inv(w) ++ u. Its length is twice length(v), twice length(w), plus length(u). Its evaluation is the commutator of eval(v),eval(w), followed by eval(u).", DescribeRole.Definition),
            Entry("finite-word-net", "exists_finite_word_net", "A finite net made of actual words", FiniteNet(),
                "Compactness of the determinant-one closed subset of the unitary group and density give finitely many actual word values. Choose one list for each net point and take the maximum of their actual lengths. The compact unitary carrier is reused from HaarTwoCopyTwirl.unitaryCompactSpace. No numerical bound on this maximum or effective net construction is required.", DescribeRole.Theorem),
            Entry("commutator-stability", "norm_groupCommutator_sub_le", "Stability gains the small factor", Stability(),
                "For four unitary factors within a of identity and factor errors at most delta, the commutator error is at most 4*a*delta*(1+a). This is the Apache-2.0 CSD estimate of Zayn Blore, specialized to the matrix carrier. Its factorization pairs a factor difference with a small near-identity factor.", DescribeRole.Theorem,
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Computability/dawsonnielsen2006solovaykitaev"))),
            Entry("paired-word-invariant", "exists_word_at_level", "One list carries error and length together", Invariant(),
                "Start with a word u from the preceding level approximating the current U. The residual is U*star(eval(Gamma,u)), whose distance from identity equals the preceding error and whose determinant remains one. BalancedSU2Commutator supplies exact factors V,W at square-root distance. Approximate both at the same preceding level and concatenate their words with inverse words and u. Stability bounds this same list's error by e(n+1)=33*e(n)^(3/2), while its actual length is bounded by 5^(n+1)*L. This alphabet-parametric construction follows the licensed CSD ordinary-word induction; the residual always uses the preceding approximation to this target.", DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("uniform-ordinary-word-bound"),
                DeclarationHandle.Create(Prefix + "ordinary_word_solovay_kitaev"),
                H("The uniform polylogarithmic ordinary-word theorem"),
                StatementSource.FromAuthor(EventStatement()),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Computability/dawsonnielsen2006solovaykitaev")),
                Blocks(
                    Paragraph(Text("For every finite alphabet Gamma of determinant-one unitary matrices, assume inverse closure and density of its ordinary finite words in SU(2). Then K>0 and 0<epsilon0<1 can be chosen uniformly for every target U and every 0<epsilon<=epsilon0. One ordinary list w satisfies both the error and real-valued length inequalities. The exponent is exactly log(5)/log(3/2).")),
                    Paragraph(Text("A compactness net supplies the alphabet-dependent initial length. The paired word invariant gives the same list at every level; the licensed scalar and logarithmic estimates in SolovayKitaevRate eliminate the level. Zayn Blore's Apache-2.0 CSD proof is the source of the balanced decomposition, stability and rate estimates and of the fixed-alphabet word induction. The full license is docs/reports/qmutualinfo/csd-lean4-LICENSE.txt. This theorem concerns existence and ordinary list length. It asserts no effectiveness, runtime, optimality, numerical constants, physical realization, compressed length or bound uniform in growing dimension."))),
                DescribeRole.Theorem))));

    private static DocumentBlock.Describe Entry(string id, string name, string title, Formula formula,
        string body, DescribeRole role, AssessedProvenance? provenance = null) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
            provenance ?? AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(body))), role);

    private static Formula Evaluation()
    {
        Formula m=X("m"), g=X("Gamma"), i=X("i"), w=X("w");
        return Alphabet(And(Eq(Eval(g,Call("nil")),N(1)),
            All("i",Call("Fin",m),All("w",Words(m),
                Eq(Eval(g,Call("cons",i,w)),Multiply(At(g,i),Eval(g,w)))))));
    }
    private static Formula InverseDefinition()
    {
        Formula m=X("m"), s=X("sigma"), w=X("w");
        return All("m",Call("Nat"),All("sigma",new Formula.TypeArrow(Call("Fin",m),Call("Fin",m)),
            All("w",Words(m),Eq(Inv(s,w),Call("map",s,Call("reverse",w))))));
    }
    private static Formula SuccessorDefinition()
    {
        Formula m=X("m"), s=X("sigma"), v=X("v"), w=X("w"), u=X("u");
        return All("m",Call("Nat"),All("sigma",new Formula.TypeArrow(Call("Fin",m),Call("Fin",m)),
            All("v",Words(m),All("w",Words(m),All("u",Words(m),Eq(
                Call("successorWord",s,v,w,u),Call("concat",v,w,Inv(s,v),Inv(s,w),u)))))));
    }
    private static Formula FiniteNet()
    {
        Formula m=X("m"), g=X("Gamma"), eta=X("eta"), f=X("F"), l=X("L"), u=X("U"), w=X("w");
        Formula bound=All("w",Words(m),Imp(Member(w,f),Le(Call("length",w),l)));
        Formula net=All("U",Call("Mat"),Imp(Su(u),Ex("w",Words(m),
            And(Member(w,f),Lt(Error(g,u,w),eta)))));
        return Alphabet(Imp(Density(m,g),All("eta",Call("Real"),Imp(Pos(eta),
            Ex("F",Call("Finset",Words(m)),Ex("L",Call("Nat"),And(bound,net)))))));
    }
    private static Formula Stability()
    {
        Formula v=X("V"), w=X("W"), p=X("P"), q=X("Q"), a=X("a"), d=X("delta");
        Formula hyp=And(Unitary(v),And(Unitary(w),And(Unitary(p),And(Unitary(q),
            And(Le(Norm(Subtract(v,N(1))),a),And(Le(Norm(Subtract(w,N(1))),a),
            And(Le(Norm(Subtract(p,N(1))),a),And(Le(Norm(Subtract(q,N(1))),a),
            And(Le(Norm(Subtract(v,p)),d),Le(Norm(Subtract(w,q)),d))))))))));
        Formula result=Le(Norm(Subtract(Comm(v,w),Comm(p,q))),
            Multiply(Multiply(Multiply(N(4),a),d),Add(N(1),a)));
        return All("V",Call("Mat"),All("W",Call("Mat"),All("P",Call("Mat"),All("Q",Call("Mat"),
            All("a",Call("Real"),All("delta",Call("Real"),Imp(hyp,result)))))));
    }
    private static Formula Invariant()
    {
        Formula m=X("m"),g=X("Gamma"),s=X("sigma"),e=X("e"),l=X("L"),n=X("n"),u=X("U"),w=X("w");
        Formula hnet=All("U",Call("Mat"),Imp(Su(u),Ex("w",Words(m),
            And(Le(Error(g,u,w),e),Le(Call("length",w),l)))));
        Formula hyp=And(Generators(m,g),And(ChosenInverse(m,g,s),And(Le(N(0),e),
            And(Le(Call("sqrt",e),Frac(N(1),N(33))),hnet))));
        Formula result=All("n",Call("Nat"),All("U",Call("Mat"),Imp(Su(u),Ex("w",Words(m),
            And(Le(Error(g,u,w),Call("skErr",e,n)),
                Le(Call("length",w),Multiply(Pow(N(5),n),l)))))));
        return Alphabet(All("sigma",new Formula.TypeArrow(Call("Fin",m),Call("Fin",m)),
            All("e",Call("Real"),All("L",Call("Nat"),Imp(hyp,result)))));
    }
}

internal static class SolovayKitaevNotation
{
    internal static Formula X(string n) => F.Id(n);
    internal static Formula N(long n) => new Formula.Number(n);
    internal static Formula All(string n, Formula t, Formula b) => new Formula.Bind(
        FormulaQuantifier.ForAll,FormulaIdentifier.Create(n),t,b);
    internal static Formula Ex(string n, Formula t, Formula b) => new Formula.Bind(
        FormulaQuantifier.Exists,FormulaIdentifier.Create(n),t,b);
    internal static Formula At(Formula f, Formula x) => new Formula.Apply(f,[x]);
    internal static Formula Eq(Formula a, Formula b) => new Formula.Relation(a,FormulaRelationOperator.Equal,b);
    internal static Formula Le(Formula a, Formula b) => new Formula.Relation(a,FormulaRelationOperator.LessThanOrEqual,b);
    internal static Formula Lt(Formula a, Formula b) => new Formula.Relation(a,FormulaRelationOperator.LessThan,b);
    internal static Formula And(Formula a, Formula b) => new Formula.Logic(a,FormulaLogicOperator.And,b);
    internal static Formula Imp(Formula a, Formula b) => new Formula.Logic(a,FormulaLogicOperator.Implies,b);
    internal static Formula Pos(Formula a) => Lt(N(0),a);
    internal static Formula Frac(Formula a, Formula b) => new Formula.Fraction(a,b);
    internal static Formula Pow(Formula a, Formula b) => new Formula.Power(a,b);
    internal static Formula Norm(Formula a) => new Formula.Norm(a);
    internal static Formula Star(Formula a) => Call("star",a);
    internal static Formula Words(Formula m) => Call("List",Call("Fin",m));
    internal static Formula Su(Formula a) => And(Unitary(a),Eq(Call("det",a),N(1)));
    internal static Formula Unitary(Formula a) => new Formula.Relation(a,FormulaRelationOperator.MemberOf,Call("unitary",Call("Mat")));
    internal static Formula Member(Formula a, Formula f) => new Formula.Relation(a,FormulaRelationOperator.MemberOf,f);
    internal static Formula Eval(Formula g, Formula w) => Call("evalGamma",g,w);
    internal static Formula Inv(Formula s, Formula w) => Call("inverseWord",s,w);
    internal static Formula Error(Formula g, Formula u, Formula w) => Norm(Subtract(u,Eval(g,w)));
    internal static Formula Comm(Formula v, Formula w) => Multiply(Multiply(Multiply(v,w),Star(v)),Star(w));
    internal static Formula Exponent() => Frac(Call("log",N(5)),Call("log",Frac(N(3),N(2))));
    internal static Formula Alphabet(Formula body) => All("m",Call("Nat"),All("Gamma",
        new Formula.TypeArrow(Call("Fin",X("m")),Call("Mat")),body));
    internal static Formula Generators(Formula m, Formula g) => All("i",Call("Fin",m),Su(At(g,X("i"))));
    internal static Formula ChosenInverse(Formula m, Formula g, Formula s) => All("i",Call("Fin",m),
        Eq(At(g,At(s,X("i"))),Star(At(g,X("i")))));
    internal static Formula Density(Formula m, Formula g) => All("A",Call("Mat"),Imp(Su(X("A")),
        All("eta",Call("Real"),Imp(Pos(X("eta")),Ex("v",Words(m),Lt(Error(g,X("A"),X("v")),X("eta")))))));
    internal static Formula EventStatement()
    {
        Formula m=X("m"),g=X("Gamma"),k=X("K"),b=X("b"),e=X("epsilon"),u=X("U"),w=X("w");
        Formula inverse=All("i",Call("Fin",m),Ex("j",Call("Fin",m),
            Eq(At(g,X("j")),Star(At(g,X("i"))))));
        Formula paired=Ex("w",Words(m),And(Le(Error(g,u,w),e),
            Le(Call("real",Call("length",w)),Multiply(k,Pow(Call("log",Frac(N(1),e)),Exponent())))));
        Formula result=Ex("K",Call("Real"),Ex("b",Call("Real"),And(Pos(k),And(Pos(b),And(Lt(b,N(1)),
            All("epsilon",Call("Real"),Imp(And(Pos(e),Le(e,b)),All("U",Call("Mat"),Imp(Su(u),paired)))))))));
        return Alphabet(Imp(And(Generators(m,g),And(inverse,Density(m,g))),result));
    }
}
