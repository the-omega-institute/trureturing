using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Dice;

internal sealed class EaslickMinimalAdvantageDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Dice/EaslickMinimalAdvantage.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Certificates/easlick2026minimaldice");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Sorted dice and exact unconditional probabilities describe minimal-advantage simple cycles.",
        H("Minimal winning advantage for fair dice"),
        Blocks(
            Node("easlick-isdie","Valid sorted dice","IsDie","For every natural n and list d of natural labels, IsDie(n,d) means that d has length n, is pairwise nondecreasing, and each face x occurring in d satisfies 1 ≤ x ≤ n. Repeated labels and the standard tuple are permitted.", DescribeRole.Definition),
            Node("easlick-wincount","Strict winning ordered outcomes","winCount","For any two lists d and e of natural labels, winCount(d,e) is the sum over occurrences x in d and y in e of the indicator of y < x. Repeated labels retain their multiplicities and ties contribute zero.", DescribeRole.Definition),
            Node("easlick-indexwincount","Strict wins on the independent index product","indexWinCount","For all lists d,e, indexWinCount(d,e) is the sum over i in Fin(length(d)) and j in Fin(length(e)) of the indicator of e[j] < d[i]. Both indices vary over their whole finite domains independently.", DescribeRole.Definition),
            Node("easlick-winprobability","Unconditional uniform strict-win probability","winProbability","For all lists d,e, winProbability(d,e) is the rational indexWinCount(d,e) divided by length(d) times length(e). For nonempty dice this gives every ordered independent pair of face indices the same probability and leaves ties in the denominator.", DescribeRole.Definition),
            Node("easlick-threshold","The least integer above half the outcome count","threshold","For every natural n, threshold(n) = floor(n²/2) + 1. This is an integer score; its attainability by valid dice is a separate assertion.", DescribeRole.Definition),
            Node("easlick-isminimum","The true attained minimum","IsMinimum","For every natural n and rational p, IsMinimum(n,p) requires valid n-face dice d,e with winProbability(d,e)=p, requires p>1/2, and requires p≤winProbability(a,b) for every valid ordered pair a,b with winProbability(a,b)>1/2.", DescribeRole.Definition),
            Node("easlick-edge","Minimum-advantage directed edges","Edge","For natural n and lists d,e, Edge(n,d,e) requires that both are valid n-face dice and that their actual unconditional strict-win probability is an attained minimum among all probabilities above one half.", DescribeRole.Definition),
            Node("easlick-hascycle","Simple cycles with their closing edge","HasCycle","For natural n,k, HasCycle(n,k) means there is a nonempty list c of exactly k pairwise distinct dice such that c followed by its first entry is a chain for Edge(n). The last-to-first edge is included and no vertex can be reused.", DescribeRole.Definition),
            Node("easlick-s","An exact global maximum","S","For every natural n, S(n) means HasCycle(n,n) and, for every natural k>n, the negation of HasCycle(n,k). Thus the bound concerns all simple cycles in the entire graph.", DescribeRole.Definition),
            Node("easlick-conjectureone","The complete conjecture","ConjectureOne","ConjectureOne is the proposition S(6) and, for every natural n≥7, not S(n). It imposes no condition at three, four or five, and it does not assume the existence of longer cycles.", DescribeRole.Definition),
            Node("easlick-wincount-eq-indexwincount","The occurrence-to-index counting bridge","winCount_eq_indexWinCount","For all lists d and e of natural labels, winCount(d,e)=indexWinCount(d,e). Each occurrence in a list is recovered from its face index, so multiplicities are preserved in the equality.", DescribeRole.Theorem),
            Node("easlick-threshold-attained","Attainment for every n at least three","threshold_attained","For every natural n≥3 there exist valid sorted n-face dice d,e whose strict-win count is threshold(n). For n=2k the dice are 1 repeated k−1 times, then 2, then 3 repeated k times, against 1 followed by 2 repeated 2k−1 times. For n=2k+1 they are 1 repeated k times, then 2, then 3 repeated k times, against 1 repeated k+1 times followed by 2 repeated k times.", DescribeRole.Theorem),
            Node("easlick-above-half-iff", "The exact integer-grid condition", "above_half_iff", "For every natural n>0 and all valid sorted n-face dice d,e, winProbability(d,e)>1/2 if and only if threshold(n)≤winCount(d,e).", DescribeRole.Theorem),
            Node("easlick-minimum-probability", "The actual attained minimum", "minimum_probability", "For every natural n≥3, IsMinimum(n,threshold(n)/n²). The explicit attaining pair supplies existence, and the integer-grid condition bounds every other actual probability above one half.", DescribeRole.Theorem),
            Node("easlick-edge-iff", "Edges are exactly threshold scores", "edge_iff", "For every natural n≥3 and all valid n-face dice d,e, Edge(n,d,e) if and only if winCount(d,e)=threshold(n). This equivalence identifies the graph from the actual minimum among all ordered dice pairs.", DescribeRole.Theorem),
            Node("easlick-padded","Nested interval padding","padded","For natural b,t,j, a Boolean c and a seed list d, padded(b,t,j,c,d) concatenates j copies of 1+2c, t−j copies of 2+2c, the seed labels increased by four, and t copies of b+6−c, with c read as zero or one.", DescribeRole.Definition),
            Node("easlick-padded-wincount","Exact score in both directions","padded_winCount","For all naturals b,t,j,k with j≤t and k≤t, Boolean c, and seed lists d,e whose labels lie between one and b, the score from padded(b,t,j,c,d) to padded(b,t,k,not c,e) equals winCount(d,e)+t length(d)+t length(e)+2t². The two clone indices can be chosen independently.", DescribeRole.Theorem),
            Node("easlick-threshold-padding","The threshold under even padding","threshold_padding","For every natural r,t, threshold(r+2t)=threshold(r)+2tr+2t², with no restriction on the parity of r.", DescribeRole.Theorem),
            Node("easlick-padded-isdie","Sortedness and label bounds of padding","padded_isDie","For all naturals r,b,t,j, Boolean c and list d, suppose j≤t, d has length r and is nondecreasing, all its labels lie in [1,b], and b+6≤r+2t. Then padded(b,t,j,c,d) is a valid sorted (r+2t)-face die.", DescribeRole.Theorem),
            Node("easlick-padded-eq-imp","Recovering seed and clone","padded_eq_imp","For all naturals b,t,j,k, Booleans c,c′ and seed lists d,e with labels in [1,b], equality padded(b,t,j,c,d)=padded(b,t,k,c′,e) implies d=e and implies j=k whenever c=c′. Restricting to central labels recovers the seed and the first low-label multiplicity recovers the clone.", DescribeRole.Theorem)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(StrataLint.Scribe.FormulaDsl.Disp(Statement(declaration))),
            declaration is "IsDie" or "winCount" or "indexWinCount" or "winProbability" or "IsMinimum" or "Edge" or "HasCycle" or "S" or "ConjectureOne" or "threshold_attained" or "minimum_probability" or "edge_iff"
                ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose)), Paragraph(Text("In the formulas, at selects a zero-based face or cycle position, sum sums every element of the displayed finite sequence, NatToRat is the natural-to-rational cast, NatSub is truncated natural subtraction, shift adds its displayed constant to each face, and head denotes head!; HasCycle separately requires a nonempty cycle. Boolean toNat sends false to zero and true to one. Rational division is total, with x divided by zero equal to zero; all graph applications use at least three faces. All finite face-index domains retain repeated-face multiplicities."))), role);
    private static Formula.BoundVariable B(string name, Formula type) => new(FormulaIdentifier.Create(name), type);
    private static Formula All(Formula body, params Formula.BoundVariable[] variables) => new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables], body);
    private static Formula Ex(Formula body, params Formula.BoundVariable[] variables) => new Formula.BindMany(FormulaQuantifier.Exists, [.. variables], body);
    private static Formula And(params Formula[] xs) => xs.Aggregate((a,b) => new Formula.Logic(a, FormulaLogicOperator.And,b));
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a,FormulaLogicOperator.Implies,b);
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(a,FormulaLogicOperator.Iff,b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a,FormulaRelationOperator.LessThanOrEqual,b);
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a,FormulaRelationOperator.LessThan,b);
    private static Formula Mem(Formula a, Formula b) => new Formula.Relation(a,FormulaRelationOperator.MemberOf,b);
    private static Formula Not(Formula a) => new Formula.Not(a);
    private static Formula Frac(Formula a, Formula b) => new Formula.Fraction(a,b);
    private static Formula Len(Formula a) => Call("length",a);
    private static Formula N => Id("Nat");
    private static Formula L => Call("List",N);
    private static Formula LL => Call("List",L);
    private static Formula Half => Frac(Num(1),Num(2));
    private static Formula Bounds(Formula d, Formula b) => All(Imp(Mem(Id("x"),d),And(Le(Num(1),Id("x")),Le(Id("x"),b))),B("x",N));
    private static Formula Sorted(Formula d) => All(Imp(Lt(Id("i"),Id("j")),Le(Call("at",d,Id("i")),Call("at",d,Id("j")))),B("i",Call("Fin",Len(d))),B("j",Call("Fin",Len(d))));
    private static Formula Closed(Formula n, Formula c) => Call("IsChain",Call("Edge",n),Call("append",c,Call("singleton",Call("head",c))));
    internal static Formula Statement(string declaration)
    {
        Formula n=Id("n"),r=Id("r"),b=Id("b"),t=Id("t"),j=Id("j"),k=Id("k");
        Formula d=Id("d"),e=Id("e"),c=Id("c"),cp=Id("cprime"),p=Id("p");
        Formula target=Add(r,Multiply(Num(2),t));
        Formula dieD=Call("IsDie",n,d),dieE=Call("IsDie",n,e),w=Call("winCount",d,e),prob=Call("winProbability",d,e),th=Call("threshold",n);
        Formula padD=Call("padded",b,t,j,c,d),padE=Call("padded",b,t,k,cp,e);
        Formula minimum=Call("IsMinimum",n,Frac(Call("NatToRat",th),Call("NatToRat",Multiply(n,n))));
        Formula sum=Call("sum",new Formula.Sequence(Call("sum",new Formula.Sequence(Call("ite",Lt(Call("at",e,Id("v")),Call("at",d,Id("u"))),Num(1),Num(0)),Id("v"),Call("Fin",Len(e)))),Id("u"),Call("Fin",Len(d))));
        Formula result=declaration switch
        {
            "IsDie" => All(Iff(dieD,And(Equal(Len(d),n),Sorted(d),Bounds(d,n))),B("n",N),B("d",L)),
            "winCount" => All(Equal(w,sum),B("d",L),B("e",L)),
            "indexWinCount" => All(Equal(Call("indexWinCount",d,e),sum),B("d",L),B("e",L)),
            "winProbability" => All(Equal(prob,Frac(Call("NatToRat",Call("indexWinCount",d,e)),Call("NatToRat",Multiply(Len(d),Len(e))))),B("d",L),B("e",L)),
            "threshold" => All(Equal(th,Add(new Formula.Floor(Frac(Multiply(n,n),Num(2))),Num(1))),B("n",N)),
            "IsMinimum" => All(Iff(Call("IsMinimum",n,p),And(Ex(And(dieD,dieE,Equal(prob,p)),B("d",L),B("e",L)),Lt(Half,p),All(Imp(And(dieD,dieE,Lt(Half,prob)),Le(p,prob)),B("d",L),B("e",L)))),B("n",N),B("p",Id("Rat"))),
            "Edge" => All(Iff(Call("Edge",n,d,e),And(dieD,dieE,Call("IsMinimum",n,prob))),B("n",N),B("d",L),B("e",L)),
            "HasCycle" => All(Iff(Call("HasCycle",n,k),Ex(And(Equal(Len(c),k),Call("Nodup",c),NotEqual(c,Call("nil")),Closed(n,c)),B("c",LL))),B("n",N),B("k",N)),
            "S" => All(Iff(Call("S",n),And(Call("HasCycle",n,n),All(Imp(Lt(n,k),Not(Call("HasCycle",n,k))),B("k",N)))),B("n",N)),
            "ConjectureOne" => Iff(Call("ConjectureOne"),And(Call("S",Num(6)),All(Imp(Le(Num(7),n),Not(Call("S",n))),B("n",N)))),
            "padded" => All(Equal(padD,Call("append",Call("replicate",j,Add(Num(1),Multiply(Num(2),Call("toNat",c)))),Call("append",Call("replicate",Call("NatSub",t,j),Add(Num(2),Multiply(Num(2),Call("toNat",c)))),Call("append",Call("shift",d,Num(4)),Call("replicate",t,Call("NatSub",Add(b,Num(6)),Call("toNat",c))))))),B("b",N),B("t",N),B("j",N),B("c",Id("Bool")),B("d",L)),
            "winCount_eq_indexWinCount" => All(Equal(w,Call("indexWinCount",d,e)),B("d",L),B("e",L)),
            "threshold_attained" => All(Imp(Le(Num(3),n),Ex(And(dieD,dieE,Equal(w,th)),B("d",L),B("e",L))),B("n",N)),
            "above_half_iff" => All(Imp(And(Lt(Num(0),n),dieD,dieE),Iff(Lt(Half,prob),Le(th,w))),B("n",N),B("d",L),B("e",L)),
            "minimum_probability" => All(Imp(Le(Num(3),n),minimum),B("n",N)),
            "edge_iff" => All(Imp(And(Le(Num(3),n),dieD,dieE),Iff(Call("Edge",n,d,e),Equal(w,th))),B("n",N),B("d",L),B("e",L)),
            "padded_winCount" => All(Imp(And(Le(j,t),Le(k,t),Bounds(d,b),Bounds(e,b)),Equal(Call("winCount",padD,Call("padded",b,t,k,Call("BoolNot",c),e)),Add(Add(Add(w,Multiply(t,Len(d))),Multiply(t,Len(e))),Multiply(Multiply(Num(2),t),t)))),B("b",N),B("t",N),B("j",N),B("k",N),B("c",Id("Bool")),B("d",L),B("e",L)),
            "threshold_padding" => All(Equal(Call("threshold",target),Add(Add(Call("threshold",r),Multiply(Multiply(Num(2),t),r)),Multiply(Multiply(Num(2),t),t))),B("r",N),B("t",N)),
            "padded_isDie" => All(Imp(And(Le(j,t),Equal(Len(d),r),Sorted(d),Bounds(d,b),Le(Add(b,Num(6)),target)),Call("IsDie",target,padD)),B("r",N),B("b",N),B("t",N),B("j",N),B("c",Id("Bool")),B("d",L)),
            "padded_eq_imp" => All(Imp(And(Bounds(d,b),Bounds(e,b),Equal(padD,padE)),And(Equal(d,e),Imp(Equal(c,cp),Equal(j,k)))),B("b",N),B("t",N),B("j",N),B("k",N),B("c",Id("Bool")),B("cprime",Id("Bool")),B("d",L),B("e",L)),
            "finite_cycle_witnesses" => And(Call("HasCycle",Num(6),Num(6)),Call("HasCycle",Num(7),Num(14)),Call("HasCycle",Num(8),Num(29)),Call("HasCycle",Num(9),Num(10)),Call("HasCycle",Num(10),Num(110)),Call("HasCycle",Num(11),Num(14))),
            "cycle_edge_at" => All(Imp(And(Equal(Len(c),k),Closed(r,c),Lt(Num(0),k)),All(Call("Edge",r,Call("at",c,Id("i")),Call("at",c,new Formula.Modulo(Add(Id("i"),Num(1)),k))),B("i",Call("Fin",k)))),B("r",N),B("k",N),B("c",LL)),
            "padded_cycle" => All(Imp(And(Le(Num(3),r),Lt(Num(0),k),Equal(new Formula.Modulo(k,Num(2)),Num(0)),Le(Add(r,Num(6)),target),Call("HasCycle",r,k)),Call("HasCycle",target,Multiply(k,Add(t,Num(1))))),B("r",N),B("k",N),B("t",N)),
            "longer_cycle" => All(Imp(Le(Num(7),n),Ex(And(Lt(n,k),Call("HasCycle",n,k)),B("k",N))),B("n",N)),
            "not_S_above_six" => All(Imp(Le(Num(7),n),Not(Call("S",n))),B("n",N)),
            "six_cycle_bound" => All(Imp(Call("HasCycle",Num(6),k),Le(k,Num(6))),B("k",N)),
            "S_six" => Call("S",Num(6)),
            "conjecture_one" => And(Call("S",Num(6)),All(Imp(Le(Num(7),n),Not(Call("S",n))),B("n",N))),
            _ => throw new ArgumentException("Unknown dice declaration",nameof(declaration))
        };
        return result;
    }

}
