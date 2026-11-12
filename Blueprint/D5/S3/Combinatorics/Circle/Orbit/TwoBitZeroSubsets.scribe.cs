using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Circle.Orbit;

internal sealed class TwoBitZeroSubsetsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Circle/Orbit/TwoBitZeroSubsets.";

    public DocumentDefinition Create()
    {
        Formula r = V("r"), a = V("a"), A = V("A");
        Formula labels = Call("Fin", r), subsets = Call("Finset", labels);
        Formula q = Add(Num(1), Pow(Num(2), a));
        Formula N = Sub(Pow(Num(2), r), Num(1));
        Formula source = Call("actualSource", r, q);
        Formula sum = Call("sum", A, source);
        Formula zero = Eq(sum, Num(0));
        Formula rho = Pow(Call("finRotate", r), a);
        Formula classification = Or(Eq(A, Name("empty")), Eq(A, Call("univ", labels)),
            Eq(Call("image", A, rho), Call("compl", A)));
        Formula divisibility = new Formula.Relation(N, FormulaRelationOperator.Divides,
            Mul(q, Call("mask", A)));
        Formula g = Call("gcd", a, r);
        Formula even = Call("Even", Call("div", r, g));
        Formula card = Call("card", Call("Z", r, a));
        Formula count = And(Imp(even, Eq(card, Add(Pow(Num(2), g), Num(2)))),
            Imp(Call("Not", even), Eq(card, Num(2))));
        Formula domain = And(Le(Num(2), r), Lt(Num(0), a), Lt(a, r));

        return DocumentDefinition.Create(ScribeNode.Create(
            "Exact integer-zero subsets of every labelled two-bit centered source are the two endpoints and complement-rotation subsets; a binary gcd identity gives their exact parity-dependent count.",
            H("Physical two-bit zero subsets: complement rotation and an exact gcd count"),
            Blocks(
                Paragraph(Text("Fix natural r and a with 2 <= r, 0 < a and a < r. Put N = 2^r-1 and q = 1+2^a. At every physical label i in Fin(r), s(i) is SourceWidth.actualSource(r,q,i): the integer centered representative of q*2^i modulo N, in [-floor(N/2),floor(N/2)]. The source and its integer values are fixed independently of any proposed zero subset. A ranges over Finset(Fin(r)); equal numerical source values at different labels remain separate occurrences. No unit, coprimality, ordering, period, parity or finite-cutoff hypothesis is added.")),
                Paragraph(Text("In the displayed statements sum(A,actualSource(r,q)) means exactly the integer sum over i in A of SourceWidth.actualSource(r,q,i). The natural mask is M(A) = ZeroSumSubsets.mask(A) = sum over i in A of 2^i. The map rho = finRotate(r)^a sends the physical label i to i+a modulo r; image(A,rho) is the image finset and compl(A) is its complement in all Fin(r). Z(r,a) is the finite family obtained by filtering the universe of every physical-label finset by that independent exact integer-sum equality. Thus card(Z) includes both the empty and full subsets.")),
                Paragraph(Text("The three declaration descriptions below retain the whole parameter range of the owning Lean statements. Natural division is used in r/gcd(a,r), and Even is a conclusion branch condition rather than an assumption. The source module proves the classification, the equivalence with divisibility, and the exact count as separate public targets; the counting argument actually uses the divisibility equivalence.")),
                Describe.Lean(DescribeId.Create("actual-zero-iff"),
                    DeclarationHandle.Create(Prefix + "actual_zero_iff"),
                    H("Exact integer zero is empty, full, or a physical complement translate"),
                    StatementSource.FromAuthor(Disp(Q(Imp(domain,
                        Q(IffOf(zero, classification), ("A", subsets))),
                        ("r", Nat()), ("a", Nat())))),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text("For every physical subset A, its actual integer source sum is zero if and only if A is empty, A is all physical labels, or rho(A) equals the physical complement of A. The two endpoint alternatives are explicit. In particular the theorem is not merely a congruence modulo N, and it does not identify the physical labels with the gcd many reduced choices.")),
                        Paragraph(Text("The local centered two-bit identity is the mechanism. Since 0<a<r, the labels i and rho(i) differ. Write t for the physical label r-1. Centering the two distinct powers of two gives s(i) = 2^i + 2^rho(i) - N*(indicator(i=t)+indicator(rho(i)=t)). Summing over A and reindexing the second term gives sum(A,s) = M(A)+M(rho(A))-N*(indicator(t in A)+indicator(t in rho(A))). Each indicator is an integer zero or one. This is an exact integer identity, not a deduction from modular zero alone.")),
                        Paragraph(Text("For nonempty proper A, mask positivity, the strict mask bound below N, and bijectivity of rho put M(A)+M(rho(A)) strictly between zero and 2N. Integer zero in the preceding identity makes this sum divisible by N, hence equal to N. The complement mask identity M(A)+M(A complement)=N and binary-mask injectivity then force rho(A)=A complement. Conversely that complement equality makes the mask sum N and the two top-label indicators add to one, so the exact integer sum is zero. The empty case is immediate; the full case uses the already established source_cycle total-zero identity.")),
                        Paragraph(Text("This describes physical subsets for the particular two-bit source. Reading the relation along a rho-cycle forces alternating membership; an odd cycle cannot support a proper complement-rotation subset. The formal proof here obtains the exact number through binary arithmetic, rather than assuming a cycle-count formula or constructing a new signed-action conjugacy."))),
                    DescribeRole.Theorem),
                Describe.Lean(DescribeId.Create("actual-zero-iff-dvd"),
                    DeclarationHandle.Create(Prefix + "actual_zero_iff_dvd"),
                    H("Two-bit modular zero is sufficient for exact integer zero"),
                    StatementSource.FromAuthor(Disp(Q(Imp(domain,
                        Q(IffOf(zero, divisibility), ("A", subsets))),
                        ("r", Nat()), ("a", Nat())))),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text("On the same entire parameter range and for every A, the actual integer sum is zero if and only if the natural number N divides q*M(A). This is stronger than the general zero_mask_dvd necessary condition. Its reverse implication is proved for these two-bit sources and is not asserted for an arbitrary centered source.")),
                        Paragraph(Text("The forward direction reuses zero_mask_dvd. For the reverse direction, powers of two at rho(i) and 2^a*2^i agree modulo N. Summing gives divisibility of q*M(A) - (M(A)+M(rho(A))). Combining it with the assumed divisibility gives N dividing the mask sum. After separating empty and full A, the same strict interval argument makes that sum exactly N. Binary injectivity supplies the complement translate, and actual_zero_iff returns exact integer zero. No physical ordering certificate occurs in this implication.")),
                        Paragraph(Text("The private reduced-divisibility helper used in the count puts d = gcd(q,N) and Q = N/d. With N positive, it proves that the very same independent actual integer-zero condition is equivalent to Q dividing M(A). Gcd cancellation proves the forward direction. For the reverse direction, d divides both q and N and d*(N/d)=N, so Q dividing M(A) reconstructs N dividing q*M(A), and this public equivalence supplies integer zero. The helper therefore connects both sides of the later counting bijection to physical zero, not just to a congruence superset."))),
                    DescribeRole.Theorem),
                Describe.Lean(DescribeId.Create("actual-zero-subsets-card"),
                    DeclarationHandle.Create(Prefix + "actual_zero_subsets_card"),
                    H("All physical zero subsets, with both endpoints, have an exact gcd and parity count"),
                    StatementSource.FromAuthor(Disp(Q(Imp(domain, count),
                        ("r", Nat()), ("a", Nat())))),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text("Let g = gcd(a,r). If r/g is even, the exact number of all physical integer-zero subsets is 2^g+2; otherwise it is two. The two always-counted subsets are empty and full. These assertions include r=2,a=1, for which q=N=3 and every actual source value is zero: all four physical subsets are counted. There is no restriction to units or to proper subsets.")),
                        Paragraph(Text("First, binary-mask injectivity and equality of finite cardinalities make A -> M(A) a bijection from every physical subset onto all natural masks in [0,2^r-1]. Both endpoints remain represented: zero by empty and N by univ. With d=gcd(q,N), Q=N/d is positive and Q*d=N. The reduced physical-zero equivalence sends a zero subset to the integer M(A)/Q in [0,d]. Multiplication by Q recovers its mask, proving injectivity. Conversely every n in [0,d] has Q*n<=N and therefore a physical mask preimage A; Q divides its mask and the reverse physical-zero bridge proves its actual integer sum zero. This proves exactly d+1 subsets. The public divisibility theorem lies on the live path through this helper in both directions of the bijection.")),
                        Paragraph(Text("The arithmetic evaluation of d is independent of an assumed orbit count. Write a=g*u and r=g*v, with u and v coprime and g positive. Since a>0, q is odd. Any common divisor of q and 2^g-1 divides both 2^a+1 and 2^a-1, hence divides two; oddness forces it to be one. Also d divides 2^(2a)-1 and 2^r-1, so the power-minus-one gcd identity makes d divide 2^gcd(2a,r)-1. Coprimality of u,v gives gcd(2a,r)=g*gcd(2,v).")),
                        Paragraph(Text("If v is odd, gcd(2,v)=1; the preceding coprimality forces d=1. If v is even, u is odd and d divides (2^g-1)*(2^g+1). Cancelling the coprime first factor shows d divides 2^g+1. In the other direction, odd u makes 2^g+1 divide 2^a+1, while 2g divides r and the difference-of-squares factorization makes it divide 2^r-1. Thus d=2^g+1 in the even branch and d=1 in the odd branch. Substitution into the already proved exact d+1 count yields the displayed formula.")),
                        Paragraph(Text("For r=4,a=1, g=1 and r/g=4 is even. The source values at labels 0,1,2,3 are 3,6,-3,-6. The proper zero subsets are {0,2} and {1,3}, giving four total with the endpoints. They are physical alternating subsets, not singleton representatives of a reduced one-bit space. For r=6,a=3, g=3 and r/g=2. The source values are 9,18,-27,9,18,-27. Each proper zero subset chooses one label from each pair {0,3}, {1,4}, {2,5}; the eight choices all sum to zero, and the two endpoints make ten. Repeated numerical values do not merge their labels. These numerical illustrations explain the theorem and are not additional Lean declarations or fresh acceptance evidence.")),
                        Paragraph(Text("The result classifies exact zero subsets for the family q=1+2^a. It gives no new signed-action conjugacy, no classification of every physical cyclic structure, and no complete ordering or capacity theorem for arbitrary sources. A complement-rotation constraint can be read as alternating physical membership, but the proof does not construct an ordering inside a geometric strip. This exposition makes no literature novelty claim and is not an official delivery, freeze, audit, CI or merge certificate."))),
                    DescribeRole.Theorem)), []));
    }

    private static Formula V(string name) => F.Id(name);
    private static Formula Name(string name) => new Formula.NamedConstant(FormulaIdentifier.Create(name));
    private static Formula Nat() => Name("Nat");
    private static Formula Num(long n) => new Formula.Number(n);
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
    private static Formula Q(Formula body, params (string Name, Formula Domain)[] variables)
    {
        for (var i = variables.Length - 1; i >= 0; i--)
            body = new Formula.Bind(FormulaQuantifier.ForAll,
                FormulaIdentifier.Create(variables[i].Name), variables[i].Domain, body);
        return body;
    }
    private static Formula Eq(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.Equal, y);
    private static Formula Le(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.LessThanOrEqual, y);
    private static Formula Lt(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.LessThan, y);
    private static Formula Imp(Formula x, Formula y) => new Formula.Logic(x, FormulaLogicOperator.Implies, y);
    private static Formula IffOf(Formula x, Formula y) => new Formula.Logic(x, FormulaLogicOperator.Iff, y);
    private static Formula And(params Formula[] values) => Logic(FormulaLogicOperator.And, values);
    private static Formula Or(params Formula[] values) => Logic(FormulaLogicOperator.Or, values);
    private static Formula Logic(FormulaLogicOperator op, Formula[] values)
    {
        Formula result = values[^1];
        for (var i = values.Length - 2; i >= 0; i--)
            result = new Formula.Logic(values[i], op, result);
        return result;
    }
    private static Formula Add(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Add, y);
    private static Formula Sub(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Subtract, y);
    private static Formula Mul(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Multiply, y);
    private static Formula Pow(Formula x, Formula y) => new Formula.Power(x, y);
}
