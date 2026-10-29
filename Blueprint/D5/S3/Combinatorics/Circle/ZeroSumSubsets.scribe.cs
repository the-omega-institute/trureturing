using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Circle;

internal sealed class ZeroSumSubsetsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Circle/ZeroSumSubsets.";

    public DocumentDefinition Create()
    {
        Formula k = V("k"), t = V("t"), A = V("A"), blocks = V("blocks");
        Formula N = Sub(Pow(Num(2), k), Num(1));
        Formula g = Call("gcd", t, N);
        Formula labels = Call("Fin", k);
        Formula subsets = Call("Finset", labels);
        Formula sum = Call("sum", A, Call("actualSource", k, t));
        Formula zeros = Call("Z", k, t);
        Formula bound = Le(Call("card", zeros), Add(g, Num(1)));
        Formula blockHyp = And(
            Q(Imp(Call("mem", A, blocks), Call("Nonempty", A)), ("A", subsets)),
            Call("PairwiseDisjoint", blocks),
            Q(Imp(Call("mem", A, blocks), Eq(sum, Num(0))), ("A", subsets)));
        Formula n = V("n"), m = V("m"), B = V("B"), v = V("v"), i = V("i");
        Formula counts = new Formula.TypeArrow(labels, Nat());
        Formula c = V("c"), source = V("s"), modulus = V("N");
        Formula boolLabels = new Formula.TypeArrow(labels, Name("Bool"));
        Formula integerSource = new Formula.TypeArrow(labels, Name("Int"));
        Formula pathHypotheses = And(
            Eq(Call("sum", source), Num(0)),
            Call("cyclicStep", source, c, modulus),
            Call("physical", m, c),
            Call("chargeZero", m, c));
        Formula pathStatement = Q(
            Imp(pathHypotheses, Call("neutralCarryPath", k, c, source, modulus, m)),
            ("k", Nat()), ("c", boolLabels), ("s", integerSource), ("N", Name("Int")),
            ("m", counts));
        Formula L(Formula x) => Call("L", x);
        Formula E(Formula x) => Call("E", x);
        Formula M(Formula x) => Call("M", x);
        Formula T(Formula x) => Call("T", k, t, x);
        Formula J(Formula x) => Call("J", k, t, x);
        Formula Core(Formula a, Formula c) => And(
            Call("Nonempty", a),
            Q(Eq(Call("int", Call("apply", n, i)),
                Sub(Add(Call("indicator", a, i), Mul(Num(2), Call("int", Call("apply", c, i)))),
                    Call("int", Call("apply", c, Call("pred", k, i))))), ("i", labels)),
            Eq(L(n), Add(Call("card", a), L(c))),
            Eq(E(n), Add(M(a), Mul(N, Call("apply", c, Sub(k, Num(1)))))),
            Eq(T(n), Add(Call("sourceSum", k, t, a), Mul(N, J(c)))),
            Imp(Eq(T(n), Num(0)), Call("dvd", Call("div", N, g), M(a))),
            Imp(Call("Coprime", t, N), Imp(Eq(T(n), Num(0)), And(
                Eq(a, Call("univ", labels)), Eq(J(c), Num(0)),
                Eq(L(n), Add(k, L(c))), Le(k, L(n)),
                new Formula.Logic(Eq(L(n), k), FormulaLogicOperator.Iff,
                    Q(Eq(Call("apply", n, i), Num(1)), ("i", labels)))))));
        Formula carryStatement = Q(Imp(And(Lt(Num(0), k), Call("ne", n, Num(0))),
            Ex("A", subsets, Ex("m", counts, And(Core(A, m),
                Q(Imp(Core(B, v), And(Eq(B, A), Eq(v, m))), ("B", subsets), ("v", counts)))))),
            ("k", Nat()), ("t", Nat()), ("n", counts));
        return DocumentDefinition.Create(ScribeNode.Create(
            "Cyclic natural carrying gives a unique physical binary endpoint and sharp unit-source relation length; binary masks also bound exact zero subsets and independent zero blocks.",
            H("Cyclic carries and zero relations of the physical circle source"),
            Blocks(
                Describe.Lean(DescribeId.Create("neutral-carry-path"),
                    DeclarationHandle.Create(Prefix + "neutral_carry_path"),
                    H("Atomic neutral coefficient paths preserve physical nonnegativity and exact zero"),
                    StatementSource.FromAuthor(Disp(pathStatement)),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text("Fix k, an arbitrary Boolean labelling c : Fin(k) -> Bool, an arbitrary integer source s : Fin(k) -> Int, and an integer modulus N. Let tau = finRotate(k), pred = tau^{-1}, eps(a) = int(c(a)) - int(c(tau(a))), and q(u,a) = 1 + 2*int(u(a)) - int(u(pred(a))). Assume sum_a s(a) = 0 and 2*s(a) - s(tau(a)) = N*eps(a) for every physical label. For a natural coefficient vector m, assume q(m,a) >= 0 and sum_a int(m(a))*eps(a) = 0.")),
                        Paragraph(Text("The theorem constructs a finite list P of natural coefficient vectors with head m and last element zero. Its chain relation is inline: an edge removes one available neutral carry at a label with eps = 0, or removes an atomic pair of available carries at labels with eps = +1 and eps = -1. The singleton packet has cardinality one, the opposite packet has cardinality two, the selected labels are distinct, and the coordinate equations are in Nat, so no truncated subtraction is hidden. Each edge records the corresponding decrease of the total coefficient mass.")),
                        Paragraph(Text("At every vertex u in P, q(u,a) >= 0, the Boolean charge sum Q(u) = sum_a int(u(a))*eps(a) is zero, and the source sum sum_a q(u,a)*s(a) is zero. The source-zero clause is obtained by applying the existing carry_charge ledger to the natural vector q(u).toNat; nonnegativity makes its integer cast exactly q(u). The existing carry_length owner is not reproved or used to assert a geometric order.")),
                        Paragraph(Text("The selector is the Boolean-partition argument on the live induction path. If no neutral or positive available label exists, summing 2*u(a) <= u(pred(a)) over the true-labelled set forces all true-labelled coefficients to vanish; charge balance then forces the opposite boundary coefficients to vanish, and the global cyclic sum gives u = 0, a contradiction. Complementing c supplies the negative label. The selector itself does not require q >= 0; that hypothesis is used only to preserve q along a packet edge.")),
                        Paragraph(Text("For the native circle source, take s = actualSource(k,t), N = modulus(k), and c(a) = decide(0 < actualSource(k,t,a)). The source_cycle identity supplies the displayed step equation and the Boolean sign identity supplies eps. A native application also needs the supplied full-baseline m, q(m) >= 0, and charge-zero hypotheses from cyclic_binary_normal_form; the abstract path theorem does not assert those hypotheses for every native zero relation and introduces no forwarding specialization.")),
                        Paragraph(Text("This is an algebraic coefficient path with physical labels retained. It does not quotient labels by a period, realize a word in the half strip, shorten a geometric cycle, or complete the original Circle C3.1 statement. The k = 5, t = 3 example with packet size at most two records the remaining geometric gap: a size-three packet may be needed for strip realization."))),
                    DescribeRole.Theorem),
                Describe.Lean(DescribeId.Create("cyclic-binary-normal-form"),
                    DeclarationHandle.Create(Prefix + "cyclic_binary_normal_form"),
                    H("Natural cyclic carries and the sharp unit relation length"),
                    StatementSource.FromAuthor(Disp(carryStatement)),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text("Let k>0 and t be arbitrary natural numbers, N=2^k-1, and s(i)=actualSource(k,t,i) on the physical labels Fin(k). For any nonzero natural coefficient function n, there is exactly one pair consisting of a nonempty physical subset A and natural carries m. Write pred for the inverse of finRotate(k), L(x)=sum_i x(i), E(x)=sum_i x(i)2^i, and M(A)=sum_{i in A}2^i. In the coordinate equation the indicator is integer valued, every coefficient is cast to the integers before subtraction, and the last index k-1 denotes its physical Fin(k) label.")),
                        Paragraph(Text("The pair satisfies n(i)=indicator_A(i)+2m(i)-m(pred(i)), L(n)=card(A)+L(m), and E(n)=M(A)+N m(k-1). The endpoint mask lies in [1,N]; the full mask N represents residue zero. To construct it, fire any coordinate containing at least two units, subtracting two there and adding one at its successor. The natural total decreases by exactly one and the vector remains nonzero. At k=1 these changes occur at the same coordinate and subtract one. Strong induction ends at a nonempty binary vector. Summing the coordinate identity gives the length formula; weighting by powers of two cancels every interior contribution and leaves only the last carry.")),
                        Paragraph(Text("Two possible endpoints have congruent masks in [1,N], so their masks agree and binary-mask injectivity gives the same physical subset. For two carry vectors their integer difference d satisfies 2d(i)=d(pred(i)). Reindexing the sum of absolute values gives twice that sum equal to itself, hence d=0. This proves uniqueness of the counts, without asserting uniqueness of a firing order.")),
                        Paragraph(Text("For the exact source put eps(i)=1 when N<4s(i), eps(i)=-1 when 4s(i)<-N, and eps(i)=0 otherwise. Define T(x)=sum_i x(i)s(i) and J(m)=sum_i m(i)eps(i), in the integers; their displayed arguments also show the fixed parameters k,t. The displayed sourceSum(k,t,A) means sum_{i in A}s(i). Centered doubling gives 2s(i)-s(next(i))=N eps(i). The unsigned potential u(i)=s(i)+(N if s(i)<0 else 0) satisfies u(next(i))-u(i)=s(i). Reindexing its cyclic sum gives sum_i s(i)=0, including k=1, zero sources, repeated values and short periods. Pairing the same coordinate equation with s proves T(n)=sum_{i in A}s(i)+N J(m). In particular carrying preserves modular charge but can change exact integer charge; the negative wrap has sign minus one.")),
                        Paragraph(Text("If T(n)=0, then N divides t E(n). The weighted identity and gcd cancellation imply that N/gcd(t,N) divides M(A), for the very same pair. For a unit t modulo N, positivity and the upper bound M(A)<=N force M(A)=N and A=univ. The source total and the charge identity then give J(m)=0. Consequently L(n)=k+L(m), so L(n)>=k, and L(n)=k if and only if every physical n(i) equals one. No coordinatewise positivity was assumed. At k=1, N=1 and the result reads n(0)=1+m(0); at k=2 the unit source values are opposite.")),
                        Paragraph(Text("For a nonunit source the divisibility condition and card(A)<=L(n) are necessary restrictions only. They do not make the endpoint integer-zero, assert a minimum-weight mask is attained by a relation, or realize any ordering in an interval. A closed-walk count vector may use the unit length bound only after an independent telescoping proof of its exact source charge zero. These arithmetic restrictions do not construct a capacity-(N-1)/2 permutation. Damasdi–Frankl–Pach–Palvolgyi, Monochromatic configurations on a circle, arXiv:2504.10687v2, Conjecture 3.1, DOI 10.5070/C6.68671, remains open in its full all-source scope. No literature novelty claim is made."))),
                    DescribeRole.Theorem),
                Describe.Lean(DescribeId.Create("source-zero-subset-count"),
                    DeclarationHandle.Create(Prefix + "zero_subsets_card_le"),
                    H("The source gcd bounds the entire zero fibre"),
                    StatementSource.FromAuthor(Disp(Q(Imp(Le(Num(3), k), bound),
                        ("k", Nat()), ("t", Nat())))),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text("Let k be any natural number at least three, t any natural number, and N=2^k-1. The source is exactly SourceWidth.actualSource: at the physical label p in Fin(k), take the integer centered representative of t times 2^p modulo N. The centered interval is [-floor(N/2),floor(N/2)]. Cyclic doubling supplies these arithmetic residues; the count concerns their exact integer sums. Equal numerical values at different positions remain different labels.")),
                        Paragraph(Text("Write Z for all finsets A of Fin(k) whose source values sum to the integer zero. Thus Z ranges over every physical-label finset satisfying that equality. Then card(Z) is at most gcd(t,N)+1. There is no unit, distinct-value or full-period assumption.")),
                        Paragraph(Text("Encode A by the natural binary mask M(A)=sum over p in A of 2^p. Colexicographic binary-sum injectivity makes M injective on physical subsets. Every mask lies in [0,N], including the empty mask zero and the full mask N. Each centered value is congruent to t times 2^p modulo N. Summing these congruences shows that integer zero forces N to divide t M(A).")),
                        Paragraph(Text("Put g=gcd(t,N) and Q=N/g. Since N is positive, g and Q are positive. Cancel g, then use coprimality of t/g and N/g: Q divides every zero-subset mask. The quotient M(A)/Q is therefore an integer in [0,g]. It still determines A, because multiplication by Q recovers M(A). This injection into g+1 integers proves the bound. The same cancellation includes t=0: g=N and Q=1, so all binary masks remain allowed.")),
                        Paragraph(Text("Mask divisibility is used only as a necessary condition. A mask with Q dividing M(A) need not have exact integer source sum zero: congruence modulo N cannot detect a nonzero multiple of N. The argument counts a superset of the integer-zero fibre and does not replace that fibre by a congruence class."))),
                    DescribeRole.Theorem),
                Describe.Lean(DescribeId.Create("source-zero-block-bound"),
                    DeclarationHandle.Create(Prefix + "disjoint_zero_blocks_bound"),
                    H("Independent zero blocks consume exponentially many masks"),
                    StatementSource.FromAuthor(Disp(Q(Imp(Le(Num(3), k),
                        Imp(blockHyp, Le(Pow(Num(2), Call("card", blocks)), Add(g, Num(1))))),
                        ("k", Nat()), ("t", Nat()), ("blocks", Call("Finset", subsets))))),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text("For every finite family blocks of nonempty, pairwise disjoint physical-label finsets, assume each block has exact integer source sum zero. Then 2 raised to card(blocks) is at most gcd(t,N)+1. The family need not cover all labels; a partition of the entire source is a special case. The empty family is also allowed.")),
                        Paragraph(Text("Every subfamily has a union with exact sum zero, by disjoint-union sum additivity. Distinct subfamilies have distinct unions: choose a label in a block belonging to one subfamily, and disjointness forces any block covering that label in the other subfamily to be the same block. Thus the 2^b subfamilies inject into Z. Combining this injection with the source count gives the restriction.")),
                        Paragraph(Text("For a unit source g=1, this permits at most one nonempty zero block. More generally, any proposed splitting into b independent zero pieces must satisfy the exponential bound, even when source values repeat or have a short period. A construction based on freely choosing arbitrarily many independent integer-zero pieces therefore has an arithmetic obstruction. Existence of such a decomposition is not an assumption about the source in the count theorem.")),
                        Paragraph(Text("The source motivation is Damasdi–Frankl–Pach–Palvolgyi, Monochromatic configurations on a circle, arXiv:2504.10687v2, Conjecture 3.1, DOI 10.5070/C6.68671. These are necessary restrictions on exact zero subsets and decompositions. They do not construct a permutation with every prefix in [0,(N-1)/2]. The full all-source capacity-C conclusion remains open; collective splitting and interleaving with nonzero block charges is not controlled by this count. No claim of literature novelty is made."))),
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
            body = new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(variables[i].Name), variables[i].Domain, body);
        return body;
    }
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Ex(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), domain, body);
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula And(params Formula[] values)
    {
        Formula result = values[^1];
        for (var i = values.Length - 2; i >= 0; i--)
            result = new Formula.Logic(values[i], FormulaLogicOperator.And, result);
        return result;
    }
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(a, b);
}
