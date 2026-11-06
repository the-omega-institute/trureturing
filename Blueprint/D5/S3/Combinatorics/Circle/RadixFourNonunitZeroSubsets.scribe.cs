using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Circle;

internal sealed class RadixFourNonunitZeroSubsetsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Circle/RadixFourNonunitZeroSubsets.";

    public DocumentDefinition Create()
    {
        Formula n = V("n"), B = V("B"), i = V("i"), A = V("A");
        Formula r = Mul(Num(2), n), N = Sub(Pow(Num(2), r), Num(1));
        Formula digits = Call("Fin", n), labels = Call("Fin", r);
        Formula subsets = Call("Finset", labels), supports = Call("Finset", digits);
        Formula seed = Call("radixSeed", B);
        Formula even = Call("evenLabel", i);
        Formula empty = Call("empty", labels), full = Call("univ", labels);
        Formula source(Formula t, Formula p) => Call("actualSource", r, t, p);
        Formula sum(Formula t) => Call("sum", A, Call("actualSource", r, t));
        Formula evenSum(Formula t) => Call("sum", Call("univ", digits),
            Call("lambda", i, source(t, even)));
        Formula count(Formula t) => Call("card", Call("filter", Call("univ", subsets),
            Call("lambda", A, Eq(sum(t), Num(0)))));
        Formula ends = Or(Eq(A, empty), Eq(A, full));
        Formula gcd(Formula t) => Eq(Call("gcd", t, N), Num(3));
        Formula positive = Lt(Num(0), n), nonempty = Call("Nonempty", B);
        Formula general(Formula body, bool needsGcd = false) => Q(
            Imp(needsGcd ? And(positive, nonempty, gcd(seed)) : And(positive, nonempty), body),
            ("n", Nat()), ("B", supports));
        Formula allPositive(Formula t) => Q(Lt(Num(0), source(t, even)), ("i", digits));
        Formula allZeros(Formula t) => Q(Iff(Eq(sum(t), Num(0)), ends), ("A", subsets));
        Formula family = Q(Imp(And(Le(Num(3), n), Not(Call("dvd", Num(3), n))), And(
            gcd(Num(21)), gcd(Num(3)), allPositive(Num(21)),
            Eq(evenSum(Num(21)), N), allZeros(Num(21)),
            Eq(count(Num(21)), Num(2)), Eq(count(Num(3)), Num(4)))), ("n", Nat()));
        return DocumentDefinition.Create(ScribeNode.Create(
            "Prepared, uncompiled source: actual radix-four digit rotation gives positivity and an integral trace, then exact gcd three forces only empty/full physical zero subsets; an infinite seed21 family has the same gcd as seed3 and a different zero count.",
            H("Radix-four rotation and nonunit physical additive geometry"),
            Blocks(
                Paragraph(Text("Preparation status: neither this Scribe nor the associated Lean source has been compiled in this stage. The declarations are proof scripts for later guarded integration, not a kernel acceptance claim. No completed GPT Pro agreement has been received or used. The in-flight Pro answer, request, status and logs were excluded. No literature-novelty claim is made.")),
                Node("seed", "Radix-four-supported seeds", "radixSeed",
                    Q(Eq(seed, Call("sum", B, Call("lambda", V("j"),
                        Pow(Num(4), Call("val", V("j")))))), ("n", Nat()), ("B", supports)),
                    "For a finset B of Fin(n), t_B is the natural sum of 4^j over j in B. There is one actual zero-or-one digit at each radix-four position. The general theorems require only n>0 and B nonempty before the explicitly stated gcd hypothesis; no ordering, unit, width, distinct-value or orbit-period assumption is imposed.",
                    DescribeRole.Definition),
                Node("even-label", "The actual even physical label", "evenLabel",
                    Q(Eq(Call("val", even), Mul(Num(2), Call("val", i))),
                        ("n", Nat()), ("i", digits)),
                    "evenLabel(i) is the Fin(2*n) label with value 2*i.val. It is an injection into the original full physical label type; repeated numerical source values remain separate labelled occurrences.",
                    DescribeRole.Definition),
                Node("even-half", "The even physical half", "evenLabels",
                    Q(Eq(Call("evenLabels", n),
                        Call("image", Call("evenLabel"), Call("univ", digits))), ("n", Nat())),
                    "The even half E is the image of all Fin(n) under evenLabel. Its complement consists of exactly the odd labels, since every natural label below 2*n has parity zero or one. Its binary mask is Q=sum_j<n 4^j=(2^(2*n)-1)/3; the complement mask is 2Q. These are masks of actual physical subsets, not replacement source definitions.",
                    DescribeRole.Definition),
                Node("even-positive", "Every actual even occurrence is positive", "actual_even_pos",
                    general(allPositive(seed)),
                    "For i,j in Fin(n), finCycle(i)(j) has value (j+i) mod n. The proof establishes 4^((j+i) mod n) congruent to 4^i*4^j modulo N by splitting at the single possible wrap and using 4^n=2^(2*n)=N+1. Summing over B gives the actual residue of 2^(2*i)*t_B. Rotation is a permutation, so this positive natural representative R_i is at most Q. Since N=3Q and Q>0, R_i lies in the integer centered interval. SourceWidth.centered_unique identifies R_i with the actualSource value, proving strict positivity at every even label. The modular congruence and the centered integer equality are separate proof steps.",
                    DescribeRole.Theorem),
                Node("even-trace", "The complete integral even-label trace", "actual_even_trace",
                    general(Eq(Mul(Num(3), evenSum(seed)), Mul(Call("card", B), N))),
                    "For each fixed support digit j, varying i over Fin(n) visits every radix-four position exactly once. Interchanging the two finite sums therefore gives sum_i R_i=card(B)*Q. Multiplication by three gives the exact integer trace 3*sum_i actualSource(2*n,t_B,2*i)=card(B)*N. All n rotations are counted even when the seed has a shorter orbit; no distinct-residue assumption or division of orbit multiplicities is used.",
                    DescribeRole.Theorem),
                Node("zero-iff", "All physical zero subsets at exact gcd three", "actual_zero_iff",
                    general(allZeros(seed), true),
                    "Assume additionally gcd(t_B,N)=3, and let A be any finset of Fin(2*n). Existing ZeroSumSubsets.zero_mask_dvd first gives N divides t_B*mask(A); its quotient_dvd cancels the exact gcd to give Q divides mask(A). The existing injective binary mask is bounded between zero and N=3Q. Thus only masks 0,Q,2Q,3Q remain, identifying A as empty, the even half, its odd complement, or the full set. Strict positivity of all actual even labels excludes the even half. ZeroSumSubsets.source_cycle gives the full physical sum zero; complement additivity then excludes the odd half. Empty and full are explicitly proved zero. This is an integer-zero statement on every physical subset, not merely a congruence classification and not a conclusion assumed as a hypothesis.",
                    DescribeRole.Theorem),
                Node("count", "Exactly two physical zero subsets", "actual_zero_subsets_card",
                    general(Eq(count(seed), Num(2)), true),
                    "The classification identifies the filtered finset of all physical zero subsets with the two-element finset containing empty and univ. Positivity of n makes the complete label type inhabited, so these endpoints are distinct. The theorem includes n=1 and all nonempty B when the stated exact gcd holds; there is no hidden n>=3 restriction in the general result.",
                    DescribeRole.Theorem),
                Node("gcd21", "The exact arithmetic boundary for seed21", "seed21_gcd",
                    Q(Eq(Call("gcd", Num(21), N), Call("ite", Call("dvd", Num(3), n),
                        Num(21), Num(3))), ("n", Nat())),
                    "For every natural n, gcd(21,4^n-1) is 21 when 3 divides n and 3 otherwise. If 3 divides n, 4^3-1=63 divides 4^n-1 and hence 21 divides it. Otherwise primality of 3 gives gcd(3,n)=1. Every common divisor of 21 and 4^n-1 divides both 63 and 4^n-1, hence divides 4^gcd(3,n)-1=3 by the existing power-minus-one gcd theorem. Conversely 3 divides both numbers. The n=0 arithmetic boundary is included.",
                    DescribeRole.Theorem),
                Node("separation", "An infinite same-gcd separation of additive geometry", "seed21_separation",
                    family,
                    "For every n>=3 with 3 not dividing n, take B={0,1,2}, so t_B=1+4+16=21 and card(B)=3. The general positivity, trace, zero classification and count are used on the live proof path: the even sum is N and seed21 has exactly two physical zero subsets. Seed3 has the same exact gcd three. The sealed TwoBitZeroSubsets.actual_zero_subsets_card at a=1 yields exactly four zero subsets on the same full Fin(2*n) labels. The parameters n=3*k+4, k natural, are distinct, unbounded and satisfy the hypotheses, giving infinitely many separations.",
                    DescribeRole.Theorem),
                Paragraph(Text("Arithmetic orbit invariants and physical additive relations must be distinguished. Equal gcd describes cancellation of seed returns and the candidate binary masks allowed by divisibility; it does not identify which candidates have integer sum zero. In the three-digit radix-four family the even candidate has positive trace and the odd one negative trace. For seed3 the two-bit theorem supplies both extra zeros. Cyclic rotation of subsets is an action on a powerset; multiplication by two on a seed in ZMod(N) is a different action.")),
                Paragraph(Text("Original-target residual: for r=2*n>=8 and n not divisible by three, establish the common exact modular seed period r for seeds 3 and 21. The sealed PowerQuotientOrder.power_quotient_order with u=2,a=1,k=n supplies orderOf(2 in ZMod(N/3))=r after exact parameter normalization. What is still missing here is a proved seed-return bridge (2^e*t=t mod N iff N/3 divides 2^e-1), using exact gcd cancellation for t=3,21, including e=0 and the natural-subtraction/cast boundary, followed by the exact dynamics/minimalPeriod identification. This period statement is not asserted by the same-gcd separation theorem.")),
                Paragraph(Text("Integration remains with the caller: the visibility-only patch exposes only mask_injective, mask_bound, mask_full, zero_mask_dvd and quotient_dvd, without copying or changing their proofs. Its actual consumers are the even/odd binary-mask calculation and the four-candidate zero-mask classification in this module. The separate sealed TwoBit consumer patch removes exactly these five names from open private, retaining its two still-private helpers and all proof bodies. Later integration must recheck all consumers against the canonical source, perform guarded Lean/kernel and accepted-axiom checks, bind and audit any required Reg mirror, use the canonical pin writer for visibility changes, and complete normal freeze/CI/review/delivery. No such binding, kernel, audit, pin or delivery result is claimed by this preparation."))), []));
    }

    private static DocumentBlock Node(string id, string title, string declaration,
        Formula formula, string prose, DescribeRole role) => Describe.Lean(
            DescribeId.Create("radix-four-" + id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
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
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula Or(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Or, b);
    private static Formula Not(Formula a) => Imp(a, Name("False"));
    private static Formula And(params Formula[] values)
    {
        Formula result = values[^1];
        for (var i = values.Length - 2; i >= 0; i--)
            result = new Formula.Logic(values[i], FormulaLogicOperator.And, result);
        return result;
    }
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(a, b);
}
