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
        return DocumentDefinition.Create(ScribeNode.Create(
            "Binary masks restrict how many exact integer-zero subsets and independent zero blocks an actual centered doubling source can have.",
            H("Zero subsets of the physical circle source"),
            Blocks(
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
