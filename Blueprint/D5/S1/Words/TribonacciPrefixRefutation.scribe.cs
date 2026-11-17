using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words;

internal sealed class TribonacciPrefixRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Words/TribonacciPrefixRefutation.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Explicit prefixes of the literal Tribonacci word have quadratic alternating charge in the substitution level and refute a uniform logarithmic interval bound.",
        H("Quadratic Prefix Charge in the Literal Tribonacci Word"),
        Blocks(
            Paragraph(Text("The letters A, B and C are 0, 1 and 2 in Fin 3. The substitution is exactly A to AB, B to AC and C to A. W is the closed A-starting infinite word from TribonacciAlignedWindows, with its actual letters identified with finite substitution iterates by MBonacciSentinelDesubstitution.word_eq_iterate. All positions, lengths and levels are natural numbers; positions start at zero.")),
            Node("tau", "fourth-iterate", "Four substitution steps", DescribeRole.Definition,
                All("x", Call("Fin", D(3)), Eq(Call("tau", F.Id("x")),
                    Call("image", F.Id("sigma"), D(4), F.Id("x")))),
                "Write tau=sigma^4, so tau^n(x)=image sigma (4n) x. The literal images are tau(A)=ABACABAABACAB, tau(B)=ABACABAABAC and tau(C)=ABACABA. Their lengths are 13, 11 and 7. In particular tau(A)=tau(C) followed by A and BACAB."),
            Node("weight", "letter-weights", "Integer letter weights", DescribeRole.Definition,
                Conj(Eq(Call("weight", D(0)), D(2)), Eq(Call("weight", D(1)), D(1)),
                    Eq(Call("weight", D(2)), D(0))),
                "The weights are exactly A=2, B=1 and C=0, with values in the integers."),
            Node("signedWordSum", "local-sign", "Alternating charge from the local start", DescribeRole.Definition,
                All("v", Call("List", Call("Fin", D(3))),
                    Eq(Call("signedWordSum", F.Id("v")),
                        Call("alternatingSum", Call("map", F.Id("weight"), F.Id("v"))))),
                "For v of length m this is the sum of (-1)^i times weight(v[i]) over 0<=i<m. The sign starts positive at the beginning of v, independently of its position in W. The empty sum is zero. Mathlib's alternatingSum_append gives F(uv)=F(u)-F(v) whenever u has odd length."),
            Paragraph(Text("TribonacciAlignedWindows.four_parity supplies odd length for every tau^n letter image. Thus substitution of such blocks preserves the alternating pattern of the original letters. Put a_n=F(tau^n(A)), b_n=F(tau^n(B)) and c_n=F(tau^n(C)). Expanding the three literal images gives (a_0,b_0,c_0)=(2,1,0) and (a_(n+1),b_(n+1),c_(n+1))=(a_n,2a_n-b_n,4a_n-2b_n-c_n). Induction gives a_n=2, b_n=2-(-1)^n and c_n=2-(2n+2)(-1)^n. These are identities at every natural level.")),
            Node("prefixWord", "recursive-prefix", "The actual recursive prefix family", DescribeRole.Definition,
                Conj(Eq(Call("prefixWord", D(0)), Call("nil")),
                    All("n", Nat(), Eq(Call("prefixWord", Add(F.Id("n"), D(1))),
                        Call("append", Call("image", F.Id("sigma"), Mul(D(4), Add(F.Id("n"), D(1))), D(2)),
                            Call("prefixWord", F.Id("n")))))),
                "Denote prefixWord(n) by U_n. Thus U_0 is empty and U_(n+1)=tau^(n+1)(C) U_n; the new block is prepended. The decomposition tau^(n+1)(A)=tau^(n+1)(C) tau^n(A) tau^n(BACAB) proves inductively that U_n is a literal prefix of tau^n(A). This is a prefix assertion about the original substitution, without an assumed occurrence hypothesis."),
            Node("prefixLength", "prefix-length", "Prefix lengths", DescribeRole.Definition,
                All("n", Nat(), Eq(Call("prefixLength", F.Id("n")),
                    Call("length", Call("prefixWord", F.Id("n"))))),
                "Let m_n=length(U_n). Each letter image is nonempty, so m_n>0 for n>=1. Each of the three fourth images has length at most 13; induction bounds the length of tau^n(A) by 13^n. Prefix containment therefore gives 0<m_n<=13^n for n>=1. Applying MBonacciSentinelDesubstitution.factor_of_prefix directly to that containment, at order 3 and iterate 4n, gives the exact identity factor W 0 m_n=U_n."),
            Node("prefixCharge", "prefix-charge", "Charge of the prefix family", DescribeRole.Definition,
                All("n", Nat(), Eq(Call("prefixCharge", F.Id("n")),
                    Call("signedWordSum", Call("prefixWord", F.Id("n"))))),
                "Write q_n=F(U_n). Oddness of the prepended block gives q_0=0 and q_(n+1)=c_(n+1)-q_n. Substituting the formula for c_n and inducting yields q_n=1-(-1)^n(n^2+3n+1). For even positive n its absolute value is n^2+3n; for odd n it is n^2+3n+2. Hence |q_n|>=n^2, including n=0."),
            Node("claim", "uniform-logarithmic-claim", "The exact uniform interval claim", DescribeRole.Definition,
                Claim(),
                "The constant K is real and strictly positive. Both s and m range over all natural numbers, including m=0. factor W s m consists of W(s),...,W(s+m-1). The integer charge is coerced to a real number before taking its absolute value. The logarithm is the natural real logarithm of the real coercion of m plus 2. There are no unmentioned lower cutoffs or restrictions on the interval start."),
            Node("result", "refutation", "Failure of every positive logarithmic constant", DescribeRole.Theorem,
                new Formula.Not(F.Id("claim")),
                "The exact negation of claim holds. For each K>0, the contradiction already occurs at s=0 and m=m_n for a sufficiently large positive level n. The result is about the closed word W and the stated weights, without free word, parity or occurrence assumptions."),
            Paragraph(Text("For n>=1, the elementary bound 13^n+2<=39^n gives log(m_n+2)<=n log(39). Choose a natural n>K log(39); positivity of K log(39) ensures n>=1. Then n^2>K n log(39)>=K log(m_n+2), whereas the actual prefix identity and charge formula give |F(factor W 0 m_n)|>=n^2. This contradicts the claimed bound for that interval. The argument covers every positive real K and all substitution levels needed for the construction; finite examples do not replace the induction.")),
            Paragraph(Text("Adamczewski, Symbolic discrepancy and self-similar dynamics, Annales de l'Institut Fourier 54 (2004), DOI 10.5802/aif.2079, provides general background on discrepancy for substitutions. Its existential weight lower bounds are not used as a theorem for these particular weights or this parity construction. The proof uses the literal word and concatenation identities instead. No optimal upper bound, spectral gap, entropy estimate or literature novelty assertion is part of this conclusion.")))));

    private static DocumentBlock Node(string name, string id, string title, DescribeRole role,
        Formula statement, string prose) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(F.Disp(statement)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);

    private static Formula Claim()
    {
        Formula k = F.Id("K"), s = F.Id("s"), m = F.Id("m");
        Formula bound = Le(Call("abs", Call("real", Call("signedWordSum", Call("factor", F.Id("W"), s, m)))),
            Mul(k, Call("log", Add(Call("real", m), D(2)))));
        return new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create("K"), Real(),
            Conj(Lt(D(0), k), All("s", Nat(), All("m", Nat(), bound))));
    }

    private static Formula Nat() => F.Seq(F.Mathbb, F.Grp(F.Id("N")));
    private static Formula Real() => F.Seq(F.Mathbb, F.Grp(F.Id("R")));
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(F.Id(name), [.. args]);
    private static Formula All(string name, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Conj(params Formula[] items)
    {
        Formula result = items[^1];
        for (int i = items.Length - 2; i >= 0; --i)
            result = new Formula.Logic(items[i], FormulaLogicOperator.And, result);
        return result;
    }
}
