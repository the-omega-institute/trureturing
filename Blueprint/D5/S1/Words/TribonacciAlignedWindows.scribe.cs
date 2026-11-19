using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words;

internal sealed class TribonacciAlignedWindowsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Words/TribonacciAlignedWindows.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual Tribonacci word contains uniformly large odd repetition windows at even starts in all sufficiently long even substitution prefixes.",
        H("Aligned Repetition Windows in the Tribonacci Word"),
        Blocks(
            Paragraph(Text("The alphabet is Fin 3. Letters A, B and C mean 0, 1 and 2, respectively. All indices and lengths below are natural numbers, and the first letter has index zero.")),
            Node("sigma", "sigma", "The literal substitution", DescribeRole.Definition,
                Conj(Eq(Call("sigma", D(0)), Call("List", D(0), D(1))),
                    Eq(Call("sigma", D(1)), Call("List", D(0), D(2))),
                    Eq(Call("sigma", D(2)), Call("List", D(0)))),
                "The substitution is exactly A to AB, B to AC and C to A. It is the order-three instance of phi in MBonacciSentinelDesubstitution."),
            Node("W", "word", "The closed infinite word", DescribeRole.Definition,
                All("n", Eq(Call("W", F.Id("n")), Call("word", D(3), F.Id("n")))),
                "W is the actual closed word supplied by MBonacciSentinelDesubstitution.word at order three. Its nth letter is read from the (n+1)st iterate on A. Nested, unbounded iterates make this reading agree with every sufficiently long finite iterate. No occurrence or recurrence hypothesis is assumed."),
            Node("L", "iterate-length", "Actual iterate lengths", DescribeRole.Definition,
                All("j", Eq(Call("L", F.Id("j")),
                    Call("length", Call("image", F.Id("sigma"), F.Id("j"), D(0))))),
                "L(j) is the length of the actual jth substitution iterate on A, including L(0)=1. The generic image function uses identity at level zero and literal substitution at each successor."),
            Node("N", "even-length", "Rounding to an even prefix", DescribeRole.Definition,
                All("j", Eq(Call("N", F.Id("j")),
                    Mul(D(2), Call("natDiv", Call("L", F.Id("j")), D(2))))),
                "N(j)=2 times the natural quotient L(j)/2. It is the greatest even natural not exceeding L(j); at most one final letter is removed."),
            Node("aligned_windows", "aligned-windows", "A uniform repetition event", DescribeRole.Theorem,
                Event(),
                "There are positive natural constants K and J, with J at least one, such that every j at least J admits natural m and s. The block length m is odd and at least three, s is even, N(j) is at most K times m, and s+2m is at most N(j). Every natural i less than m-1 satisfies literal equality W(s+i+m)=W(s+i). The constants are independent of j and of every hopping parameter."),
            Paragraph(Text("One may take K=128 and J=4. Write q as the natural quotient (j-4)/4 and k=4q, so k+4 is at most j and j is at most k+7. The fourth iterate on A is ABAC followed by ABA, ABA and CAB. Apply k substitutions to all four pieces. The two images of ABA coincide literally. The starting prefix has length 2 times the A-image length plus the B- and C-image lengths; each repeated block has length 2 times the A-image length plus the B-image length.")),
            Paragraph(Text("At every level divisible by four all three letter-image lengths are odd. This follows by induction from the explicit fourth images, of lengths 13, 11 and 7. Consequently the starting prefix has even length and the repeated block has odd length. All letter images are nonempty, so the repeated block has at least three letters and the terminal image of CAB leaves a nonempty suffix. Removing at most one final letter therefore preserves the whole square. Each substitution increases length by at most a factor of two, and seven successive steps give the factor 128. The repeated block contains the kth A-image, which supplies the comparison with N(j).")),
            Paragraph(Text("For a hopping model encoded by this actual word, the conclusion supplies the odd length, even start, literal repetition, proportional scale and containment needed to select a finite inverse-matrix window. The matrix theorem odd_square_inverse_paired_mass is a downstream algebraic supplier; it does not supply these word occurrences. Embedding that window into the full physical-prefix inverse, controlling the resulting norm and spectrum, and deriving the entropy conclusion remain separate unproved interfaces. No global spectral or entropy conclusion follows here.")))));

    private static DocumentBlock Node(string name, string id, string title, DescribeRole role,
        Formula statement, string prose) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(F.Disp(statement)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);

    private static Formula Event()
    {
        Formula k = F.Id("K"), j = F.Id("j"), threshold = F.Id("J");
        Formula m = F.Id("m"), s = F.Id("s"), i = F.Id("i");
        return Ex("K", Conj(Lt(D(0), k), Ex("J", Conj(Le(D(1), threshold),
            All("j", Imp(Le(threshold, j), Ex("m", Ex("s", Conj(
                Le(D(3), m), Call("Odd", m), Call("Even", s),
                Le(Call("N", j), Mul(k, m)), Le(Add(s, Mul(D(2), m)), Call("N", j)),
                All("i", Imp(Lt(i, Sub(m, D(1))),
                    Eq(Call("W", Add(Add(s, i), m)), Call("W", Add(s, i))))))))))))));
    }

    private static Formula Nat() => F.Seq(F.Mathbb, F.Grp(F.Id("N")));
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(F.Id(name), [.. args]);
    private static Formula All(string name, Formula body) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), Nat(), body);
    private static Formula Ex(string name, Formula body) => new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), Nat(), body);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Conj(params Formula[] items)
    {
        Formula result = items[^1];
        for (int i = items.Length - 2; i >= 0; --i)
            result = new Formula.Logic(items[i], FormulaLogicOperator.And, result);
        return result;
    }
}
