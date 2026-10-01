using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic;

internal sealed class ParityLiftRationalMinimumDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciAtomic/ParityLiftRationalMinimum.";
    private static Formula V(string name) => F.Id(name);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(name))), [.. args]);
    private static Formula Par(Formula body) => Seq(Open, body, Close);
    private static Formula EqOf(Formula a, Formula b) => Seq(a, Sp, Eq, Sp, b);
    private static Formula LeOf(Formula a, Formula b) => Seq(a, Sp, Leq, Sp, b);
    private static Formula Imp(Formula a, Formula b) => Seq(Par(a), Sp, Implies, Sp, Par(b));
    private static Formula All(string name, Formula body) => Seq(Forall, Sp, V(name), Comma, Sp, body);
    private static Formula And(params Formula[] clauses)
    {
        var items = new List<Formula>();
        foreach (var clause in clauses)
        {
            if (items.Count > 0) items.AddRange([Sp, Land, Sp, RowBreak]);
            items.Add(Par(clause));
        }
        return Seq([.. items]);
    }
    private static DocumentBlock Definition(string name, string title, string prose) => Describe.Lean(
        DescribeId.Create("parity-lift-" + name.ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name), H(title), StatementSource.WithoutFormula(),
        AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The five-window parity task, lifted to rational outputs, has minimum linear dimension four.",
        H("Minimum Rational Dimension of the Fibonacci Parity Lift"),
        Blocks(
            Paragraph(Text("The five windows null, [2], [3], [25], [5] have printed bits 000, 100, "
                + "010, 101, 001, respectively. Words arrive high to low. A seam records the low bit "
                + "of the previous higher window; it cannot be one when the new window's high bit "
                + "is one. The unit bit is zero. Empty words, leading null windows and all finite "
                + "prefixes belong to the task, and an illegal seam remains an absorbing error.")),
            Definition("WordRepresentation", "Linear representations of words", "Over a field K, "
                + "a representation consists of a K-vector space V, a designated initial vector, "
                + "a linear endomorphism for each letter and a linear output map to a K-vector "
                + "space Y. No reachability or observability hypothesis is imposed. The dimension "
                + "of a finite-dimensional representation is dim_K(V)."),
            Definition("wordMap", "Chronological products", "The empty word acts by the identity. "
                + "For a word beginning with a letter b and followed by w, the operator is the "
                + "operator for w composed with the operator for b. Thus letters act in input order."),
            Definition("wordBehavior", "Full word responses", "The behavior of R "
                + "on w is its output map applied to the word operator acting on its initial vector. "
                + "R realizes a task when these responses agree on every finite word."),
            Describe.Lean(DescribeId.Create("word-map-concatenation"),
                DeclarationHandle.Create(Prefix + "word_map_append"), H("Composition of chronological products"),
                StatementSource.FromAuthor(Disp(All("T", All("u", All("w",
                    EqOf(Call("wordMap", V("T"), Call("concat", V("u"), V("w"))),
                        Call("compose", Call("wordMap", V("T"), V("w")),
                            Call("wordMap", V("T"), V("u"))))))))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("For any field K, "
                    + "alphabet and K-vector space V, T assigns a linear endomorphism to each "
                    + "letter. For finite words u and w, concat(u,w) is their concatenation, "
                    + "and compose(A,B) applies B first and A second. The chronological operator "
                    + "of a concatenation applies the prefix operator before the suffix operator."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("actual-response-minor-lower-bound"),
                DeclarationHandle.Create(Prefix + "response_minor_le_finrank"), H("Actual response rank bounds dimension"),
                StatementSource.FromAuthor(Disp(All("K", All("R", All("f", All("pre", All("suf", All("select",
                    Imp(And(Call("Realizes", V("R"), V("f")), Call("Nonsingular", V("M"))),
                        LeOf(V("n"), Call("dimK", V("V")))))))))))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("K is any field, V "
                    + "is a finite-dimensional K-vector space, Y is any K-vector space and R "
                    + "is a linear word representation on V with output in Y. The task f maps "
                    + "finite words to Y. The families pre and suf contain n actual prefixes "
                    + "and suffixes; select contains n K-linear scalar observations on Y. "
                    + "M(i,j)=select(i)(f(concat(pre(j),suf(i)))). Nonsingular(M) means its "
                    + "determinant is nonzero. If R realizes f on every finite word, its reached "
                    + "prefix vectors map linearly to the columns of M. Independence of these "
                    + "columns forces independence of the n reached vectors and n<=dim_K(V)."))),
                DescribeRole.Theorem),
            Definition("parityEncode", "Rational encoding after reduction", "An error maps to "
                + "(0,0). A residue b in ZMod(2) maps to (1,val(b)), where val(b) is the standard "
                + "representative zero or one, then embedded into the rational numbers."),
            Definition("parityTask", "The rational parity task", "g(w) applies parityEncode to "
                + "the immediate mod-two Fibonacci quantity task. Legal zero quantity yields "
                + "(1,0), distinct from error. This encoding takes the residue representative before "
                + "passing to rational coordinates."),
            Definition("integerTask", "The integer response", "Apply the existing immediate "
                + "quantity reader at modulus zero, whose carrier ZMod(0) is Z. A legal quantity "
                + "q yields (1,q) in Z^2, and an illegal word yields (0,0). This response is computed "
                + "before a coefficient field is selected."),
            Definition("integerFieldTask", "Natural change of coefficient field", "For any field "
                + "K, f_K applies the natural map from Z to K to both coordinates of integerTask. "
                + "It retains the legality coordinate separately from quantity."),
            Definition("integerRationalTask", "The integer-induced rational task", "f_Q(w) "
                + "starts with seam zero and integer composition (0,0). A legal final composition "
                + "(a,b) yields (1,2a+3b) in Q^2. Error yields (0,0). No mod-two reduction is taken."),
            Definition("BlockState", "Two homogeneous seam blocks", "V=Q^4 has coordinates "
                + "(b_0,c_0,b_1,c_1). An actual legal state occupies only its current seam block "
                + "with c=1 and b in {0,1}; error is the zero vector."),
            Definition("blockUpdate", "Linear parity flips and seam routing", "Null and [2] "
                + "preserve parity, while [3], [25] and [5] flip it using J(b,c)=(c-b,c). Allowed "
                + "source blocks are sent to the new seam, with contributions added when both "
                + "source blocks have the same destination. Disallowed blocks map to zero. "
                + "These formulas define linear maps on all of Q^4."),
            Definition("blockTransition", "The letter operators", "Each blockUpdate is regarded "
                + "as a rational linear endomorphism of the four-dimensional state space."),
            Definition("blockOutput", "Two output channels", "The output is (c_0+c_1,b_0+b_1)."),
            Definition("fourDimensional", "The initialized four-dimensional representation", "The "
                + "initial vector is (0,1,0,0), each letter uses blockTransition, and the output is "
                + "blockOutput."),
            Definition("embed", "Actual mod-two states", "Embed a legal mod-two raw state by "
                + "retaining the standard representative of its second composition coordinate in "
                + "its seam block, with homogeneous coordinate one. Embed error as zero."),
            Definition("prefixes", "Four actual histories", "The histories are the empty word, "
                + "[3], [2], and [3][2], in that order."),
            Definition("suffixes", "Actual continuation tests", "The four row tests use [5], "
                + "[5], null[5], null[5], respectively."),
            Definition("selectOutput", "Scalar row observations", "Rows zero and two observe "
                + "legality, the first output coordinate. Rows one and three observe parity, the "
                + "second output coordinate."),
            Definition("responseMinor", "The actual response matrix", "The entry in row i and "
                + "column j is the selected scalar response of g to prefix j followed by suffix i. "
                + "Denote this fixed matrix by H. Its rows are (1,1,0,0), (1,0,0,0), (1,1,1,1), (1,0,1,0); its determinant is one."),
            Describe.Lean(DescribeId.Create("parity-lift-exact-minimum"),
                DeclarationHandle.Create(Prefix + "result"), H("Attained minimum dimension four"),
                StatementSource.FromAuthor(ResultFormula()), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Here F denotes fourDimensional, g denotes parityTask, and "
                        + "f_Q denotes integerRationalTask. Q4 denotes BlockState=Q^4, word3 denotes "
                        + "the singleton word [3], and pair(a,b) denotes the ordered output pair. "
                        + "Realizes(R,g) means equality on every "
                        + "finite word. V ranges over all finite-dimensional rational vector spaces, "
                        + "and R ranges over all rational linear word representations on V with "
                        + "outputs in Q^2. No bound on word length is imposed.")),
                    Paragraph(Text("Embedding the actual mod-two state commutes with every letter "
                        + "operator. Word induction therefore identifies the four-dimensional "
                        + "representation with g on every finite input, including error continuations. "
                        + "The parity flip uses ordinary rational subtraction on Boolean states; "
                        + "it does not identify the rational field with a field of characteristic two.")),
                    Paragraph(Text("For any representation R that realizes g, let its four reached "
                        + "prefix vectors be P_j. Continuing a vector by each suffix and selecting "
                        + "the specified output coordinate defines a linear observation O into Q^4. "
                        + "Chronological composition and equality of all word responses give "
                        + "O(P_j) equal to column j of the actual response matrix. The determinant "
                        + "one makes these columns linearly independent, so the four P_j are "
                        + "linearly independent in V. Thus every such V has dimension at least four.")),
                    Paragraph(Text("The four-dimensional representation attains this lower bound. "
                        + "On [3], the parity lift is (1,1), while the integer-induced rational "
                        + "task is (1,3). Their coefficient carrier is the same, but their complete "
                        + "word response tasks differ."))), DescribeRole.Theorem))));

    private static Formula ResultFormula() => Disp(And(
        Call("Realizes", V("F"), V("g")),
        EqOf(Call("dim", V("Q4")), D(4)),
        All("V", All("R", Imp(And(Call("FiniteQSpace", V("V")),
            Call("LinearWordRep", V("R"), V("V"))),
            Imp(Call("Realizes", V("R"), V("g")), LeOf(D(4), Call("dim", V("V"))))))),
        EqOf(Call("g", V("word3")), Call("pair", D(1), D(1))),
        EqOf(Call("fQ", V("word3")), Call("pair", D(1), D(3))),
        EqOf(V("responseMinor"), V("H")),
        EqOf(Call("det", V("responseMinor")), D(1))));
}
