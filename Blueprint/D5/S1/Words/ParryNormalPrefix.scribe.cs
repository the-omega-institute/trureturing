using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words;

internal sealed class ParryNormalPrefixDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An ordered greedy cut theorem for zero-run substitutions with dominant zero images.",
        H("Greedy Remainders and Ordered Image Prefixes"),
        Blocks(
            Paragraph(Text("Let A be any alphabet, let z be a letter, and let f map letters to finite "
                + "ordered lists. Extend f to lists by concatenation and let I(k,a) be its kth "
                + "iterate on the singleton a, with I(0,a) equal to [a]. Put F(k)=length(I(k,z)). "
                + "The substitution has the form f(a)=z repeated digit(a) times, followed by the "
                + "optional successor next(a). A missing successor permits the terminal image "
                + "of a simple Parry substitution; a successor can also return to an earlier "
                + "state, as in a non-simple Parry substitution.")),
            Paragraph(Text("Assume F(k) is positive and length(I(k,a)) is at most F(k) for every "
                + "natural k and every letter a. These are explicit hypotheses. No relation "
                + "between a greedy expansion and a word prefix is assumed.")),
            Describe.Lean(DescribeId.Create("word-power"),
                DeclarationHandle.Create("D5/S1/Words/ParryNormalPrefix.wordPower"),
                H("Finite concatenation power"), StatementSource.FromAuthor(Disp(
                    Eq(Call("wordPower", F.Id("w"), F.Id("d")),
                        Call("flatten", Call("replicate", F.Id("d"), F.Id("w")))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("wordPower(w,d) concatenates d copies of w. The zeroth "
                    + "power is the empty list, and the order within every copy is preserved. "
                    + "This is the concatenation power of "), Ref("D5/S1/Words/Powers/WordPower"),
                    Text(" with the word argument first here. Its length is d times length(w)."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("greedy-blocks"),
                DeclarationHandle.Create("D5/S1/Words/ParryNormalPrefix.greedyBlocks"),
                H("Blocks from every greedy step"), StatementSource.FromAuthor(Disp(
                    Eq(Call("greedyBlocks", F.Id("f"), F.Id("z"),
                        Add(F.Id("k"), D(1)), F.Id("n")),
                        Call("append", Call("wordPower", Call("I", F.Id("k"), F.Id("z")),
                            Call("div", F.Id("n"), Call("F", F.Id("k")))),
                            Call("greedyBlocks", F.Id("f"), F.Id("z"), F.Id("k"),
                                Call("mod", F.Id("n"), Call("F", F.Id("k")))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("greedyBlocks(f,z,0,n) is the empty list. With count k+1, "
                    + "append n div F(k) copies of I(k,z), then recurse at count k with n mod "
                    + "F(k). Thus count N+1 includes all image exponents from N down through "
                    + "zero. A zero quotient contributes an empty block without ending the "
                    + "recursion. The chosen height is an input; it need not be minimal."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("greedy-remainder-prefix"),
                DeclarationHandle.Create("D5/S1/Words/ParryNormalPrefix.greedy_remainder_prefix"),
                H("All proper image prefixes are reconstructed in order"),
                StatementSource.FromAuthor(Disp(Statement())), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("At the next iterate, the actual image is digit(a) copies "
                        + "of I(k,z), followed by the image of the optional successor. The latter "
                        + "has length at most F(k). A proper cut therefore has quotient at most "
                        + "digit(a). If the quotient is smaller, its remainder lies strictly "
                        + "inside a zero-image block. If it equals digit(a), the remainder lies "
                        + "strictly inside the successor image. Induction applies to the actual "
                        + "letter in either branch, proving equality of complete ordered lists.")),
                    Paragraph(Text("The empty prefix is included. At exponent zero the only "
                        + "proper cut of [a] has length zero. To apply the theorem to a normal "
                        + "representation at height N, use k=N+1, a=z and n<F(N+1). Passing "
                        + "from the finite iterate to the infinite fixed word additionally "
                        + "requires its exact prefix compatibility.")),
                    Paragraph(Text("Turek, Abelian complexity and Abelian co-decomposition, "
                        + "Proposition 2.7 and Section 2.2, https://arxiv.org/pdf/1201.2109v1, "
                        + "give the full known Parry-word reconstruction result, including "
                        + "leading zero padding. The theorem here isolates its ordered cut "
                        + "mechanism. Deriving the required dominance from the full Parry "
                        + "admissibility conditions, and constructing the compatible fixed "
                        + "word for both substitution families, remain separate requirements. "
                        + "The displayed exponent bounds in Turek (6) alone are not substituted "
                        + "for those admissibility conditions."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("successor-dominated"),
                DeclarationHandle.Create("D5/S1/Words/ParryNormalPrefix.SuccessorDominated"),
                H("Finite lexicographic successor windows"),
                StatementSource.FromAuthor(Disp(DominanceFormula())), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For each letter a and each window length k, compare "
                    + "c(s iterated i times on a) with c(s iterated i times on z), for i below k. "
                    + "Either every pair agrees, or there is a first differing position q below "
                    + "k at which the digit from a is smaller. Equality of entire successor "
                    + "streams is allowed."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("greedy-prefix-successor-dominance"),
                DeclarationHandle.Create("D5/S1/Words/ParryNormalPrefix.greedy_prefix_of_successor_dominance"),
                H("Successor digits determine the ordered greedy prefix"),
                StatementSource.FromAuthor(Disp(SuccessorStatement())), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Here every literal image has the form z repeated c(a) "
                        + "times followed by the actual letter s(a). Positivity follows from "
                        + "this last letter. If two successor windows agree, their equal "
                        + "weighted contributions cancel, leaving equal singleton lengths at "
                        + "depth zero. At the first differing digit, one root-image weight "
                        + "bounds the entire remaining smaller-side image by strong induction "
                        + "at a lower depth. The larger-side remaining image is positive. Thus "
                        + "every image length is bounded by the root-image length, which "
                        + "permits the ordered greedy cut theorem to apply.")),
                    Paragraph(Text("For a simple Parry substitution, its last literal image "
                        + "z repeated t_m times can be written as z repeated t_m minus one "
                        + "times followed by z. This distinguishes a final actual letter "
                        + "without changing the substitution. For a non-simple substitution "
                        + "the successor is already the final letter, including its cyclic "
                        + "return. The theorem proves reconstruction from SuccessorDominated; "
                        + "the conversion of full Parry admissibility to this condition and "
                        + "the infinite fixed-word construction are separate obligations.")),
                    Paragraph(Text("The full source target is the following known result: for "
                        + "either Parry substitution family, its actual fixed word u, every "
                        + "positive n, and every N with n<F(N+1), the normal greedy digits "
                        + "d_N through d_0 reconstruct the ordered prefix u[n] as I(N,0) "
                        + "repeated d_N times, then I(N-1,0) repeated d_(N-1) times, down "
                        + "through the letter zero repeated d_0 times. Leading zero padding "
                        + "and N=0 are included. The finite-image theorems here do not yet "
                        + "establish this full statement.")),
                    Paragraph(Text("The association uses the actual Renyi expansion D=d_beta(1) "
                        + "for beta>1, not just bounds on individual exponents. Every positive "
                        + "shift of D is strictly lexicographically smaller than D. In the "
                        + "simple case D=t_1...t_m followed by zeros, with t_m positive; in "
                        + "the non-simple case D=t_1...t_m(t_(m+1)...t_(m+p)) repeated "
                        + "periodically, with a positive digit in the period and minimal "
                        + "preperiod and period. In both cases the substitution exponent "
                        + "at state i is t_(i+1); the last state terminates in the simple "
                        + "case and returns to state m in the non-simple case. These "
                        + "definitions and the shift condition are stated in Frougny, "
                        + "Masakova and Pelantova, Infinite special branches in words "
                        + "associated with beta-expansions, pp.129-130, "
                        + "https://doi.org/10.46298/dmtcs.415. Its later assumption that all "
                        + "digits are positive is not imposed here. For the simple final-letter "
                        + "presentation, the modified root successor stream is periodic, "
                        + "so equality with a shift must be allowed in SuccessorDominated. "
                        + "The exact bridge from these source expansions to that finite-window "
                        + "condition remains unproved.")),
                    Paragraph(Text("Digitwise exponent bounds alone do not give the needed "
                        + "condition. For the simple-shaped substitution 0 maps to 001, 1 to "
                        + "2, 2 to 003, and 3 to 00, all exponents are at most two and the last "
                        + "exponent is positive. Its root-image lengths start 1,3,7,17,42. "
                        + "At n=41 and height N=3 the greedy digits are 2,1,0,0. The actual "
                        + "length-41 prefix of the fourth iterate ends in zero, whereas the "
                        + "reconstruction ends in two. This substitution fails full Parry "
                        + "admissibility and does not contradict Proposition 2.7."))),
                DescribeRole.Theorem))));

    private static Formula Statement()
    {
        var a = F.Id("a"); var k = F.Id("k"); var n = F.Id("n"); var z = F.Id("z");
        var f = F.Id("f"); var digit = F.Id("digit"); var next = F.Id("next");
        Formula I(Formula j, Formula b) => Call("image", f, j, b);
        Formula L(Formula w) => Call("length", w);
        var shape = All("a", F.Id("A"), Eq(Call("f", a),
            Call("append", Call("replicate", Call("digit", a), z), Call("toList", Call("next", a)))));
        var positive = All("k", N(), Lt(D(0), L(I(k,z))));
        var dominant = All("k", N(), All("a", F.Id("A"), Leq(L(I(k,a)), L(I(k,z)))));
        var result = All("k", N(), All("a", F.Id("A"), All("n", N(),
            Imp(Lt(n,L(I(k,a))), Eq(Call("take", n,I(k,a)), Call("greedyBlocks",f,z,k,n))))));
        return All("A", F.Id("Type"), All("f", Call("Morphism", F.Id("A")),
            All("z", F.Id("A"), All("digit", Call("DigitMap", F.Id("A")),
                All("next", Call("OptionalSuccessor", F.Id("A")),
                    Imp(And(shape, And(positive, dominant)), result))))));
    }
    private static Formula DominanceFormula()
    {
        var a = F.Id("a"); var k = F.Id("k"); var i = F.Id("i"); var q = F.Id("q");
        Formula Digit(Formula j, Formula b) => Call("c", Call("iterate", F.Id("s"), j, b));
        Formula Agree(Formula bound) => All("i", N(), Imp(Lt(i,bound), Eq(Digit(i,a),Digit(i,F.Id("z")))));
        var mismatch = new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create("q"), N(),
            And(Lt(q,k), And(Agree(q),Lt(Digit(q,a),Digit(q,F.Id("z"))))));
        return All("a", F.Id("A"), All("k", N(),
            new Formula.Logic(Agree(k),FormulaLogicOperator.Or,mismatch)));
    }
    private static Formula SuccessorStatement()
    {
        var f=F.Id("f"); var z=F.Id("z"); var c=F.Id("c"); var s=F.Id("s");
        var k=F.Id("k"); var a=F.Id("a"); var n=F.Id("n");
        var image=Call("image",f,k,a);
        var shape=All("a",F.Id("A"),Eq(Call("f",a),
            Call("append",Call("replicate",Call("c",a),z),Call("singleton",Call("s",a)))));
        var conclusion=All("k",N(),All("a",F.Id("A"),All("n",N(),
            Imp(Lt(n,Call("length",image)),Eq(Call("take",n,image),Call("greedyBlocks",f,z,k,n))))));
        return All("A",F.Id("Type"),All("f",Call("Morphism",F.Id("A")),All("z",F.Id("A"),
            All("c",Call("DigitMap",F.Id("A")),All("s",Call("Successor",F.Id("A")),
                Imp(And(shape,Call("SuccessorDominated",c,s,z)),conclusion))))));
    }
    private static Formula N() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(F.Id(name), [.. args]);
    private static Formula All(string x, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(x), domain, body);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Leq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
}
