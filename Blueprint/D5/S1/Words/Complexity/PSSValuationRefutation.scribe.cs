using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Complexity;

internal sealed class PSSValuationRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Words/Complexity/PSSValuationRefutation.";
    private const string Note = "D5/L/Combinatorics/popolishallitstipulanti2024additive";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A single ternary infinite word has fewer additive classes than original-symbol "
            + "abelian classes at some positive length for every natural valuation.",
        H("Natural Valuations Cannot Preserve Every Abelian Complexity Function"),
        Blocks(
            Paragraph(Text(
                "An alphabet A is finite, and an infinite word is a function from Nat to A. "
                + "A length-n factor starting at i is the function j ↦ w(i+j), for j in Fin n. "
                + "The existing wordFactorSet is the finite subset of all functions Fin n → A "
                + "which occur at natural starting indices. Thus only ordinary contiguous "
                + "factors of the same one-sided infinite word are counted.")),
            Definition("parikh", "Original-symbol Parikh vectors",
                All("A", F.Id("Type"), All("u", Call("List", A), All("a", A,
                    Equal(Call("parikh", U, F.Id("a")), Call("count", F.Id("a"), U))))),
                "Section 2 defines the Parikh vector by its letter counts. Its coordinates "
                + "are indexed by the original letters, even when two letters receive equal "
                + "weights. List.perm_iff_count identifies equality of these vectors with "
                + "permutation of the words, exactly the source's abelian equivalence."),
            Definition("weightedSum", "Natural evaluation of a Parikh vector",
                FiniteAlphabet(All("v", Valuation, All("p", Valuation,
                    Equal(Call("weightedSum", V, F.Id("p")),
                        Seq(Sum, Underscore, Grp(Seq(F.Id("a"), InMacro, Sp, A)), Sp,
                            Call("v", F.Id("a")), Cdot, Call("p", F.Id("a"))))))),
                "A valuation is any map v : A → Nat. The evaluation is the sum of v(a)p(a) "
                + "over the finite alphabet. Induction on a list and the count-cons identity "
                + "give sum(map v u) = weightedSum v (parikh u). No injectivity or positivity "
                + "of v is required."),
            Definition("parikhSet", "Actual factor Parikh vectors",
                WordLength(Equal(Call("parikhSet", W, N),
                    Call("image", Seq(F.Id("parikh"), Circ, F.Id("ofFn")), Factors))),
                "The image of the finite factor set under parikh ∘ List.ofFn is a Finset. "
                + "Every member is the Parikh vector of an actual length-n factor, and every "
                + "such vector is included. Equal vectors are counted once."),
            Definition("abelianComplexity", "Abelian complexity on the original alphabet",
                WordLength(Equal(Call("abelianComplexity", W, N),
                    Call("card", Call("parikhSet", W, N)))),
                "This is the number of distinct original-symbol Parikh vectors. It equals "
                + "the number of abelian equivalence classes of the factors by the count "
                + "characterization of List.Perm."),
            Definition("sumSet", "Actual weighted factor sums",
                WordLength(All("v", Valuation, Equal(Call("sumSet", W, V, N),
                    Seq(OpenBrace, Call("sum", Call("map", V, Call("ofFn", U))), Sp,
                        Mid, Sp, U, Sp, InMacro, Sp, Factors, CloseBrace)))),
                "The sums are taken over exactly the same actual factor set. Their Finset "
                + "is also the image of parikhSet under weightedSum v, by the list-sum identity "
                + "and Finset.image_image. Consequently additive equivalence classes are "
                + "exactly the fibers of the weighted-sum map on original-symbol classes."),
            Definition("additiveComplexity", "Additive complexity under a valuation",
                WordLength(All("v", Valuation,
                    Equal(Call("additiveComplexity", W, V, N),
                        Call("card", Call("sumSet", W, V, N))))),
                "The additive complexity is the number of these distinct sums, as in "
                + "Definitions 1 and 3. All counted collections are finite images of the finite "
                + "set of functions Fin n → A. At n = 0 the unique empty factor gives the "
                + "zero Parikh vector and the zero sum, so both complexities are one."),
            Definition("claim", "The full valuation-existence question",
                Equivalent(F.Id("claim"), FiniteAlphabet(All("w", Word,
                    Ex("v", Valuation, All("n", Nat,
                        Equal(Call("additiveComplexity", W, V, N),
                            Call("abelianComplexity", W, N))))))),
                "Question 31 in arXiv:2410.02409v1, Section 5, PDF page 15, asks: "
                + "\"Given an alphabet A, is there a valuation such that the additive complexity "
                + "of a given sequence is equal to its abelian complexity?\" The same question "
                + "is HTML Section 4 Question 30 and official FSTTCS Question 31. The closed "
                + "proposition quantifies over every finite alphabet A : Type, every infinite "
                + "word, and a natural valuation whose equality holds at every natural length. "
                + "Finite sets are represented by their finite types; no global recurrence, "
                + "automaticity, morphicity or balancedness hypothesis is present."),
            Describe.Lean(DescribeId.Create("universalword"),
                DeclarationHandle.Create(Prefix + "universalWord"),
                H("A fixed ternary infinite word"),
                StatementSource.FromAuthor(Disp(All("i", Nat,
                    Equal(Call("universalWord", F.Id("i")),
                        Call("getD", Call("block", Call("K", F.Id("i"))),
                            Seq(F.Id("i"), Minus, Call("B", Call("K", F.Id("i")))), D(0)))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text(
                    "Decode k as a finite list over Fin 3 using the existing Encodable "
                    + "instance, using [] when decoding fails, and append [0] to obtain block k. "
                    + "Put B(0)=0 and B(k+1)=B(k)+length(block k). Every block is nonempty, "
                    + "so B is strictly increasing and B(k) ≥ k. Let K(i) be the least k with "
                    + "i < B(k+1). The displayed definition selects the letter at offset i-B(k) "
                    + "of that block; getD uses the displayed zero as its default. At every "
                    + "offset j below the block length, the least-boundary property yields "
                    + "universalWord(B(k)+j)=block(k)[j]. Decoding encode(u) returns u, so "
                    + "every finite ternary list u occurs contiguously at B(encode(u)). The "
                    + "same function universalWord is fixed before any valuation is chosen."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("result"), DeclarationHandle.Create(Prefix + "result"),
                H("A negative answer to the entire valuation-existence assertion"),
                StatementSource.FromAuthor(Disp(Seq(Neg, F.Id("claim")))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(
                    Paragraph(Text(
                        "Fix universalWord. For any valuation put a=v(0), b=v(1), c=v(2). "
                        + "If a=b=c, the two singleton factors [0] and [1] have different Parikh "
                        + "vectors and equal weighted sums at length one. Otherwise the two "
                        + "actual factors 0^b 1^c 2^a and 0^c 1^a 2^b have the same positive "
                        + "length a+b+c. Their Parikh vectors are (b,c,a) and (c,a,b). Equality "
                        + "would force a=b=c, while their weighted sums are always equal by "
                        + "commutativity of multiplication.")),
                    Paragraph(Text(
                        "Both factors occur in the fixed word by its decoded-block construction. "
                        + "Hence weightedSum is noninjective on the finite Parikh set at that "
                        + "same length. Finset.card_image_le and Finset.card_image_iff imply "
                        + "that its image has strictly smaller cardinality. This proves that for "
                        + "every natural valuation v there exists n>0 with additiveComplexity "
                        + "universalWord v n < abelianComplexity universalWord n, contradicting "
                        + "the valuation supplied by claim for A=Fin 3 and this one fixed word. "
                        + "Zero and repeated weights are included. The obstruction uses "
                        + "unbounded factor counts; it imposes no additional restriction on "
                        + "the question and does not contradict the source's positive results "
                        + "for explicitly balanced or specially structured words."))),
                DescribeRole.Theorem))));

    private static DocumentBlock Definition(string name, string title, Formula formula, string text) =>
        Describe.Lean(DescribeId.Create(name.ToLowerInvariant()), DeclarationHandle.Create(Prefix + name),
            H(title), StatementSource.FromAuthor(Disp(formula)),
            AssessedProvenance.FromLiterature(LibraryNoteRef.Create(Note)),
            Blocks(Paragraph(Text(text))), DescribeRole.Definition);

    private static Formula Nat => F.Id("Nat");
    private static Formula A => F.Id("A");
    private static Formula U => F.Id("u");
    private static Formula W => F.Id("w");
    private static Formula V => F.Id("v");
    private static Formula N => F.Id("n");
    private static Formula Valuation => new Formula.TypeArrow(A, Nat);
    private static Formula Word => new Formula.TypeArrow(Nat, A);
    private static Formula Factors => Call("wordFactorSet", W, N);
    private static Formula FiniteAlphabet(Formula body) =>
        All("A", F.Id("Type"), All("h", Call("Fintype", A), body));
    private static Formula WordLength(Formula body) =>
        FiniteAlphabet(All("w", Word, All("n", Nat, body)));
    private static Formula Call(string name, params Formula[] args) =>
        args.Length == 0 ? F.Id(name) : new Formula.Apply(F.Id(name), [.. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Ex(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Equal(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Equivalent(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Iff, b);
}
