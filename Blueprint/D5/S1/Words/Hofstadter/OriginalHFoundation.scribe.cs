using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Hofstadter;

internal sealed class OriginalHFoundationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Words/Hofstadter/OriginalHFoundation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Words/letouzeylisteiner2024pointwise");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The original Hofstadter H is exactly the complement of the number of letters 1 in every prefix of the original ternary fixed word.",
        H("The original H and its morphic word"),
        Blocks(
            Paragraph(Text("The cited source defines H(0)=0 and H(n+1)=n+1-H(H(H(n))). Its Theorem 3.1 and Proposition 4.1 relate it to the substitution 1 to 2, 2 to 3, and 3 to 31. The three nested applications, the initial value, the original letters and the initial letter 3 are retained here.")),
            Def("Letter", "Original letters", "Letter has exactly the three constructors one, two and three, representing the source labels 1, 2 and 3 in that order. These are letters, not values of H."),
            Def("tau", "Original substitution", "tau maps one to the singleton two, two to the singleton three, and three to the two-letter list three, one. Its extension to finite words is the existing polymorphic substitution subst, which concatenates the letter images in order."),
            Def("block", "Literal iterates", "For every natural k, block k is the literal list tau iterated k times on the singleton three, using the existing polymorphic image operation. In particular block 0 is the singleton three."),
            Def("wordPrefix", "All finite prefixes", "For every infinite word x : Nat to Letter and natural n, wordPrefix x n is the list x(0),...,x(n-1), in increasing position order. Its length is n, and wordPrefix x 0 is empty."),
            Def("IsOriginalWord", "Literal infinite fixed-word condition", "For every x : Nat to Letter, IsOriginalWord x means both x(0)=three and the following condition for every natural n: subst tau (wordPrefix x n) equals wordPrefix x of length (subst tau (wordPrefix x n)).length. Thus the substitution of every finite prefix is the corresponding finite prefix of the same infinite word. No supplied infinite word is assumed to exist."),
            Def("word", "The constructed infinite word", "For every natural n, word n is the letter at index n of block n, with three as the total default. The growth and agreement theorem ensures that this index is in range and that the default is never used. This construction uses only the original literal substitution iterates."),
            Def("IsOriginalH", "The original numerical equations", "For every f : Nat to Nat, IsOriginalH f means f(0)=0 and, for every natural n, f(n+1)=n+1-f(f(f(n))). All arguments and subtraction are natural numbers. There are exactly three nested applications."),
            Def("H", "Independent numerical realization", "For every natural n, H n is eval n n. The structurally recursive auxiliary eval has eval 0 m=0 and eval (p+1) m=m-eval p (eval p (eval p (m-1))). Each auxiliary value is at most its argument. The coherence proof shows that two depths p and q at least m give the same value at m. H is constructed independently of word and all letter counts."),
            Def("positive", "Complementary prefix count", "For every finite word w, positive w counts its letters different from one, using List.countP. Consequently positive w plus List.count one w equals the length of w."),
            Proof("h_characterization", "Existence and uniqueness of the original H", "The conjunction has two clauses: IsOriginalH H, and for every f : Nat to Nat, IsOriginalH f implies f=H. The first clause verifies both H(0)=0 and H(n+1)=n+1-H(H(H(n))) for every natural n. The second clause is equality of total functions, proved by strong induction using H(n) at most n at every nested argument. Thus the numerical equations have an actual, unique realization."),
            Proof("word_characterization", "Existence, uniqueness and arbitrary prefix coverage", "Four clauses hold simultaneously. First, IsOriginalWord word. Second, for every x : Nat to Letter, IsOriginalWord x implies x=word. Third, for every natural k, k+1 is at most the length of block k. Fourth, for all natural n and k, n at most the length of block k implies wordPrefix word n=(block k).take n. In particular all natural prefix lengths occur, and equality is allowed at every whole-block endpoint. The proof uses block(k+1)=block(k) followed by the nonempty k-th iterate of the letter one. Nesting and growth identify the finite iterates with the literal rooted infinite fixed word."),
            Proof("original_h_morphic_prefix", "Exact original prefix-count correspondence", "For every infinite word x : Nat to Letter, every proof hx of IsOriginalWord x, and every natural n, H(n)+List.count one (wordPrefix x n)=n. Equivalently H(n)=n-List.count one (wordPrefix x n). This includes n=0 and every whole-block endpoint, without a finite-horizon or a sufficiently-long-block premise. The word characterization supplies an actual x, and the numerical characterization identifies this H with every function satisfying the original triple recurrence."),
            Paragraph(Text("To see the correspondence, write P(n) for positive(wordPrefix word n). For an arbitrary finite word w and natural cut n in its substituted word v, put r=positive(v.take n). The number of letters three in v.take n equals positive(w.take r), and the number of letters one in v.take(n+1) equals the number of letters three in w.take r. These identities hold also when a cut is inside the image 31, at a whole-block boundary, at zero, or beyond the finite word. They follow by splitting the three original letter images. Prefix agreement transfers them to P(P(n))=countThree(wordPrefix word n) and countOne(wordPrefix word(n+1))=countThree(wordPrefix word(P(n))). It follows that P(P(P(n)))=countOne(wordPrefix word(n+1)), and the complementary count gives the original triple recurrence for P. Numerical uniqueness then gives P=H.")),
            Paragraph(Text("The numerical characterization and prefix-count correspondence are known mathematical results. The canonical Library note supplies their precise locators and the author's public-domain Coq source. The numerical depth construction follows GenG.v; the arbitrary-cut counting argument proves the morphic bridge here. External source code supplies mathematical guidance; the Lean proofs establish the statements here. No mathematical novelty is asserted.")),
            Paragraph(Text("These statements concern exact natural-number values and word prefixes. They give no machine execution, input acquisition, serialization, bit-operation count, memory bound, frequency limit, or quantitative automaton lower bound.")))));

    private static DocumentBlock Def(string name, string title, string prose) =>
        Node(name, title, prose, DescribeRole.Definition);

    private static DocumentBlock Proof(string name, string title, string prose) =>
        Node(name, title, prose, DescribeRole.Theorem);

    private static DocumentBlock Node(string name, string title, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.WithoutFormula(),
            name is "tau" or "block" or "IsOriginalH" or "H" or "h_characterization" or "original_h_morphic_prefix"
                ? AssessedProvenance.FromLiterature(Source)
                : AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role);
}
