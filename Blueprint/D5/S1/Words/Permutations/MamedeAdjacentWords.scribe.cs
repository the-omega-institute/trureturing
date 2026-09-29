using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Permutations;

internal sealed class MamedeAdjacentWordsDocument : IScribeDocumentDefinition
{
    private const string Root = "D5/S1/Words/Permutations/MamedeAdjacentWords.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Words/mamede2026commutation");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Adjacent-swap words and the first-orientation source shape.",
        H("Adjacent Words for Conditional Deletion"),
        Blocks(
            Paragraph(Text("Generators are numbered from one. A word is reduced when its "
                + "length is minimal among all valid words for the same permutation. "
                + "A singleton word is also consecutive: adjacent letters differ by one.")),
            Node("adjacent", "Adjacent swap", Disp(Q(Call("adj", V("n"), V("k")), Eq,
                Call("swap", Q(V("k"), Minus, D(1)), V("k")))),
                "On Fin(n+1), generator k swaps one-based positions k and k+1. "
                    + "The definition is total; valid words restrict k to 1 through n.",
                DescribeRole.Definition),
            Node("wordProduct", "Word product", Disp(Q(Call("prod", V("n"), V("w")), Eq,
                Prod, Underscore, Grp(Q(V("k"), InMacro, V("w"))), Call("adj", V("n"), V("k")))),
                "The list product follows the word order and uses right-to-left permutation action.",
                DescribeRole.Definition),
            Node("validWord", "Valid generators", Disp(Q(Call("Valid", V("n"), V("w")), Iff,
                Forall, V("k"), InMacro, V("w"), Comma, D(1), Le, V("k"), Le, V("n"))),
                "Every letter lies between one and n.", DescribeRole.Definition),
            Node("reducedWord", "Reduced word", Disp(Q(Call("Reduced", V("n"), V("w")), Iff,
                Call("Valid", V("n"), V("w")), Land,
                Forall, V("v"), Comma, Call("SameValidProduct", V("n"), V("v"), V("w")),
                Implies, Call("length", V("w")), Le, Call("length", V("v")))),
                "SameValidProduct means that v is valid and has the same product as w. "
                    + "This is global minimality, with no finite search bound.", DescribeRole.Definition),
            Node("consecutive", "Consecutive letters", Disp(Q(Call("Consecutive", V("w")), Iff,
                Forall, Call("neighbors", V("a"), V("b"), V("w")), Comma,
                Q(V("a"), Plus, D(1), Eq, V("b")), Lor,
                Q(V("b"), Plus, D(1), Eq, V("a")))),
                "Every neighboring pair differs by one; empty and singleton lists qualify.",
                DescribeRole.Definition, literature: true),
            Node("oscillation", "Oscillation predicate", Disp(Q(
                Call("Oscillation", V("w")), Iff,
                Call("WeakIncreasing", Call("SegmentLengths", Call("Spikes", V("w")))),
                Lor,
                Call("WeakIncreasing", Call("reverse", Call("SegmentLengths", Call("Spikes", V("w"))))))),
                "Spikes keeps the first and last letters and, in their word order, "
                    + "the internal strict peaks and valleys. SegmentLengths takes "
                    + "the absolute difference of each successive pair of spikes. "
                    + "For consecutive words this is the paper's oscillation condition: "
                    + "the lengths are weakly increasing or weakly decreasing. "
                    + "The predicate also extends to arbitrary lists, including short "
                    + "words with no internal spike.",
                DescribeRole.Definition),
            Node("singletonWord", "Singleton reduced word", Disp(Q(
                Call("Singleton", V("n"), V("sigma"), V("w")), Iff,
                Call("Reduced", V("n"), V("w")), Land,
                Call("Consecutive", V("w")), Land,
                Call("prod", V("n"), V("w")), Eq, V("sigma"))),
                "Singleton is the paper's one-element commutation-class condition "
                    + "expressed using reducedness and consecutive letters.", DescribeRole.Definition,
                literature: true),
            Node("fullExcursion", "Full excursion", Disp(Q(
                Call("Full", V("m"), V("M"), V("i"), V("j")), Eq,
                Call("concat", Call("desc", V("j"), V("m")),
                    Call("asc", Q(V("m"), Plus, D(1)), V("M")),
                    Call("desc", Q(V("M"), Minus, D(1)), V("i"))))),
                "The descending, ascending, descending blocks form the first-orientation excursion.",
                DescribeRole.Definition, literature: true),
            Node("deletedExcursion", "Deleted excursion", Disp(Q(
                Call("Deleted", V("m"), V("M"), V("i")), Eq,
                Call("concat", Call("desc", Q(V("i"), Minus, D(1)), V("m")),
                    Call("asc", Q(V("m"), Plus, D(1)), V("M")),
                    Call("desc", Q(V("M"), Minus, D(1)), V("i"))))),
                "The first descending block begins at i-1 after deletion.",
                DescribeRole.Definition, literature: true),
            Node("imageWord", "Deletion image", Disp(Q(
                Call("Image", V("i"), V("j"), V("p"), V("q")), Eq,
                Call("concat", V("p"), Call("desc", V("j"), V("i")), V("q")))),
                "The target word retains the descending run from j to i.", DescribeRole.Definition,
                literature: true),
            Node("sourceShape", "First-orientation source shape", Disp(Q(
                Call("SourceShape", V("m"), V("M"), V("i"), V("j"),
                    V("a"), V("p"), V("q")), Iff,
                V("a"), Eq, Call("concat", V("p"), Call("Full", V("m"), V("M"), V("i"), V("j")), V("q")),
                Land, Call("PrefixBounds", V("m"), V("j"), V("p")),
                Land, Call("SuffixBounds", V("i"), V("M"), V("q")))),
                "PrefixBounds requires m<k<j for every letter of p; SuffixBounds requires "
                    + "i<k<M for every letter of q. This is a separate premise of the converse.",
                DescribeRole.Definition, literature: true),
            Node("exactSourceHypotheses", "Source permutation hypotheses", Disp(Q(
                Call("ExactSource", V("n"), V("m"), V("M"), V("i"), V("j"), V("sigma")), Iff,
                D(1), Le, V("m"), Lt, V("i"), Le, V("j"), Lt, V("M"), Le, V("n"),
                Land, Call("EndpointValues", V("sigma")),
                Land, Call("ExteriorFixed", V("sigma")),
                Land, Call("NonoscSourceExists", V("sigma")))),
                "EndpointValues says sigma(M+1)=m, sigma(m)=j+1 and sigma(i)=M+1, "
                    + "with sigma(m) different from m and sigma(M+1) different from M+1. "
                    + "ExteriorFixed fixes positions below m and above M+1. "
                    + "NonoscSourceExists asserts a singleton reduced word a for sigma "
                    + "that fails the oscillation test of paper Definition 3.1. "
                    + "The test keeps the first and last letters and the internal strict "
                    + "peaks and valleys, in their word order. For successive entries s,t "
                    + "of this sequence, the segment length is the absolute difference "
                    + "|s-t|, represented on natural numbers by (s-t)+(t-s). "
                    + "A word is oscillating exactly when these lengths are monotone "
                    + "in the broad sense: weakly increasing or weakly decreasing. "
                    + "Thus the existential word a has a length sequence of neither kind. "
                    + "This word need not be the separately supplied shaped singleton a0; "
                    + "NonoscSourceExists does not assert SourceShape for a, and the "
                    + "conditional converse does not require a0 to be nonoscillating. "
                    + "The nonfixed endpoint clauses and NonoscSourceExists are contextual "
                    + "paper hypotheses unused by the two conditional proofs after the "
                    + "actual shaped singleton a0 is supplied; they do not establish "
                    + "SourceShape for that singleton.",
                DescribeRole.Definition))));

    private static DocumentBlock Node(string name, string title, Formula formula,
        string prose, DescribeRole role, bool literature = false) => Describe.Lean(
        DescribeId.Create("mamede-adjacent-" + name.Replace('_', '-').ToLowerInvariant()),
        DeclarationHandle.Create(Root + name), H(title), StatementSource.FromAuthor(formula),
        literature ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(Source),
        Blocks(Paragraph(Text(prose))), role);

    private static Formula Q(params Formula[] items)
    {
        var spaced = new Formula[items.Length * 2 - 1];
        for (var i = 0; i < items.Length; i++)
        {
            spaced[2 * i] = items[i];
            if (i + 1 < items.Length) spaced[2 * i + 1] = Sp;
        }
        return Seq(spaced);
    }

    private static Formula V(string name) => F.Id(name);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Q(Operatorname, Grp(V(name))), [.. args]);
}
