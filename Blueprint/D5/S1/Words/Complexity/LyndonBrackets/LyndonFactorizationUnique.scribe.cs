using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Complexity.LyndonBrackets;

internal sealed class LyndonFactorizationUniqueDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S1/Words/Complexity/LyndonBrackets/LyndonFactorizationUnique";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Words/nilforoushanparvaresh2026kdecks");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A nonincreasing factorization into Lyndon words is unique over any linearly ordered alphabet.",
        H("Uniqueness of Lyndon factorization"),
        Blocks(
            Paragraph(Text(
                "The alphabet A is any linearly ordered type, with no finiteness assumption. "
                + "Words are finite lists, ordered lexicographically. IsLyndon is the existing "
                + "rotation predicate: a word is nonempty and strictly smaller than each rotation "
                + "arising from a split into two nonempty words. Flatten concatenates a list of words. "
                + "LyndonFactors means that every member is Lyndon, and Nonincreasing means "
                + "Pairwise (fun u v => v <= u), so repeated identical factors are permitted. "
                + "Suffix includes the whole word. The uniqueness statement is classical. "
                + "The cited paper states Chen-Fox-Lyndon factorization in Lemma 4.4 for nonempty "
                + "words on a finite ordered alphabet, using the rotation definition in Definition 4.1. "
                + "Its Section 2 assumes a finite alphabet; it does not state an infinite-alphabet theorem.")),
            Paragraph(Text(
                "The arbitrary-alphabet scope follows by finite support. Given two factorizations "
                + "with common concatenation w, every letter of every factor belongs to the finite "
                + "set B of letters occurring in w. Give B the order inherited from A and relabel "
                + "its elements by increasing rank in a finite chain. This injective order-preserving "
                + "relabeling preserves and reflects word equality and lexicographic comparison, "
                + "including the proper-prefix case. It commutes with concatenation and rotation, "
                + "so it preserves and reflects the Lyndon predicate and the nonincrease condition. "
                + "Lemma 4.4 identifies the relabeled factor lists, and injectivity recovers the "
                + "original lists. One may enlarge the finite chain by unused letters if an alphabet "
                + "of at least two symbols is required. If w is empty, nonemptiness of Lyndon factors "
                + "forces both lists to be empty. This transfers the classical uniqueness assertion; "
                + "the Lean proof below works directly in A and does not assume finite support as "
                + "an additional hypothesis or claim mathematical novelty.")),
            Describe.Lean(DescribeId.Create("last-factor-min-suffix"),
                DeclarationHandle.Create(Module + ".last_factor_is_min_nonempty_suffix"),
                H("The final factor is the minimum nonempty suffix"),
                StatementSource.FromAuthor(MinimumFormula()),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "If fs followed by the final factor m is a nonincreasing list of Lyndon words, "
                    + "then m is nonempty, is a suffix of the concatenation, and is no greater than "
                    + "every nonempty suffix of that concatenation. This is the expanded meaning "
                    + "of IsLeast in the Lean statement. Induct on fs. A suffix contained in the "
                    + "remaining concatenation satisfies the induction hypothesis. Any longer suffix "
                    + "has the form t followed by that remaining concatenation, with t a suffix of "
                    + "the first factor u. If t is empty, apply the same induction hypothesis. "
                    + "Otherwise the Lyndon suffix characterization gives u <= t, nonincrease gives "
                    + "m <= u, and extending the prefix t cannot decrease it in lexicographic order."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("nonincreasing-lyndon-unique"),
                DeclarationHandle.Create(Module + ".nonincreasing_lyndon_factorization_unique"),
                H("Equal concatenations have equal factor lists"),
                StatementSource.FromAuthor(UniquenessFormula()),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "For any two finite lists fs and gs, if every factor in each list is Lyndon, "
                    + "each list is nonincreasing, and their concatenations agree, then fs = gs. "
                    + "There is no assumption on the factor counts or factor lengths. "
                    + "For nonempty factorizations the minimum-suffix theorem makes both final "
                    + "factors the least element of the same set, so antisymmetry identifies them. "
                    + "Cancel this common final word and apply induction to the remaining lists. "
                    + "An empty concatenation has no nonempty Lyndon factors, which supplies "
                    + "the empty-list cases. The result includes singleton words, repeated factors, "
                    + "and finite words on infinite alphabets. It asserts uniqueness, independently "
                    + "of any procedure constructing a factorization."))),
                DescribeRole.Theorem))));

    private static Formula MinimumFormula()
    {
        Formula fs = F.Id("fs"), m = F.Id("m"), s = F.Id("s");
        Formula factors = Call("append", fs, Call("singleton", m));
        Formula word = Call("flatten", factors);
        return Disp(Alphabet(All("fs", Words(), All("m", Word(), Seq(
            Call("LyndonFactors", factors), Land, Sp,
            Call("Nonincreasing", factors), Rightarrow, Sp,
            m, Neq, Sp, Call("nil"), Land, Sp, Call("Suffix", m, word), Land, Sp,
            All("s", Word(), Seq(s, Neq, Sp, Call("nil"), Land, Sp,
                Call("Suffix", s, word), Rightarrow, Sp, m, Leq, Sp, s)))))));
    }

    private static Formula UniquenessFormula()
    {
        Formula fs = F.Id("fs"), gs = F.Id("gs");
        return Disp(Alphabet(All("fs", Words(), All("gs", Words(), Seq(
            Call("LyndonFactors", fs), Land, Sp, Call("Nonincreasing", fs), Land, Sp,
            Call("LyndonFactors", gs), Land, Sp, Call("Nonincreasing", gs), Land, Sp,
            Equal(Call("flatten", fs), Call("flatten", gs)), Rightarrow, Sp,
            Equal(fs, gs))))));
    }

    private static Formula Alphabet(Formula body) => All("A", F.Id("Type"),
        Seq(OpenBracket, Call("LinearOrder", F.Id("A")), CloseBracket, Sp, body));
    private static Formula Word() => Call("List", F.Id("A"));
    private static Formula Words() => Call("List", Word());
    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
}
