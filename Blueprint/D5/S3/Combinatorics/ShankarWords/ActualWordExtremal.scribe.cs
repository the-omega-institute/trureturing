using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.ShankarWords;

internal sealed class ActualWordExtremalDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/ShankarWords/ActualWordExtremal.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Words/shankar2026canon");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Define the original finite carrier for Shankar's 321-avoiding lattice words, "
            + "its strict descent fiber, explicit candidate extremizers, and an all-parameter even construction. The all-k "
            + "maximum and fiber-cardinality law remains unproved.",
        H("Actual lattice-word extremal descent obligation"),
        Blocks(
            Node("IsLattice", "Prefix lattice inequalities",
                "A word is a list of natural numbers. For every prefix length from zero "
                + "through the whole length, the number of ones is at least the number "
                + "of twos, and the number of twos is at least the number of threes."),
            Node("Avoids321", "Subsequence avoidance",
                "For all three strictly increasing positions, the letters cannot be "
                + "3, 2 and 1 in that order. This tests subsequences, not just adjacent triples."),
            Node("IsAdmissible", "The original word conditions",
                "At parameter k, a word has length 3k, uses only the literal letters "
                + "1, 2 and 3, has exactly k copies of each, satisfies every prefix "
                + "inequality, and avoids the subsequence 321. These are the original "
                + "conditions from Shankar's sections 2.2 and 7. No refined counting "
                + "identity is used as a predicate or premise."),
            Node("rawWords", "Complete finite alphabet enumeration",
                "Enumerate every function from Fin(3k) to Fin(3), convert it to a list "
                + "in index order, and add one to each letter value. Thus the encoding "
                + "preserves order and uses 1, 2 and 3, with no quotient by word symmetries."),
            Node("actualWords", "The actual finite carrier",
                "Filter rawWords by IsAdmissible. The scalar closedFormQ in the separate "
                + "Stieltjes refutation is not used to define or count this carrier."),
            Node("descents", "Strict adjacent descent count",
                "Zip a word with its tail and count pairs whose first letter is strictly "
                + "greater than the second. Equal neighboring letters contribute zero. "
                + "Inversions and major index are different statistics."),
            Node("extremalValue", "The proposed maximum",
                "The proposed value is the floor of 3k divided by two, minus one. "
                + "Both division and subtraction are on natural numbers; the target "
                + "law is restricted to k at least two."),
            Node("topFiber", "The actual proposed extremal fiber",
                "Filter actualWords(k) by equality of the strict descent count with "
                + "extremalValue(k). Its size is not defined through the candidate family."),
            Describe.Lean(DescribeId.Create("shankar-extremal-open-law"),
                DeclarationHandle.Create(Prefix + "extremalLaw"),
                H("The exact open extremal obligation"),
                StatementSource.FromAuthor(TargetFormula()),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "The conjunction asks that every actual word lie below the proposed "
                    + "maximum and that the actual fiber have cardinality one for even k "
                    + "and 2k for odd k. For k at least two, either required cardinality "
                    + "is positive, so this also requires attainment. This is an open "
                    + "proposition definition, not a theorem. Neither the universal "
                    + "bound nor the complete fiber classification is proved here. "
                    + "The full coefficient log-concavity and unimodality conjecture "
                    + "also remains open."))), DescribeRole.Definition),
            Node("pairBlocks", "Repeated two-letter blocks",
                "Flatten n copies of the list [a,b]. Each block contributes both letters; "
                + "there is no identification or duplication at a shared boundary."),
            Node("evenWord", "Proposed even extremizer",
                "For k=2t the candidate concatenates t copies of 12, t copies of 13, "
                + "and t copies of 23. For t at least one, the construction theorem proves "
                + "membership in the actual carrier and descent count 3t minus one. "
                + "Global maximality and uniqueness remain open."),
            Describe.Lean(DescribeId.Create("shankar-even-word-construction"),
                DeclarationHandle.Create(Prefix + "even_word_construction"),
                H("Actual even words at the proposed descent level"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "For every natural t at least one, evenWord(t) belongs to actualWords(2t) "
                    + "and its strict adjacent descent count equals extremalValue(2t), namely "
                    + "3t minus one. The proof verifies all prefix cuts, including cuts inside "
                    + "a two-letter block, the equal letter counts, and avoidance of the "
                    + "subsequence 321. It then encodes the word in the complete finite carrier "
                    + "and counts its descending block boundaries. All normalization and "
                    + "carrier lemmas are local to this one content theorem. This establishes "
                    + "attainment of the proposed level for even k; it does not establish a "
                    + "universal upper bound, uniqueness, the odd construction or injectivity, "
                    + "the complete fiber cardinality, or Conjecture 9.3.")))),
            Node("oddOneBase", "Odd descending-pair base",
                "Concatenate t copies of 21, t minus one copies of 31, and t plus one "
                + "copies of 32. The classifier uses t at least one."),
            Node("oddOneWord", "Extra-one odd candidates",
                "Place an initial 1 and a final 3 around oddOneBase. Insert one further "
                + "1 after q complete pairs, where q ranges from zero through 2t minus "
                + "one. This is a proposed parametrization; no injectivity or "
                + "exhaustiveness is assumed."),
            Node("reverseComplement", "Reverse-complement operation",
                "Reverse the list and replace each letter a by 4 minus a. On the "
                + "intended alphabet this exchanges 1 with 3 and fixes 2. The function "
                + "is defined on all natural-number lists; no general preservation "
                + "theorem is asserted for that larger domain."),
            Node("oddTwoWord", "Two extra-two odd candidates",
                "Place an initial 1 and final 3 around t copies each of 21, 31 and 32. "
                + "Insert a single 2 either before or after the block of 31 pairs."),
            Node("OddIndex", "The proposed odd parameter domain",
                "The disjoint sum contains two copies of Fin(2t) and one Bool. "
                + "The size of this parameter domain is not the cardinality of the "
                + "actual maximizer fiber without the missing bijection."),
            Node("oddWord", "Odd candidate encoding",
                "The first Fin(2t) summand selects oddOneWord. The second selects its "
                + "reverse complement. The Bool summand selects oddTwoWord. "
                + "Required but unproved obligations are injectivity, actual "
                + "extremal membership for every parameter, and coverage of every "
                + "actual extremizer."),
            Node("oddCandidates", "Separate candidate image",
                "Take the finite image of oddWord. It remains separate from topFiber. "
                + "The proposed descending-pair route must prove that every extremizer "
                + "has one unpaired interior letter, that its descending pairs occur "
                + "in the order 21 then 31 then 32, and that the prefix and avoidance "
                + "conditions permit exactly these insertion positions. Those "
                + "classification implications are unproved formal obligations."))));

    private static DocumentBlock Node(string name, string title, string prose) =>
        Describe.Lean(DescribeId.Create("shankar-word-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula TargetFormula()
    {
        Formula k = F.Id("k"), w = F.Id("w");
        Formula n = Seq(Mathbb, Grp(F.Id("N")));
        Formula bound = Seq(Forall, Sp, w, InMacro, Sp, Call("actualWords", k), Comma,
            Call("descents", w), Leq, Sp, Call("extremalValue", k));
        Formula count = Seq(Call("card", Call("topFiber", k)), Eq,
            Call("if", Seq(Call("mod", k, D(2)), Eq, D(0)), D(1), Seq(D(2), k)));
        return Disp(Seq(Forall, Sp, k, InMacro, Sp, n, Comma,
            D(2), Leq, Sp, k, Rightarrow, Sp,
            Open, bound, Close, Land, Sp, Open, count, Close));
    }
}
