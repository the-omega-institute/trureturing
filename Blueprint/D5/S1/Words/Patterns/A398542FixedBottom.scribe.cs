using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Patterns;

internal sealed class A398542FixedBottomDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Words/Patterns/A398542FixedBottom.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Words/norton2026a398542");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual fixed-bottom permutations and their exact gap configurations.",
        H("Actual objects for the A398542 fixed-bottom conjecture"),
        Blocks(
            Paragraph(Text(
                "The source is OEIS A398542, revision 18, August 30, 2026. "
                + "Perm(n) means bijections of Fin(n), with zero-based values; adding one "
                + "recovers the source alphabet 1,...,n. Contains is the existing generic "
                + "classical containment predicate. All sizes in the semantic constructions "
                + "are natural numbers, including zero. The eventual polynomial theorem "
                + "requires m>=1. The new Library note records the exact source formula "
                + "and the bounded literature comparison.")),
            Node("pattern132", "The literal pattern 132",
                "The permutation of Fin(3) with values [0,2,1]. This is the source's "
                + "132 pattern after subtracting one from every value.", source: true),
            Node("pattern213", "The literal pattern 213",
                "The permutation of Fin(3) with values [1,0,2], representing the source's "
                + "upper-cell forbidden pattern 213.", source: true),
            Node("pattern1324", "The literal pattern 1324",
                "The permutation of Fin(4) with values [0,2,1,3], representing the "
                + "forbidden pattern in the complete source permutation.", source: true),
            Node("lowerWord", "The literal lower-value word",
                "For every m,k and w in Perm(m+k), read the values of w in increasing "
                + "position order and retain exactly those less than m. The result is "
                + "a list of natural numbers; it retains actual values, not just ranks.", source: true),
            Node("upperWord", "The standardized upper-value word",
                "For every m,k and w in Perm(m+k), read w in position order, retain "
                + "exactly the values at least m, and subtract m from each retained value. "
                + "This is a list over 0,...,k-1.", source: true),
            Node("lowerValues", "Values on lower positions",
                "For w in Perm(m+k), lowerValues is an equivalence from positions i "
                + "satisfying w(i)<m to Fin(m). Its forward map is w(i), and its inverse "
                + "is the position w inverse at the same lower value."),
            Node("upperValues", "Values on upper positions",
                "For w in Perm(m+k), upperValues is an equivalence from positions i "
                + "satisfying not w(i)<m to Fin(k). It sends i to w(i)-m; its inverse "
                + "sends j to the position of value m+j."),
            Node("lowerOrder", "Increasing lower-position enumeration",
                "For every w in Perm(m+k), lowerOrder is the increasing order isomorphism "
                + "from Fin(m) to the subtype of positions with values below m. The "
                + "cardinality equality is supplied by lowerValues."),
            Node("upperOrder", "Increasing upper-position enumeration",
                "For every w in Perm(m+k), upperOrder is the increasing order isomorphism "
                + "from Fin(k) to positions with values at least m, using upperValues "
                + "for their cardinality."),
            Node("lowerPerm", "The actual lower permutation",
                "For every w in Perm(m+k), compose lowerOrder with lowerValues to obtain "
                + "a permutation of Fin(m). Its values are precisely lowerWord(w) in "
                + "position order."),
            Node("upperPerm", "The actual standardized upper permutation",
                "For every w in Perm(m+k), compose upperOrder with upperValues to obtain "
                + "a permutation of Fin(k). It reads the upper cell in position order "
                + "and subtracts the fixed value cut m."),
            Node("Shuffle", "An ordered interleaving",
                "For all m,k, Shuffle(m,k) consists of an equivalence from the disjoint "
                + "sum Fin(m) plus Fin(k) to Fin(m+k), strictly increasing on each "
                + "summand separately. Both summands may be empty."),
            Node("extractShuffle", "Extract the two ordered position sets",
                "For every w in Perm(m+k), extractShuffle(w) combines lowerOrder and "
                + "upperOrder into the common position set, retaining the order within "
                + "each cell."),
            Node("insert", "Insert the two actual value blocks",
                "For b in Perm(m), u in Perm(k), and s in Shuffle(m,k), insert(b,u,s) "
                + "is the permutation whose value at s(lower i) is b(i), and whose "
                + "value at s(upper j) is m+u(j). The shuffle determines positions only."),
            Node("insertionEquiv", "Mutually inverse insertion and extraction",
                "For every m,k, insertionEquiv is an equivalence from "
                + "(Perm(m) times Perm(k)) times Shuffle(m,k) to Perm(m+k). The forward "
                + "map inserts both cells; the inverse returns lowerPerm, upperPerm "
                + "and extractShuffle. Both composites are identities, including "
                + "empty cells. The increasing lower and upper enumerations recover "
                + "the original positions and actual values."),
            Node("gap", "The number of preceding lower positions",
                "For s in Shuffle(m,k) and upper index j in Fin(k), gap(s,j) in "
                + "Fin(m+1) is the cardinality of lower indices i with "
                + "s(lower i)<s(upper j)."),
            Node("gap_spec", "Exact gap order and position recovery",
                "For every m,k and s in Shuffle(m,k), gap(s) is weakly increasing; "
                + "for all lower i and upper j, s(lower i)<s(upper j) if and only if "
                + "i<gap(s,j); and for every upper j, the natural position "
                + "s(upper j) equals gap(s,j)+j. Equal consecutive gaps are permitted. "
                + "The proof identifies each lower prefix by its finite cardinality.",
                DescribeRole.Theorem),
            Node("shuffleOfGaps", "Reconstruct an ordered shuffle",
                "For every weakly increasing g:Fin(k)->Fin(m+1), shuffleOfGaps(g) "
                + "constructs a Shuffle(m,k). Its upper positions are g(j)+j; its "
                + "lower positions fill the complement in increasing order."),
            Node("gapEquiv", "Shuffles are exactly weakly increasing gaps",
                "For all natural m,k, gapEquiv is an equivalence between Shuffle(m,k) "
                + "and the subtype of weakly increasing functions Fin(k)->Fin(m+1). "
                + "It uses gap and shuffleOfGaps, with both inverse laws."),
            Node("prefixMin", "A total prefix minimum",
                "For every b in Perm(m) and natural g, prefixMin(b,g) is the minimum "
                + "of {m} together with all b(i) for i in Fin(m) satisfying i<g. "
                + "In particular the empty prefix has value m."),
            Node("dead", "The first forbidden later endpoint",
                "For every b in Perm(m) and natural g, dead(b,g) is the minimum of "
                + "{m+2} together with all j+1 for j in Fin(m) satisfying g<=j and "
                + "prefixMin(b,g)<b(j). The endpoint uses the source's one-based "
                + "bottom convention; m+2 is the sentinel when no endpoint exists."),
            Node("contains1324_iff_mixed", "The exact mixed-pattern obstruction",
                "For every w in Perm(m+k), assume lowerPerm(w) avoids 132 and "
                + "upperPerm(w) avoids 213. Then w contains 1324 if and only if there "
                + "are positions a<x<c<y with w(a),w(c)<m, m<=w(x),w(y), "
                + "w(a)<w(c), and w(x)<w(y). Every other distribution of a forbidden "
                + "occurrence between the cells would contain one of the excluded "
                + "cell patterns. The interleaved-ascent criterion is an existing "
                + "ingredient in the domino literature cited by the source audit.",
                DescribeRole.Theorem, source: true),
            Node("gap_criterion", "A strict deadline for every upper ascent",
                "Under the same two avoidance assumptions on w, let b=lowerPerm(w), "
                + "u=upperPerm(w) and g=gap(extractShuffle(w)). Then dead(b,0)=m+2; "
                + "for every natural t<=m, t<dead(b,t); and w avoids 1324 if and only "
                + "if every pair i<j in Fin(k) with u(i)<u(j) satisfies "
                + "g(j)<dead(b,g(i)). The strict cutoff is essential. The proof "
                + "relates a lower ascent across a gap interval to its first later "
                + "endpoint. It asserts no monotonicity of dead.", DescribeRole.Theorem),
            Node("Actual", "The literal source class",
                "For every b in Perm(m) and k in N, Actual(b,k) is the subtype of "
                + "w in Perm(m+k) such that lowerWord(w) is exactly the position-ordered "
                + "list of b's values, w avoids 1324, and upperPerm(w) avoids 213. "
                + "This is the original fixed value-cut class of actual permutations.", source: true),
            Node("Configuration", "The equivalent gap data",
                "For b in Perm(m) and k in N, a configuration consists of u in "
                + "Perm(k) and weakly increasing g:Fin(k)->Fin(m+1), with u avoiding "
                + "213 and g(j)<dead(b,g(i)) for every i<j with u(i)<u(j). "
                + "The bottom remains the whole fixed b."),
            Node("actualEquiv", "Equivalence with the actual source permutations",
                "For every m, b in Perm(m) avoiding 132, and k in N, actualEquiv(b,k) "
                + "is an equivalence Actual(b,k) equivalent to Configuration(b,k). "
                + "It combines the insertion and gap equivalences with the strict "
                + "mixed-pattern criterion. The proof identifies lowerWord with "
                + "the values of lowerPerm and upperWord with those of upperPerm, "
                + "so equality of the bottom is literal list equality. Both "
                + "composites are identities, including k=0."),
            Node("count", "Cardinality of actual permutations",
                "For every b in Perm(m) and k in N, count(b,k)=Nat.card(Actual(b,k)). "
                + "This is d(b,k) in the source. No recurrence is assumed in this "
                + "definition; the next module proves the actual cardinal recurrence.", source: true))));

    private static DocumentBlock Node(string name, string title, string prose,
        DescribeRole role = DescribeRole.Definition, bool source = false) =>
        Describe.Lean(DescribeId.Create(name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.WithoutFormula(),
            source ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
