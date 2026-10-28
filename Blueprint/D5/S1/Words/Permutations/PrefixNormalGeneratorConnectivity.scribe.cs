using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Permutations;

internal sealed class PrefixNormalGeneratorConnectivityDocument : IScribeDocumentDefinition
{
    private const string Root = "D5/S1/Words/Permutations/PrefixNormalGeneratorConnectivity.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/PermutationPatterns/adamsondudeyfleischmannhuch2025prefixnormal");
    private static Formula N => Q(Mathbb, Grp(V("N")));
    private static Formula L => C("List", N);
    private static Formula S => C("Finset", N);
    private static Formula Predicate => Q(L, To, V("Prop"));
    private static Formula n => V("n");
    private static Formula s => V("s");
    private static Formula t => V("t");
    private static Formula a => V("a");
    private static Formula b => V("b");
    private static Formula p => V("p");
    private static Formula l => V("l");
    private static Formula m => V("m");
    private static Formula ell => V("ell");
    private static Formula set => V("S");
    private static Formula P => V("P");
    private static Formula Cat(Formula x, Formula y) => C("append", x, y);
    private static Formula Pair(Formula x, Formula y, Formula tail) => C("cons", x, C("cons", y, tail));
    private static Formula Count(Formula x, Formula start, Formula len) => C("count", x, start, len);
    private static Formula Normal(Formula x) => C("PN", n, x);
    private static Formula Gen(Formula x) => C("Generator", n, x);
    private static Formula Exact(Formula x) => C("ExactGenerator", n, x);
    private static Formula Perm => C("Perm", l, C("range", n));
    private static Formula Drop => C("toFinset", C("drop", t, l));
    private static Formula Remaining => Q(C("range", n), Setminus, C("toFinset", C("take", t, l)));
    private static Formula Closure => All("p", L, All("s", L, All("a", N, All("b", N,
        Q(a, Lt, b, Implies, C("P", Cat(p, Pair(a, b, s))), Implies,
            C("P", Cat(p, Pair(b, a, s))))))));
    private static Formula Path(Formula pred, Formula x, Formula y) =>
        C("ReflTransGen", C("Edge", pred), x, y);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Valid flip-to-zero generators are connected by finite adjacent-position exchanges.",
        H("Connectivity of prefix normal generators"),
        Blocks(
            Paragraph(Text("The source is Adamson, Dudey, Fleischmann and Huch, arXiv:2508.19619v1. "
                + "Its Conclusion asks whether any prefix normal generator can reach all others by "
                + "swapping neighbouring entries. The institutional accepted author manuscript poses "
                + "the same question. The result answers that question in these two read versions "
                + "in a zero-based model, for every natural n and hence every positive n. "
                + "The later Springer chapter body is inaccessible and has not been compared with v1; "
                + "its answer status remains ASSUMED-UNVERIFIED. This exposition asserts neither "
                + "current literature priority nor a counted resolution.")),
            Paragraph(Text("A set S represents a binary word of fixed length n: position i has bit 1 "
                + "exactly when i belongs to S, for 0<=i<n. The actual chain sets are subsets of range(n). "
                + "The source coordinate is i+1, and a zero-based permutation entry a means flipping "
                + "source position a+1. Adding one to every entry is a bijection with permutations of "
                + "1,...,n and preserves list positions, order of flips and adjacency. After t flips, "
                + "source component t+1 is the characteristic word of range(n) minus take(t,l). "
                + "All times 0<=t<=n are quantified; permutation length and distinctness give precisely "
                + "n+1 states, starting at all ones and ending at all zeros.")),
            Node("count", "Factor count", All("S", S, All("s", N, All("ell", N,
                Q(Count(set,s,ell), Eq, C("card", C("inter",set,C("Ico",s,Q(s,Plus,ell)))))))),
                "inter denotes finite-set intersection. Ico(s,s+ell) "
                + "is the half-open interval [s,s+ell); card counts its occupied positions. "
                + "Thus count agrees with the number of ones in a contiguous binary factor.", true, true),
            Node("PN", "Prefix normality", All("n",N,All("S",S,
                Q(Normal(set), Iff, All("s",N,All("ell",N,
                    Q(s,Plus,ell,Le,n,Implies,Count(set,s,ell),Le,Count(set,D(0),ell))))))),
                "Every factor ending at or before n is compared with the prefix of the same length. "
                + "Zero lengths, zero counts, empty words and factors ending exactly at n are included. "
                + "The predicate itself is also defined on unrestricted finite sets; only the "
                + "permutation-chain uses assert the binary word of length n.", true, true),
            Node("count_erase", "Deleting one occupied position", All("S",S,All("s",N,All("ell",N,All("a",N,
                Q(Count(C("erase",set,a),s,ell),Eq,C("ite",
                    Q(a,InMacro,set,Land,s,Le,a,Land,a,Lt,s,Plus,ell),
                    Q(Count(set,s,ell),Minus,D(1)),Count(set,s,ell))))))),
                "Subtraction is natural subtraction. This finite-set cardinality identity is "
                + "consumed by erase_later_preserves and carries no separate research claim."),
            Node("erase_later_preserves", "Deletion farther to the right", All("n",N,All("S",S,All("a",N,All("b",N,
                Q(a,Lt,b,Implies,a,InMacro,set,Implies,b,InMacro,set,Implies,
                    Normal(set),Implies,Normal(C("erase",set,a)),Implies,Normal(C("erase",set,b))))))),
                "For each factor, split according to whether b is in its equal-length prefix and "
                + "in the factor. If both contain b, both counts lose one. If only the prefix "
                + "contains b, interval geometry excludes a from the factor and the comparison "
                + "comes from S with a erased. If the prefix excludes b, use monotonicity of "
                + "deletion. The checked local fact is consumed by the ascent exchange."),
            Node("Generator", "Suffix form of chain validity", All("n",N,All("l",L,
                Q(Gen(l),Iff,Perm,Land,All("t",N,Q(t,Le,n,Implies,Normal(Drop)))))),
                "The suffix lists the positions not yet flipped. This proof-facing predicate "
                + "is equivalent to the direct undeleted-set predicate below.", true),
            Node("generator_ascent_swap", "Published Lemma 17", All("n",N,All("p",L,All("s",L,All("a",N,All("b",N,
                Q(a,Lt,b,Implies,Gen(Cat(p,Pair(a,b,s))),Implies,Gen(Cat(p,Pair(b,a,s))))))))),
                "For q=length(p), the old and new states agree for t<=q and t>=q+2. "
                + "Only t=q+1 differs, and erase_later_preserves proves its prefix normality. "
                + "The source component of this state is q+2, as in the recurrence and Figure 5; "
                + "the q+1 component references in the Lemma 17 prose are not used as assumptions. "
                + "This is a published supply statement with an independent Lean proof.", false, true),
            Node("Edge", "Valid adjacent-position exchange", All("P",Predicate,All("l",L,All("m",L,
                Q(C("Edge",P,l,m),Iff,C("P",l),Land,C("P",m),Land,
                    Ex("p",L,Ex("s",L,Ex("a",N,Ex("b",N,
                        Q(l,Eq,Cat(p,Pair(a,b,s)),Land,m,Eq,Cat(p,Pair(b,a,s))))))))))),
                "Both endpoints satisfy P. A common prefix and suffix show literal adjacency "
                + "of the exchanged positions; a,b need not be consecutive values. "
                + "For generators they are distinct by permutation validity.", true),
            Node("normalize_by_adjacent_ascents", "Consumed insertion path", All("P",Predicate,
                Q(Open,Closure,Close,Implies,All("l",L,All("p",L,Q(C("P",Cat(p,l)),Implies,
                    Path(P,Cat(p,l),Cat(p,C("insertionSortDescending",l)))))))),
                "insertionSortDescending(l) denotes List.insertionSort with relation b<=a. "
                + "Contextual inductions over insertion and the list construct actual adjacent "
                + "edges while preserving P at every intermediate vertex. Generic Mathlib sorting "
                + "is applied directly for permutation and sortedness below; this helper supplies "
                + "the valid intermediate path and is consumed only by full_event_list."),
            Node("full_event_list", "Connectivity in suffix coordinates", All("n",N,All("l",L,All("m",L,
                Q(Gen(l),Implies,Gen(m),Implies,Path(C("Generator",n),l,m))))),
                "Normalize each endpoint to descending order using generator_ascent_swap. "
                + "List.perm_insertionSort, List.pairwise_insertionSort and List.Perm.eq_of_pairwise' "
                + "identify the sorted endpoints directly. Edge symmetry reverses the second "
                + "path; transitivity joins them. This theorem is consumed by result."),
            Node("suffix_eq_undeleted", "The actual binary-state correspondence", All("n",N,All("l",L,
                Q(Perm,Implies,All("t",N,Q(Drop,Eq,Remaining))))),
                "For every time t, not merely an interior time, permutation membership and "
                + "take/drop disjointness identify the suffix with precisely the undeleted set. "
                + "This equality is consumed in both directions by generator_iff_exact."),
            Node("ExactGenerator", "Direct flip-to-zero chain", All("n",N,All("l",L,
                Q(Exact(l),Iff,Perm,Land,All("t",N,Q(t,Le,n,Implies,Normal(Remaining)))))),
                "This definition uses the actual set difference after each of the n+1 possible "
                + "flip counts. No validity clause is supplied as an unproved structural premise.", true, true),
            Node("generator_iff_exact", "Equivalent chain coordinates", All("n",N,All("l",L,
                Q(Gen(l),Iff,Exact(l)))),
                "The suffix/undeleted equality transports each chain comparison in both directions. "
                + "It is consumed on the two endpoints and on every edge transported by result."),
            Node("result", "The exact v1 event", All("n",N,All("l",L,All("m",L,
                Q(Exact(l),Implies,Exact(m),Implies,Path(C("ExactGenerator",n),l,m))))),
                "ReflTransGen is the reflexive transitive closure, so the path is finite and may "
                + "have zero moves. Every nontrivial edge has valid endpoints; the initial validity "
                + "hypothesis also covers reflexivity. There is no restriction on direction, "
                + "complexity, shortest paths or which sorting procedure a path must follow. "
                + "The harmless n=0 extension does not replace any positive-n case.",
                resolution: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("adamson-dudey-fleischmann-huch-prefix-normal-connectivity"),
                    ResolutionKind.Proved)),
            Paragraph(Text("The displayed names ReflTransGen, Perm, range, take, drop, toFinset, "
                + "append, cons, erase and Ico denote their Lean operations. All new helpers lie on "
                + "the result's live proof path. The generic sorting path, the suffix theorem and "
                + "the final coordinate transport are proof support for this one question. "
                + "Descending n,...,1 is a semantic valid generator: each state is an initial "
                + "block of ones followed by zeros, so its prefix maximizes the count. "
                + "No weighted-alphabet, directed reachability or efficient enumeration conclusion "
                + "is asserted. The verified source scope and final-version limit are in the "
                + "Library note; Lemma 17 is published supply, and the global construction is "
                + "the retained application to the explicit v1 question.")))));

    private static DocumentBlock Node(string name, string title, Formula formula,
        string prose, bool definition = false, bool literature = false,
        OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
        DescribeId.Create("prefix-normal-" + name.Replace('_','-').ToLowerInvariant()),
        DeclarationHandle.Create(Root + name), H(title), StatementSource.FromAuthor(Disp(formula)),
        literature ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(Source),
        Blocks(Paragraph(Text(prose))), definition ? DescribeRole.Definition : DescribeRole.Theorem,
        openProblemResolutionClaim: resolution);

    private static Formula All(string name, Formula type, Formula body) =>
        Q(Forall,Open,V(name),Colon,type,Close,Comma,body);
    private static Formula Ex(string name, Formula type, Formula body) =>
        Q(Exists,Open,V(name),Colon,type,Close,Comma,body);
    private static Formula V(string name) => F.Id(name);
    private static Formula C(string name, params Formula[] args) =>
        new Formula.Apply(Q(Operatorname,Grp(V(name))), [.. args]);
    private static Formula Q(params Formula[] items)
    {
        var spaced = new Formula[items.Length*2-1];
        for (var i=0;i<items.Length;i++)
        {
            spaced[2*i]=items[i];
            if (i+1<items.Length) spaced[2*i+1]=Sp;
        }
        return Seq(spaced);
    }
}
