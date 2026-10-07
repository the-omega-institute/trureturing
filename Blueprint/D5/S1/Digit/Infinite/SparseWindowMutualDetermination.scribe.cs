using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Digit.Infinite;

internal sealed class SparseWindowMutualDeterminationDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef GoldenWindows =
        LibraryNoteRef.Create("D5/L/Digit/mathlib2026goldenwindows");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Sparse natural Fibonacci windows have the same fibres precisely when their translated cuts agree.",
        H("Sparse Fibonacci Window Mutual Determination"),
        Blocks(
            Paragraph(Text(
                "Let X(L) be the binary words of length L with no adjacent ones. "
                    + "The Fibonacci numbers start with F(0)=0 and F(1)=1, and G(L)=F(L+2). "
                    + "The canonical value V(p) is the sum of the Fibonacci weights F(j+2) "
                    + "at the occupied positions j of p. The row zRow(n) is the canonical "
                    + "finite Fibonacci expansion of n, continued by zeros. P(L) takes its "
                    + "first L digits. All natural numbers here include zero.")),
            Paragraph(Text(
                "For a finite set S of retained natural times, observations use ordinary "
                    + "addition on a single source. The tuple is a function on the subtype "
                    + "of times belonging to S, including the empty function when S is empty. "
                    + "Icc denotes an inclusive interval of natural indices.")),
            new DocumentBlock.DisplayFormula(DefinitionsFormula()),
            Paragraph(Text(
                "The range of an observation consists of its actual natural values. "
                    + "Write actual(n) for sigma(m,S,n), regarded as an element of that range "
                    + "with witness n, and val for the underlying value of a range element. "
                    + "Equiv denotes a bijection with a specified inverse.")),
            Describe.Lean(
                DescribeId.Create("sparse-window-natural-row-raw-data"),
                DeclarationHandle.Create(
                    "D5/S1/Digit/Infinite/SparseWindowMutualDetermination.natural_row_raw_data"),
                H("Canonical natural digits"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(GoldenWindows),
                Blocks(Paragraph(Text("For every natural n, the raw digits of its Zeckendorf expansion have value n. At every position their real coefficient equals the Boolean digit of zRow(n)."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("sparse-window-natural-row-phase"),
                DeclarationHandle.Create(
                    "D5/S1/Digit/Infinite/SparseWindowMutualDetermination.natural_row_phase"),
                H("Natural row phase"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(GoldenWindows),
                Blocks(Paragraph(Text("For every natural n, the phase of zRow(n) is n times the golden ratio modulo one. The equality identifies natural digit observations with circle rotation."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("sparse-window-natural-phase-avoids-cut"),
                DeclarationHandle.Create(
                    "D5/S1/Digit/Infinite/SparseWindowMutualDetermination.natural_phase_avoids_cut"),
                H("Natural phases avoid positive cuts"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(GoldenWindows),
                Blocks(Paragraph(Text("For every natural n and every positive cut index k, the phase n times the golden ratio modulo one differs from E(k). Irrationality excludes equality."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("sparse-window-natural-window-arc"),
                DeclarationHandle.Create(
                    "D5/S1/Digit/Infinite/SparseWindowMutualDetermination.natural_window_arc"),
                H("Natural labels and cylinder arcs"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every positive width L, natural n, and legal word p of width L, q(L,n)=p if and only if the phase of zRow(n) belongs to the open cylinder arc A(p). Natural rows avoid the endpoint alternatives of the closed cylinder."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("sparse-window-cut-injective"),
                DeclarationHandle.Create(
                    "D5/S1/Digit/Infinite/SparseWindowMutualDetermination.cut_injective"),
                H("Distinct cut indices"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The circle cut map E is injective on natural indices."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("sparse-window-natural-phase-visit"),
                DeclarationHandle.Create(
                    "D5/S1/Digit/Infinite/SparseWindowMutualDetermination.natural_phase_visit"),
                H("Arbitrarily late open-set visits"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every nonempty open subset U of the circle and every natural bound B, a natural index n greater than B has golden phase in U."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("sparse-window-window-arc-avoids-cut"),
                DeclarationHandle.Create(
                    "D5/S1/Digit/Infinite/SparseWindowMutualDetermination.window_arc_avoids_cut"),
                H("Open arcs avoid their cuts"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every positive width L, legal word p, and index k between one and G(L), the circle cut E(k) lies outside A(p)."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("sparse-window-window-arc-open"),
                DeclarationHandle.Create(
                    "D5/S1/Digit/Infinite/SparseWindowMutualDetermination.window_arc_isOpen"),
                H("Open cylinder arcs"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every width L and legal word p of that width, A(p) is an open subset of the circle."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("sparse-window-golden-inverse-data"),
                DeclarationHandle.Create(
                    "D5/S1/Digit/Infinite/SparseWindowMutualDetermination.golden_inverse_data"),
                H("The reciprocal golden ratio"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The reciprocal golden ratio alpha is positive, less than one, and satisfies alpha squared plus alpha equals one."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("sparse-window-window-arc-cover"),
                DeclarationHandle.Create(
                    "D5/S1/Digit/Infinite/SparseWindowMutualDetermination.window_arc_cover"),
                H("Labels away from cuts"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every positive width L and every circle point z outside B(L), some legal word p of width L has z in A(p)."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("sparse-window-circle-integer-offset"),
                DeclarationHandle.Create(
                    "D5/S1/Digit/Infinite/SparseWindowMutualDetermination.circle_integer_offset"),
                H("Integer differences of equal phases"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("If two real numbers x and y have equal images in the circle modulo one, an integer k has real value x minus y."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("sparse-window-translated-cut"),
                DeclarationHandle.Create(
                    "D5/S1/Digit/Infinite/SparseWindowMutualDetermination.translated_cut"),
                H("Translation of cut indices"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For all natural t and j, adding t times the golden ratio modulo one to E(t+j) gives E(j)."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("sparse-window-phase-surjective"),
                DeclarationHandle.Create(
                    "D5/S1/Digit/Infinite/SparseWindowMutualDetermination.phase_surjective"),
                H("Every circle phase is realized"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The signed phase map from legal infinite digit rows to the circle is surjective."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("sparse-window-window-arc-unique"),
                DeclarationHandle.Create(
                    "D5/S1/Digit/Infinite/SparseWindowMutualDetermination.window_arc_unique"),
                H("Unique arc labels"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every positive width L and legal words p and q, membership of one circle point z in both A(p) and A(q) implies p equals q."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("sparse-window-missing-cut-witness"),
                DeclarationHandle.Create("D5/S1/Digit/Infinite/SparseWindowMutualDetermination.missing_cut_witness"),
                H("Missing target cuts"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For 1 at most m at most M, a finite S, 1 at most k at most G(M) with k outside K(m,S), and every natural bound B, two sources greater than B have the same sparse tuple and different M-windows."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("sparse-window-extra-cut-witness"),
                DeclarationHandle.Create("D5/S1/Digit/Infinite/SparseWindowMutualDetermination.extra_cut_witness"),
                H("Extra observation cuts"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For 1 at most m at most M, a finite S, an index k in K(m,S) outside the target cut interval, and every natural bound B, two sources greater than B have the same M-window and different sparse tuples."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("sparse-window-mutual-determination"),
                DeclarationHandle.Create(
                    "D5/S1/Digit/Infinite/SparseWindowMutualDetermination."
                        + "sparse_window_mutual_determination"),
                H("Equal cut sets, equal natural fibres, and the canonical actual-image bijection"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every positive pair of widths m at most M and every finite S, "
                            + "equality of the translated query-cut indices with the target-cut "
                            + "indices is equivalent to equality of the two natural fibre relations. "
                            + "Under this cut equality both actual ranges have G(M) elements. "
                            + "The displayed bijection sends p to sigma(m,S,V(p)); its inverse "
                            + "on an actual observation returns the target window of that same source.")),
                    Paragraph(Text(
                        "The phase of the canonical row n is n times the golden ratio modulo one. "
                            + "Translation by t is therefore addition of t times that ratio on the circle. "
                            + "Positive cut indices are distinct, and every natural row avoids them. "
                            + "The natural rotation visits every nonempty open arc above every natural bound. "
                            + "A chart centered at a chosen cut has its seam half a turn away. "
                            + "Small open collars on its two sides have different native window labels, "
                            + "including at the exterior seam. A missing target cut yields two arbitrarily "
                            + "late natural sources with equal query tuples and different targets. "
                            + "An extra query cut yields equal targets and different query tuples.")),
                    Paragraph(Text(
                        "Cut coverage forces time zero to be observed. For m at least two, "
                            + "this coordinate provides a common real interval of length at most alpha squared, "
                            + "where alpha is the reciprocal golden ratio. Its length plus that of any "
                            + "query arc is at most alpha squared plus alpha, which equals one. "
                            + "Two points in the common interval with the same query label consequently "
                            + "use the same integer lift of that query arc. A target boundary between "
                            + "the points would then be a query cut inside its own open query arc, "
                            + "a contradiction.")),
                    Paragraph(Text(
                        "For m=1 and M at least two, coverage additionally forces time one or "
                            + "time two to be observed. A one at either of the paired times gives "
                            + "a short anchor, and the common-lift argument allows length sum equal to one. "
                            + "If both paired bits are zero, the signed value lies in "
                            + "(alpha squared minus alpha cubed, alpha squared) for times {0,1}, "
                            + "and in (-alpha cubed, alpha squared minus alpha cubed) for times {0,2}. "
                            + "These are short anchors as well. For m=M=1 the observed time-zero "
                            + "coordinate already gives the target. No assertion that arbitrary binary "
                            + "tuples have connected fibres is used; the all-zero fibre for times {0,4} "
                            + "can be disconnected.")),
                    Paragraph(Text(
                        "Each target label occupies one connected open real interval. When the "
                            + "query cuts are target cuts, no translated query cut lies inside that interval. "
                            + "The disjoint open query-label sets then force each coordinate to remain "
                            + "constant throughout it, giving prediction. Canonical re-encoding gives "
                            + "q(L,V(p))=p, and the Zeckendorf sum bound gives V(p)<G(L). "
                            + "Together with V(q(L,n))=n for n<G(L), these identities identify X(L) "
                            + "with Fin(G(L)). Fibre equality factors the target through the actual "
                            + "sparse observation, while prediction identifies its image with the "
                            + "displayed V representatives. This establishes both cardinalities and "
                            + "the forward and inverse identities."))),
                DescribeRole.Theorem))));

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));

    private static Formula Window(Formula length) => Call("X", length);

    private static Formula Count(Formula length) => Call("G", length);

    private static Formula QFunction(Formula length) =>
        Seq(F.Id("q"), Underscore, Grp(length));

    private static Formula Q(Formula length, Formula n) =>
        Seq(QFunction(length), Open, n, Close);

    private static Formula SigmaFunction(Formula m, Formula s) =>
        Seq(SigmaLower, Underscore, Grp(m, Comma, s));

    private static Formula Observation(Formula m, Formula s, Formula n) =>
        Seq(SigmaFunction(m, s), Open, n, Close);

    private static Formula CutSet(Formula m, Formula s) => Call("K", m, s);

    private static Formula Range(Formula function) => Call("range", function);

    private static Formula Group(Formula formula) => Seq(Open, formula, Close);

    private static Formula CutEquality(Formula m, Formula big, Formula s) =>
        Seq(CutSet(m, s), Sp, Eq, Sp, Call("Icc", D(1), Count(big)));

    private static Formula DefinitionsFormula()
    {
        Formula length = F.Id("L");
        Formula m = F.Id("m");
        Formula s = F.Id("S");
        Formula n = F.Id("n");
        Formula t = F.Id("t");

        return Disp(Seq(
            Q(length, n), Sp, Eq, Sp, Call("P", length, Call("zRow", n)), Comma, Sp,
            Observation(m, s, n), Open, t, Close, Sp, Eq, Sp,
            Q(m, Seq(n, Plus, t)), Sp, Open, t, Sp, InMacro, Sp, s, Close, Comma, Sp,
            CutSet(m, s), Sp, Eq, Sp,
            Cup, Underscore, Grp(t, Sp, InMacro, Sp, s), Sp,
            Call("Icc", Seq(t, Plus, D(1)), Seq(t, Plus, Count(m)))));
    }

    private static Formula TheoremFormula()
    {
        Formula m = F.Id("m");
        Formula big = F.Id("M");
        Formula s = F.Id("S");
        Formula a = F.Id("a");
        Formula b = F.Id("b");
        Formula p = F.Id("p");
        Formula n = F.Id("n");
        Formula e = F.Id("e");
        Formula sparseRange = Range(SigmaFunction(m, s));
        Formula cutsEqual = CutEquality(m, big, s);
        Formula fibres = Group(Seq(
            Forall, Sp, a, Comma, b, Sp, InMacro, Sp, Naturals(), Comma, Sp,
            Group(Seq(
                Q(big, a), Sp, Eq, Sp, Q(big, b), Sp, Iff, Sp,
                Observation(m, s, a), Sp, Eq, Sp, Observation(m, s, b)))));
        Formula canonicalMap = Group(Seq(
            Forall, Sp, p, Sp, InMacro, Sp, Window(big), Comma, Sp,
            Call("val", new Formula.Apply(e, [p])), Sp, Eq, Sp,
            Observation(m, s, Call("V", p))));
        Formula actualMap = Group(Seq(
            Forall, Sp, n, Sp, InMacro, Sp, Naturals(), Comma, Sp,
            Call("val", new Formula.Apply(e, [Q(big, n)])), Sp, Eq, Sp,
            Observation(m, s, n)));
        Formula actualInverse = Group(Seq(
            Forall, Sp, n, Sp, InMacro, Sp, Naturals(), Comma, Sp,
            e, Caret, Grp(Minus, D(1)), Open, Call("actual", n), Close,
            Sp, Eq, Sp, Q(big, n)));
        Formula equivalence = Group(Seq(
            Exists, Sp, e, Sp, InMacro, Sp, Call("Equiv", Window(big), sparseRange), Comma, Sp,
            canonicalMap, Sp, Land, Sp, actualMap, Sp, Land, Sp, actualInverse));
        Formula imageConsequences = Group(Seq(
            cutsEqual, Sp, Rightarrow, Sp,
            Group(Seq(
                Call("card", Range(QFunction(big))), Sp, Eq, Sp, Count(big), Sp, Land, Sp,
                Call("card", sparseRange), Sp, Eq, Sp, Count(big), Sp, Land, Sp,
                equivalence))));

        return Disp(Seq(
            Forall, Sp, m, Comma, big, Sp, InMacro, Sp, Naturals(), Comma, Sp,
            Forall, Sp, s, Sp, InMacro, Sp, Call("Finset", Naturals()), Comma, Sp,
            Group(Seq(D(1), Sp, Le, Sp, m, Sp, Land, Sp, m, Sp, Le, Sp, big)),
            Sp, Rightarrow, Sp,
            Group(Seq(
                Group(Seq(fibres, Sp, Iff, Sp, cutsEqual)), Sp, Land, Sp,
                imageConsequences)), Dot));
    }
}
