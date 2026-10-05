using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.GraphRepresentation;

internal sealed class UniformHierarchyDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Words/GraphRepresentation/UniformHierarchy.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Words/adamson2026twoword");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For every positive k, the finite graphs represented by two k-uniform words "
        + "form a proper subclass of those represented by two (k+1)-uniform words.",
        H("Strict Positive Uniform Hierarchy"),
        Blocks(
            Paragraph(Text("The representation is "),
                Ref("D5/S1/Words/GraphRepresentation/UniformVertexExtension.InG"),
                Text(". Both actual List words contain every vertex exactly k times. "
                    + "For every ordered distinct pair, adjacency is equivalent to equality "
                    + "of the actual two-letter projections, using "),
                Ref("D5/S1/Words/GraphRepresentation/ExplicitNonTwoUniform.twoProjection"),
                Text(". Positive k begins at one. Inclusion covers all finite carriers, "
                    + "including the empty carrier, at every type universe. Decidable "
                    + "equality is available on every carrier. No alternation or "
                    + "union-of-languages representation is used.")),
            Node("membershipGraph", "The finite membership graph", GraphFormula(),
                "Omega(m) is Fin(m) plus all finite subsets of Fin(m), with disjoint tags. "
                + "A point and a subset are adjacent exactly when the point belongs to the "
                + "subset. Both same-tag adjacency relations are false. The graph is finite, "
                + "undirected and loopless. This parameterized definition supplies the "
                + "actual obstruction in the full consumer.", DescribeRole.Definition),
            Node("claim", "The complete positive-k source assertion", ClaimFormula(),
                "For k>0 put m=64k^2 and Omega=Omega(m). For a finite subset s of Omega, "
                + "X(s) is its subtype and H(s) is U(m).comap(val). The first conjunct "
                + "quantifies over every finite vertex type with decidable equality and "
                + "every simple graph on it. The second supplies a finite subset s, with "
                + "the same H(s) on the same X(s) in its positive and negative clauses. "
                + "Actual word witnesses are supplied by InG. This is Conjecture 31 of "
                + "the primary source with an explicit finite ambient graph for its "
                + "existential separator. IFIG Report 2501 Conjecture 3.2 states the "
                + "same problem and is not an additional settlement.",
                DescribeRole.Definition),
            Describe.Remark(DescribeId.Create("uniform-hierarchy-source-conjecture"),
                DeclarationHandle.Create(Prefix + "claim"),
                H("The published source question"), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "Conjecture 31 states: for each k in the source's natural numbers, "
                    + "the inclusion G_k subset G_(k+1) is proper. The source natural "
                    + "numbers begin at one. The claim retains this whole assertion "
                    + "and strengthens its existential clause by specifying the finite "
                    + "ambient membership graph. This additional witness refinement "
                    + "is repository-derived, not attributed to the source.")))),
            Paragraph(Ref(Source.Value), Text(": "
                + "Theorem 29 supplies the known conclusion that no fixed positive-k "
                + "class contains every finite graph. The full consumer discharges "
                + "that conclusion internally, using the actual membership graph "
                + "and the repository cut reconstruction. Its chosen bound m=64k^2 "
                + "and local proof are not attributed to the paper. No independent "
                + "known-result declaration or theorem parameter is introduced.")),
            Node("result", "Every adjacent inclusion is proper", ClaimFormula(),
                "For inclusion, enumerate the finite carrier once in q and append the "
                + "same q to both words. Counts increase by one; projected suffixes are "
                + "identical, so right cancellation preserves every edge and nonedge. "
                + "For separation, discharge the known Theorem 29 nonuniversality "
                + "component from the source literature inside this proof. In a "
                + "hypothetical representation of U(m), each left restriction has "
                + "length km. Each right vertex has two ordered k-cut lists bounded "
                + "by km. Encode each list as Fin(k) -> Fin(km+1), preserving tied "
                + "cuts and order. The signature count is (km+1)^(2k). The estimates "
                + "km+1 <= 128k^3 <= 2^(7+3k) <= 2^(10k) give at most 2^(20k^2) "
                + "signatures, strictly fewer than the 2^(64k^2) subsets. Pigeonhole "
                + "gives distinct subsets with equal signatures. Use arbitrary-cut "
                + "reconstruction separately in each actual word and cancel each "
                + "fixed right label's own injective Unit-marker renaming. Equal "
                + "normalized cut data then give equal adjacency truth at every left "
                + "point; finite-set extensionality contradicts distinctness. The "
                + "left orders may differ. Original projections carrying different "
                + "right labels are never equated. "
                + "Nat.find selects a nonrepresented induced subset s of minimum "
                + "cardinality. The whole carrier is a witness by actual word transport "
                + "through the whole-set subtype equivalence. The empty subtype has "
                + "[]/[] representations, so s contains x. Minimality supplies an "
                + "actual k-uniform representation of the smaller erased subset t. "
                + "Let d identify X(t) with the subtype of X(s) excluding x, keeping "
                + "underlying vertices. E=optionCongr(d).trans(optionSubtypeNe(x)) "
                + "maps none to x and some(z) to its original retained vertex. "
                + "For K=H(s).comap(E), the actual deletion K.comap(some) equals H(t). "
                + "Apply the frozen vertex extension and map its returned words "
                + "through E. Injective count transport and filter/map identities "
                + "preserve every count and both directions of each adjacency iff. "
                + "Pair InG(k+1,H(s)) with the original nonmembership in InG(k,H(s)) "
                + "on precisely X(s). No nonuniversality, closure, minimum, relabeling "
                + "or extension premise is assumed.",
                resolves: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("adamson-positive-uniform-hierarchy"),
                    ResolutionKind.Proved)),
            Paragraph(Text("The live inference directly reuses "),
                Ref("D5/S0/Diagonal/PigeonholeFiber.finite_reading_has_fiber"), Text(", "),
                Ref("D5/S1/Words/GraphRepresentation/ExplicitNonTwoUniform.projection_eq_reconstruction"),
                Text(" and "),
                Ref("D5/S1/Words/GraphRepresentation/UniformVertexExtension.vertex_extension"),
                Text(". Known nonuniversality and local word transports remain inside "
                    + "this single full consumer. No exponentially large graph is "
                    + "enumerated. The inaccessible SSRN and Gradiva full bodies limit "
                    + "priority claims. Reg enrollment is paused.")))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role = DescribeRole.Theorem, AssessedProvenance? provenance = null,
        OpenProblemResolutionClaim? resolves = null) =>
        Describe.Lean(DescribeId.Create("uniform-hierarchy-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
            provenance ?? AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text(prose))), role, resolves);

    private static Formula X(string value) => F.Id(value);
    private static Formula Named(string value) => Seq(Operatorname, Grp(X(value)));
    private static Formula App(string name, params Formula[] args) =>
        new Formula.Apply(Named(name), [.. args]);
    private static Formula Par(Formula value) => Seq(Open, value, Close);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, X(name), Colon, Sp, type, Comma, Sp, body);
    private static Formula And(Formula a, Formula b) => Seq(Par(a), Sp, Land, Sp, Par(b));
    private static Formula Imp(Formula a, Formula b) => Seq(Par(a), Sp, Implies, Sp, Par(b));
    private static Formula IffEq(Formula a, Formula b) => Seq(Par(a), Sp, Iff, Sp, Par(b));
    private static Formula Natural() => Seq(Mathbb, Grp(X("N")));
    private static Formula Inl(Formula a) => App("inl", a);
    private static Formula Inr(Formula a) => App("inr", a);
    private static Formula R(Formula k, Formula g) => App("InG", k, g);
    private static Formula U() => App("membershipGraph", X("m"));
    private static Formula Equations(params Formula[] rows) => Disp(Seq(
        Begin, Grp(X("gathered")),
        Seq(rows.SelectMany((row, index) => index == 0
            ? new[] { row } : new[] { RowBreak, row }).ToArray()),
        End, Grp(X("gathered"))));
    private static Formula GraphFormula() => Equations(
        Seq(Forall, Sp, X("m"), Colon, Natural(), Comma, Sp,
            X("a"), Comma, X("b"), Colon, App("Fin", X("m")), Comma, Sp,
            X("S"), Comma, X("T"), Colon, App("Finset", App("Fin", X("m")))),
        Equal(App("Omega", X("m")), App("Sum", App("Fin", X("m")),
            App("Finset", App("Fin", X("m"))))),
        Seq(U(), Colon, App("SimpleGraph", App("Omega", X("m")))),
        IffEq(App("Adj", U(), Inl(X("a")), Inr(X("S"))),
            Seq(X("a"), Sp, InMacro, Sp, X("S"))),
        IffEq(App("Adj", U(), Inr(X("S")), Inl(X("a"))),
            Seq(X("a"), Sp, InMacro, Sp, X("S"))),
        And(Seq(Neg, App("Adj", U(), Inl(X("a")), Inl(X("b")))),
            Seq(Neg, App("Adj", U(), Inr(X("S")), Inr(X("T"))))));
    private static Formula Inclusion() => All("V", Named("Type"),
        Imp(App("Finite", X("V")), All("G", App("SimpleGraph", X("V")),
            Imp(R(X("k"), X("G")), R(Add(X("k"), D(1)), X("G"))))));
    private static Formula Separator() => Seq(Exists, Sp, X("s"), Colon, Sp,
        App("Finset", App("Omega", Multiply(D(6, 4), new Formula.Power(X("k"), D(2))))),
        Comma, Sp,
        And(R(Add(X("k"), D(1)), App("H", X("s"))),
            Seq(Neg, R(X("k"), App("H", X("s"))))));
    private static Formula ClaimFormula() => Disp(All("k", Natural(),
        Imp(Seq(D(0), Sp, Lt, Sp, X("k")), And(Inclusion(), Separator()))));
}
