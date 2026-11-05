using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology.Separation;

internal sealed class SynchronizedClopenSupportsDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Topology/Separation/SynchronizedClopenSupports.";

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(F.Id(name), [.. arguments]);

    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);

    private static Formula Exists(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula Imp(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula Statement()
    {
        Formula x = F.Id("X");
        Formula domain = F.Id("F");
        Formula map = F.Id("f");
        Formula p = F.Id("P");
        Formula a = F.Id("a");
        Formula w = F.Id("W");
        Formula nat = F.Id("Nat");
        Formula sets = Call("Set", x);
        Formula point(Formula n) => Call("At", a, n);
        Formula support(Formula n) => Call("At", w, n);

        Formula membership = All("n", nat,
            And(Call("Mem", Call("Value", point(F.Id("n"))), support(F.Id("n"))),
                Call("Mem", Call("Apply", map, point(F.Id("n"))), support(F.Id("n")))));
        Formula disjointness = All("m", nat, All("n", nat,
            Imp(Call("Ne", F.Id("m"), F.Id("n")),
                Call("Disjoint", support(F.Id("m")), support(F.Id("n"))))));
        Formula family = Exists("a", Call("Function", nat, Call("Subtype", domain)),
            Exists("W", Call("Function", nat, sets),
                And(All("n", nat, Call("IsClopen", support(F.Id("n")))),
                    And(disjointness, membership))));
        Formula conclusion = Exists("P", sets,
            And(Call("IsClopen", p),
                And(Call("Subset", domain, p),
                    And(Call("Subset", Call("Range", map), Call("Complement", p)), family))));
        Formula mapHypotheses = And(Call("Continuous", map),
            And(Call("Infinite", Call("Range", map)),
                Call("Disjoint", domain, Call("Range", map))));
        Formula maps = All("f", Call("Function", Call("Subtype", domain), x),
            Imp(mapHypotheses, conclusion));
        Formula domains = All("F", sets, Imp(Call("IsClosed", domain), maps));
        Formula spaces = And(Call("CompactSpace", x),
            And(Call("T2Space", x), Call("ZeroDimensionalSpace", x)));
        return Disp(All("X", F.Id("TopologicalSpaceU"), Imp(spaces, domains)));
    }

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Continuous infinite-image maps between disjoint closed sides have synchronized source-image pairs in disjoint ambient clopen supports.",
        H("Synchronized ambient clopen supports"),
        Blocks(
            Paragraph(Text(
                "X is an arbitrary topological space with carrier in Type u, compact, Hausdorff and zero-dimensional. "
                + "F is a closed subset, and f maps its actual subtype continuously into X. The actual range of f is infinite and disjoint from F. "
                + "No injectivity of f, relative partition, point sequence or ambient support family is assumed. "
                + "In the formula TopologicalSpaceU includes the carrier and its topology, Subtype(F) is the subtype of points belonging to F, "
                + "Function denotes a function type, Range is actual set range, Complement is ambient complement, and Subset and Mem are literal set relations. "
                + "At evaluates a sequence, Value is subtype inclusion, Apply evaluates f, and Ne is inequality.")),
            Describe.Lean(
                DescribeId.Create("synchronized-clopen-supports"),
                DeclarationHandle.Create(Owner + "exists_synchronized_clopen_supports"),
                H("Disjoint ambient supports retaining both corresponding points"),
                StatementSource.FromAuthor(Statement()),
                AssessedProvenance.FromRepo(
                    LibraryNoteRef.Create("D5/L/Topology/kania2026talagrand")),
                Blocks(
                    Paragraph(Text(
                        "There is one ambient clopen P containing all of F, whose complement contains the entire range of f. "
                        + "There are a sequence a from Nat into F and a sequence W of ambient subsets of X. Every W(n) is clopen. "
                        + "For distinct m and n the sets W(m) and W(n) are literally disjoint in X. Both Value(a(n)) and f(a(n)) belong to W(n). "
                        + "Thus each support is nonempty. Equality of two selected source points or two image points would put one point in two disjoint supports, "
                        + "so both point sequences are injective even though the given map need not be injective.")),
                    Paragraph(Text(
                        "The closed domain is compact, so its continuous image is compact and therefore closed in the Hausdorff ambient space. "
                        + "Mathlib's exists_clopen_of_closed_subset_open separates F from this image. "
                        + "Apply exists_seq_infinite_isOpen_pairwise_disjoint to the actual image subspace. Choose one y(n) in each relative open U(n), "
                        + "then choose a(n) from actual range membership with f(a(n)) equal to y(n). Lift U(n) to an ambient open O(n). "
                        + "Continuity makes its preimage open in F; lift that preimage to an ambient open S(n).")),
                    Paragraph(Text(
                        "The clopen basis supplies C(n) around a(n) inside P intersect S(n), and D(n) around y(n) inside the complement of P intersect O(n). "
                        + "A selected source point in C(m), or its image in D(m), would put y(n) in U(m). Disjointness of the relative U sets excludes this for m different from n. "
                        + "The opposite-side memberships are excluded by P. Hence both selected points of column n miss every E(m) with m different from n, "
                        + "where E(m) is C(m) union D(m). This step excludes the marked points; it does not assert disjointness of arbitrary ambient extensions.")),
                    Paragraph(Text(
                        "Define W(n) as E(n) minus the union of E(m) over m less than n. This is a clopen difference of a clopen and a finite clopen union. "
                        + "Both marked points survive because they miss all earlier E(m). If n is less than m, W(n) is contained in E(n), while W(m) excludes E(n). "
                        + "This proves literal ambient disjointness without an infinite-union closedness claim or a recursive support construction.")),
                    Paragraph(Text(
                        "For a homeomorphism between disjoint infinite closed subspaces, composing with ambient inclusion supplies exactly this map f. "
                        + "The resulting P and W are the initial synchronized geometry for the final-capture argument in the Talagrand CH route. "
                        + "The existing CountableClopenReflection.exists_common_stage can reflect P together with the countably many W(n) to one proper stage of a suitable profinite inverse system. "
                        + "The selected points remain actual final source-image pairs inside these supports. "
                        + "This local separation result constructs no transfinite system, proves no anti-homeomorphism conclusion or signed analytic endpoint, "
                        + "and does not resolve arXiv:2607.06808v2 Problem 8.2. No literature novelty is asserted."))),
                DescribeRole.Theorem))));
}
