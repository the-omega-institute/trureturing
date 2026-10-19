using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.PriorityLattice;

internal sealed class SublatticeDismantlingDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/PriorityLattice/SublatticeDismantling.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/GraphInvariants/lillo2026prioritylattice");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The priority lattice is not always sublattice dismantlable.",
        H("A sublattice obstruction in the priority lattice"),
        Blocks(
            Node("ambient-closed", "AmbientClosed", "Closure under ambient extrema",
                "For every two members x and y of a set, an ambient greatest lower bound and "
                + "an ambient least upper bound must exist and belong to the set. Bounds are "
                + "tested against every element of the ambient partial order. This expresses "
                + "binary sublattice closure without choosing operations or requiring the "
                + "ambient bottom and top to belong to the subset.", DescribeRole.Definition),
            Node("recursive", "Dismantlable", "Recursive disjoint sublattice subdivision",
                "A singleton is dismantlable. A closed set is dismantlable when it is the "
                + "disjoint union of two nonempty closed sets, each dismantlable by the same "
                + "rule. An inductive proof is exactly a finite binary subdivision tree "
                + "ending in singletons. The word subdivision in Section 6, item 4 is read "
                + "as a partition, consistently with the cited Sage implementation. An "
                + "overlapping-cover interpretation is outside this statement.", DescribeRole.Definition),
            Node("hereditary", "hereditary", "Restriction to a nonempty sublattice",
                "Intersect a dismantling tree with a nonempty ambient sublattice. Uniqueness "
                + "of greatest lower bounds and least upper bounds makes every intersection "
                + "closed. If one child intersection is empty, retain the other child; if "
                + "both are nonempty, retain their disjoint split. Singleton leaves restrict "
                + "to singleton leaves. Thus every nonempty sublattice of a dismantlable "
                + "set is dismantlable.", DescribeRole.Lemma),
            Node("order-transport", "dismantlable_image", "Transport by the source order isomorphism",
                "An order isomorphism transports all ambient extrema, closed sets, disjoint "
                + "partitions, nonemptiness and recursive subdivision trees. In particular "
                + "the existing coreOrderIso at n = 6 connects the literal PriorityForest "
                + "carrier and its adjoined top to the IntervalForest carrier used below.", DescribeRole.Lemma),
            Node("embedding", "embed", "Sixteen forests and the actual top",
                "Put F = {(0,1),(0,2),(3,4),(3,5)}. The sixteen forests are F, "
                + "A_i = F union {(i,3)}, B_j = F union {(3+j,6)}, and "
                + "C_ij = F union {(i,3),(3+j,6)}, with i and j in {0,1,2}. "
                + "The code some(a,b), with a and b in Fin 4, selects no extra edge when "
                + "a coordinate is zero and selects the corresponding parent when it is "
                + "positive. Code none denotes the actual adjoined ambient top. The "
                + "parent functions satisfy increasingness and the local interval condition "
                + "of forestOfLocal; hence these are actual source forests. Reading the "
                + "parents at vertices 3 and 6 proves injectivity, giving seventeen distinct elements.", DescribeRole.Definition),
            Node("meet", "meet_extremum", "All ambient greatest lower bounds",
                "On two forest codes, retain each optional extra parent exactly when both "
                + "forests contain it. Their edge intersection is one of the sixteen valid "
                + "forests. Parent preservation proves it is below both forests and above "
                + "every common lower bound in the whole ambient order. Meeting with top "
                + "returns the other argument. Thus every one of the seventeen-by-seventeen "
                + "ambient meets lies in the displayed set.", DescribeRole.Lemma),
            Node("join", "join_extremum", "All ambient least upper bounds",
                "Compatible optional parents combine to give another displayed valid forest. "
                + "Its edges are the union, so it is below every common upper bound. "
                + "Incompatible codes give two different parents to vertex 3 or vertex 6. "
                + "No ambient forest can contain both assignments, and the only common "
                + "upper bound is the actual adjoined top. Joining with top returns top. "
                + "These conclusions follow from the defining order and do not require "
                + "a general intersection or union formula for arbitrary priority forests.", DescribeRole.Lemma),
            Node("no-partition", "no_partition", "The incidence obstruction has no first split",
                "The seventeen-element sublattice is the incidence lattice of K3,3. "
                + "If F and top occupy different parts, C_00, C_11 and C_22 have pairwise "
                + "meet F and join top, so neither part can hold two of them. If both "
                + "bounds occupy one part, the other part has at most one atom and one "
                + "coatom. A lone coatom is forced by the join of its two endpoint atoms. "
                + "If that other part contains an atom, at least two of its three incident "
                + "coatoms occupy the first part and their meet forces the atom there too. "
                + "The formal finite Boolean argument uses exactly these ambient operation "
                + "tables and excludes every nontrivial two-part sublattice partition.", DescribeRole.Lemma),
            Describe.Lean(DescribeId.Create("priority-dismantling-claim"),
                DeclarationHandle.Create(Prefix + "claim"), H("The whole universal question"),
                StatementSource.FromAuthor(F.Disp(F.Seq(
                    F.Id("claim"), F.Sp, F.Iff, F.Sp, F.Forall, F.Sp,
                    F.Id("n"), F.Sp, F.InMacro, F.Sp, F.Mathbb, F.Grp(F.Id("N")),
                    F.Sp, F.Comma, F.Sp, F.D(1), F.Sp, F.Leq, F.Sp, F.Id("n"),
                    F.Sp, F.To, F.Sp, F.Operatorname, F.Grp(F.Id("Dismantlable")),
                    F.Sp, F.Open, F.Operatorname, F.Grp(F.Id("univ")), F.Sp, F.Colon,
                    F.Sp, F.Operatorname, F.Grp(F.Id("Set")), F.Sp, F.Open,
                    F.Operatorname, F.Grp(F.Id("Pi")), F.Sp, F.Id("n"), F.Close, F.Close))),
                AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text(
                    "Lillo and Rosas ask whether Pi(n) is sublattice dismantlable for every "
                    + "positive n, after reporting Sage checks for n from 1 through 5. "
                    + "Pi is the existing source carrier of all increasing interval forests "
                    + "on labels 0 through n, ordered by edge inclusion, with an extra top."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("priority-dismantling-result"),
                DeclarationHandle.Create(Prefix + "result"), H("A negative answer at n = 6"),
                StatementSource.FromAuthor(F.Disp(F.Seq(F.Neg, F.Sp, F.Id("claim")))),
                AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text(
                    "If the actual Pi(6) were dismantlable, order transport followed by "
                    + "restriction would dismantle its displayed seventeen-element ambient "
                    + "sublattice. That sublattice has neither a singleton carrier nor a first "
                    + "split, a contradiction. The positive parameter 6 therefore refutes the "
                    + "entire universal question. The abstract incidence obstruction and the "
                    + "existing principal-interval results are background; the source-specific "
                    + "conclusion follows from the explicit forests and ambient extrema. "
                    + "No assertion about the authors' historical Sage version or an "
                    + "overlapping-cover meaning is needed, and no exhaustive publication "
                    + "priority claim is made."))), DescribeRole.Theorem,
                new OpenProblemResolutionClaim(ProblemSlugRef.Create(
                    "lillo-rosas-2026-priority-lattice-sublattice-dismantling"), ResolutionKind.Refuted))), []));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create("priority-dismantling-" + id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role);
}
