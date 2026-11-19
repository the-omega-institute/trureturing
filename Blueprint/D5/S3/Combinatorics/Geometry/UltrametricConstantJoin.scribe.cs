using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Geometry;

internal sealed class UltrametricConstantJoinDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Geometry/UltrametricConstantJoin.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Constant cross-distance joins preserve ultrametricity and give exact sphere, order and distance-center formulas.",
        H("Constant cross-distance joins of ultrametric spaces"),
        Blocks(
            Paragraph(Text("Let X be an arbitrary indexed family of metric spaces, each with the ultrametric distance mixin. Fix a positive real cross-distance a and a proof hb that every component distance is at most a. Write J for Join X a ha hb. Indices and components may be empty; finiteness is imposed only for the finite sum and top-sphere count formulas. The center is the existing distance-center predicate from "),
                Ref("D5/S3/Combinatorics/Geometry/DovgosheyRovenskaCentralEdges.center"),
                Text(". A radius is central when it is nonnegative and has a distance witness at every point.")),
            Node("strong-triangle", "Non-strict component bounds suffice for the join metric",
                "crossDist_triangle_max",
                Disp(Seq(Call("crossDist", F.Id("X"), F.Id("a"), F.Id("p"), F.Id("r")), Sp, Leq, Sp,
                    Call("max", Call("crossDist", F.Id("X"), F.Id("a"), F.Id("p"), F.Id("q")),
                        Call("crossDist", F.Id("X"), F.Id("a"), F.Id("q"), F.Id("r"))))),
                Blocks(Paragraph(Text("For all three points of the dependent disjoint union, the displayed strong triangle inequality holds under the component upper bound. The cross-distance retains the old distance within a component and equals a between different components. The explicit metricSpace definition installs this metric on the dependent union; joinMetric transports it to Join without introducing a competing global metric on Sigma.")),
                    Paragraph(Text("The resulting Mathlib ultrametric mixin is "), Ref(Prefix + "isUltrametricDist"),
                        Text(". The same-component and cross-component formulas are "), Ref(Prefix + "dist_same"),
                        Text(" and "), Ref(Prefix + "dist_cross"), Text(".")))),
            Node("sphere-in-component", "Every sphere away from the join radius stays in its component",
                "sphere_eq_image", Disp(Seq(Call("sphere", JPoint(), F.Id("t")), Sp, Eq, Sp,
                    Call("image", F.Id("inclusion"), Call("sphere", F.Id("x"), F.Id("t"))))),
                Blocks(Paragraph(Text("For every index i, point x in X i and real radius t different from a, the inclusion sends the old sphere onto the entire join sphere. No inequality between t and a is required. The corresponding existential witness equivalence is "),
                    Ref(Prefix + "sphere_witness_iff"), Text(".")))),
            Node("top-sphere", "Strict bounds identify the sphere at the join radius", "sphere_top",
                Disp(Seq(Call("sphere", F.Id("p"), F.Id("a")), Sp, Eq, Sp,
                    OpenBrace, F.Id("q"), Sp, Mid, Sp, Call("fst", F.Id("q")), Sp, Neq, Sp,
                    Call("fst", F.Id("p")), CloseBrace)),
                Blocks(Paragraph(Text("Assume additionally that every component distance is strictly less than a. For every point p of J, its sphere at a consists exactly of the points in different components. This strict hypothesis is additional to the non-strict bound used to construct the metric.")))),
            Node("sphere-count", "Every sphere count away from the join radius is preserved", "sphere_card",
                Disp(Seq(Card(Call("sphere", JPoint(), F.Id("t"))), Sp, Eq, Sp,
                    Card(Call("sphere", F.Id("x"), F.Id("t"))))),
                Blocks(Paragraph(Text("For every i, x in X i and real t different from a, Nat.card gives the displayed equality. This statement needs no finiteness assumption; the sphere inclusion is injective and surjective onto the sphere.")))),
            Node("join-order", "The order of a finite join is the sum of the component orders", "card_join_sum",
                Disp(Seq(Card(F.Id("J")), Sp, Eq, Sp, Sum, Underscore, Grp(F.Id("i")),
                    Sp, Card(Call("X", F.Id("i"))))),
                Blocks(Paragraph(Text("Here the index type has a Fintype instance and every component is finite. The sum runs over that index type. The equivalence with the dependent disjoint union is equivSigma, and the general Nat.card equality is "),
                    Ref(Prefix + "card_join"), Text(".")))),
            Node("top-sphere-count", "The top sphere contains all points outside the component", "sphere_top_card",
                Disp(Seq(Card(Call("sphere", JPoint(), F.Id("a"))), Sp, Eq, Sp,
                    Card(F.Id("J")), Sp, Minus, Sp, Card(Call("X", F.Id("i"))))),
                Blocks(Paragraph(Text("Assume a finite index type, finite components, and the strict component-distance bound. For every i and x in X i the displayed subtraction is natural-number subtraction, exactly as in Nat.card. No nonemptiness assumption on other components is hidden in the formula.")))),
            Node("center-away-from-top", "Central radii away from the join radius are common component radii", "mem_center_iff",
                Disp(Seq(F.Id("t"), Sp, InMacro, Sp, Call("center", F.Id("J")), Sp, Iff, Sp,
                    D(0), Sp, Leq, Sp, F.Id("t"), Sp, Land, Sp, Forall, Sp, F.Id("i"), Comma, Sp,
                    F.Id("t"), Sp, InMacro, Sp, Call("center", Call("X", F.Id("i"))))),
                Blocks(Paragraph(Text("For every real t different from a, the equivalence holds under the original non-strict component bound. The separate nonnegativity condition is retained, including when the index type is empty.")))),
            Node("center-at-top", "The join radius is central exactly when each occupied component has another occupied component",
                "top_mem_center_iff",
                Disp(Seq(F.Id("a"), Sp, InMacro, Sp, Call("center", F.Id("J")), Sp, Iff, Sp,
                    Forall, Sp, F.Id("i"), Comma, Sp, Forall, Sp, F.Id("x"), Colon, Call("X", F.Id("i")), Comma, Sp,
                    Exists, Sp, F.Id("j"), Comma, Sp, Call("Nonempty", Call("X", F.Id("j"))),
                    Sp, Land, Sp, F.Id("j"), Sp, Neq, Sp, F.Id("i"))),
                Blocks(Paragraph(Text("The strict component-distance bound is assumed. The implication from an element of X i retains the vacuous empty-component cases. In particular the formula also applies to an empty join or to a join with a single index; it does not silently require two occupied components.")))),
            Node("exact-center", "The exact distance center separates the join radius from the other radii", "center_eq",
                Disp(Seq(Call("center", F.Id("J")), Sp, Eq, Sp,
                    OpenBrace, F.Id("t"), Sp, Mid, Sp, D(0), Sp, Leq, Sp, F.Id("t"), Sp, Land, Sp,
                    F.Id("t"), Sp, Neq, Sp, F.Id("a"), Sp, Land, Sp, Forall, Sp, F.Id("i"), Comma, Sp,
                    F.Id("t"), Sp, InMacro, Sp, Call("center", Call("X", F.Id("i"))), CloseBrace,
                    Sp, Cup, Sp, OpenBrace, F.Id("t"), Sp, Mid, Sp, F.Id("t"), Sp, Eq, Sp, F.Id("a"),
                    Sp, Land, Sp, Forall, Sp, F.Id("i"), Comma, Sp, Forall, Sp, F.Id("x"), Colon, Call("X", F.Id("i")), Comma,
                    Sp, Exists, Sp, F.Id("j"), Comma, Sp, Call("Nonempty", Call("X", F.Id("j"))),
                    Sp, Land, Sp, F.Id("j"), Sp, Neq, Sp, F.Id("i"), CloseBrace)),
                Blocks(Paragraph(Text("Under strict component-distance bounds, this set equality combines the two preceding equivalences. It uses the original distance center and keeps every empty-index and empty-component case. The prescribed-count construction uses this formula at the outer join and the componentwise equivalence mem_center_iff at the inner joins.")))))));

    private static DocumentBlock Node(string id, string title, string name, Formula formula, BlockSequence narrative) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(formula), AssessedProvenance.FromRepo(), narrative, DescribeRole.Theorem);

    private static Formula Card(Formula set) => Call("card", set);
    private static Formula JPoint() => Seq(Langle, Sp, F.Id("i"), Comma, F.Id("x"), Sp, Rangle);
}
