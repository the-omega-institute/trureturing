using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.GraphInvariants.Simplicial;

internal sealed class FiniteJoinSuspensionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/GraphInvariants/Simplicial/FiniteJoinSuspension.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The geometric join with two isolated points is the ordinary suspension of a nonempty finite polyhedron.",
        H("Finite geometric joins and ordinary suspension"),
        Blocks(
            Definition("geometric-carrier", "geometricCarrier", "The usual finite polyhedron",
                "For every finite vertex type V and precomplex K, place vertex i at "
                + "the coordinate vector with coordinate one at i and zero elsewhere. "
                + "The carrier is the union, over the nonempty faces of K, of their "
                + "closed convex hulls in the real product indexed by V. A coordinate "
                + "vector belongs exactly when all its coordinates are nonnegative, "
                + "their sum is one, and its true nonzero support is a face of K. "
                + "The coordinate equivalence from finitely supported functions to "
                + "the finite product transports Mathlib's onFinsupp polyhedron and "
                + "the sourced simplex characterization to this literal union."),
            Definition("true-coordinate-support", "support", "The true nonzero support",
                "For a finite vertex type V with decidable equality and a real "
                + "coordinate vector x, support x consists exactly of the vertices "
                + "i for which x at i is nonzero. Zero coordinates are omitted. "
                + "For a point of the carrier, every vertex whose singleton is "
                + "absent has coordinate zero and is omitted from its support."),
            Describe.Lean(DescribeId.Create("geometric-carrier-membership"),
                DeclarationHandle.Create(Prefix + "mem_geometricCarrier_iff"),
                H("Membership by barycentric coordinates and true support"),
                StatementSource.FromAuthor(MembershipFormula()),
                AssessedProvenance.FromLiterature(
                    LibraryNoteRef.Create("D5/L/GraphInvariants/tauceti2026finitejoinsuspension")),
                Blocks(Paragraph(Text(
                    "For every finite vertex type V with decidable equality, every "
                    + "precomplex K on V and every real coordinate vector x, membership "
                    + "in the literal union of closed face hulls is equivalent to "
                    + "coordinate nonnegativity, total coordinate sum one, and the "
                    + "true nonzero support being a face of K. No nonemptiness or "
                    + "full-vertex hypothesis is imposed: for an empty carrier both "
                    + "sides are false, and ghost coordinates must vanish. The finite "
                    + "coordinate equivalence transports the sourced finitely "
                    + "supported characterization. This criterion characterizes "
                    + "join coordinates and verifies the suspension coordinate "
                    + "map and its normalized base points."))), DescribeRole.Theorem),
            Definition("geometric-realization", "GeometricRealization", "The Euclidean subspace topology",
                "The realization is the carrier with the subspace topology from "
                + "the finite real product. It is compact, since each closed face "
                + "simplex is compact and there are finitely many faces. It is "
                + "Hausdorff as a subspace of that real product. A vertex whose "
                + "singleton is absent contributes no points to the carrier."),
            Describe.Lean(DescribeId.Create("precomplex-join"),
                DeclarationHandle.Create(Prefix + "join"), H("The disjoint vertex join"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(
                    LibraryNoteRef.Create("D5/L/GraphInvariants/tauceti2026finitejoinsuspension")),
                Blocks(Paragraph(Text(
                    "For arbitrary precomplexes K and L, a finite set of tagged vertices "
                    + "is a join face precisely when it is nonempty and each projection "
                    + "is either empty or a face of its factor. Empty contributions "
                    + "are allowed independently. The join and the coordinate-support "
                    + "characterizations follow TauCeti at revision "
                    + "64bb4d871548995899dee90beda88b787fafe27d, in Join/Basic and "
                    + "Realization/Basic and Realization/Coordinates."))), DescribeRole.Definition),
            Definition("two-isolated-points", "D2", "The two-point factor",
                "D2 is the bottom abstract simplicial complex on Fin two, "
                + "regarded as a precomplex. Its faces are the two singletons; "
                + "the edge is absent. Thus a point of the geometric join has "
                + "at most one nonzero pole coordinate. Bottom as a precomplex "
                + "instead has no faces and is a different object."),
            Definition("height-interval", "Height", "The closed height interval",
                "Height is the closed real interval from minus one to one, "
                + "with its real subspace topology."),
            Definition("endpoint-relation", "suspensionSetoid", "Collapse the endpoint fibres separately",
                "For every topological space X, take the cylinder of X with "
                + "the closed real interval from minus one to one. Two cylinder "
                + "points are related precisely when their heights agree and "
                + "that common height is an endpoint or their base points agree. "
                + "This equivalence relation is specified independently of any "
                + "map into a geometric realization. Opposite endpoints have "
                + "different heights and remain distinct whenever X is nonempty."),
            Definition("ordinary-suspension", "OrdinarySuspension", "The ordinary unreduced suspension",
                "The ordinary suspension of X is the quotient of that cylinder "
                + "by the endpoint relation, with the quotient topology. If X "
                + "is empty, the cylinder and its quotient are both empty."),
            Definition("suspension-coordinates", "suspensionCoordinates", "The barycentric coordinate map",
                "For a base point x and height s, give base vertex i coordinate "
                + "(one minus the absolute value of s) times x at i. Give pole "
                + "zero coordinate max of s and zero, and pole one coordinate "
                + "max of minus s and zero. The coordinates are nonnegative "
                + "and sum to one. The base support is either the support of "
                + "x or empty, and at most one pole occurs, so the true support "
                + "is a face of the join."),
            Definition("cylinder-map", "suspensionMap", "A continuous map into the actual join",
                "The coordinate map takes every cylinder point to the literal "
                + "Euclidean realization of the join. Absolute value, maximum "
                + "and coordinate multiplication give continuity. No "
                + "connectedness or requirement that every ambient vertex be "
                + "used is imposed."),
            Describe.Lean(DescribeId.Create("exact-endpoint-fibres"),
                DeclarationHandle.Create(Prefix + "suspensionMap_fibres"),
                H("The fibres are exactly the ordinary suspension relation"),
                StatementSource.FromAuthor(FibresFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Equality of pole coordinates recovers the common height as "
                    + "their difference. At either endpoint the remaining base "
                    + "mass is zero. Away from the endpoints it is strictly "
                    + "positive, and equality of scaled coordinates recovers "
                    + "the base point. Conversely, equivalent cylinder points "
                    + "have the same coordinates. This statement includes "
                    + "empty realizations without a nonemptiness hypothesis."))), DescribeRole.Theorem),
            Definition("quotient-map", "suspensionQuotientMap", "Descend to the endpoint quotient",
                "The exact fibre identity allows the continuous cylinder map "
                + "to descend to the ordinary suspension. The descended map "
                + "is injective. For a join point with base coordinates z and "
                + "pole masses a and b, set s to a minus b. One pole mass "
                + "vanishes, so the absolute value of s is a plus b. If the "
                + "remaining mass is positive, divide z by one minus the "
                + "absolute value of s to obtain its unique base point. If "
                + "that mass is zero, all base coordinates vanish and any "
                + "existing base point maps to the required pure pole."),
            Describe.Lean(DescribeId.Create("join-suspension-homeomorphism"),
                DeclarationHandle.Create(Prefix + "joinSuspensionHomeomorph"),
                H("The finite geometric join is the ordinary suspension"),
                StatementSource.FromAuthor(HomeomorphFormula()), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every finite vertex type V, every precomplex K on V "
                        + "and a nonempty realization of K, the construction gives "
                        + "a Homeomorph from the geometric realization of the "
                        + "join with D2 to the ordinary suspension of K's "
                        + "realization. The inverse is the descended coordinate "
                        + "map. The cylinder quotient is compact; a continuous "
                        + "bijection from it to the Hausdorff join realization "
                        + "is a homeomorphism.")),
                    Paragraph(Text(
                        "Nonemptiness is essential. For the empty precomplex, "
                        + "including on Fin zero, the realization and its "
                        + "cylinder quotient are empty, but its join with D2 "
                        + "has the two pure poles. No negative-dimensional "
                        + "sphere is introduced.")),
                    Paragraph(Text(
                        "For path independence complexes at N at least one, "
                        + "this identifies the ordinary suspension once the "
                        + "exact relabelled deletion is the specified join. "
                        + "The exact path collapse and relabelling, its "
                        + "geometric homotopy equivalence, the path recurrence, "
                        + "the base cases and the full classification by "
                        + "residue modulo three are additional assertions."))), DescribeRole.Definition)), []));

    private static DocumentBlock Definition(string id, string declaration, string title, string prose) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var i = 0; i < arguments.Length; i++)
        {
            if (i > 0) { items.Add(Comma); items.Add(Sp); }
            items.Add(arguments[i]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, F.Id(name), Sp, Colon, Sp, type, Comma, Sp, body);
    private static Formula Realization => Call("GeometricRealization", F.Id("K"));
    private static Formula BindComplex(Formula body) => All("V", F.Id("Type"),
        Seq(OpenBracket, Call("Fintype", F.Id("V")), CloseBracket, Sp,
            OpenBracket, Call("DecidableEq", F.Id("V")), CloseBracket, Sp,
            All("K", Call("PreAbstractSimplicialComplex", F.Id("V")), body)));
    private static Formula FibresFormula() => Disp(BindComplex(
        All("p", Call("Cylinder", Realization), All("q", Call("Cylinder", Realization),
            Seq(Call("suspensionMap", F.Id("p")), Sp, Eq, Sp,
                Call("suspensionMap", F.Id("q")), Sp, Iff, Sp,
                Call("suspensionSetoid", Realization, F.Id("p"), F.Id("q")))))));
    private static Formula MembershipFormula() => Disp(BindComplex(
        All("x", Seq(F.Id("V"), Sp, To, Sp, Mathbb, Grp(F.Id("R"))),
            Seq(F.Id("x"), Sp, InMacro, Sp, Call("geometricCarrier", F.Id("K")),
                Sp, Iff, Sp, Open,
                All("i", F.Id("V"), Seq(D(0), Sp, Leq, Sp, Call("x", F.Id("i")))),
                Close, Sp, Land, Sp,
                new Formula.Subscript(Sum, Seq(F.Id("i"), Sp, Colon, Sp, F.Id("V"))),
                Sp, Call("x", F.Id("i")), Sp, Eq, Sp, D(1), Sp, Land, Sp,
                Call("support", F.Id("x")), Sp, InMacro, Sp, F.Id("K")))));
    private static Formula HomeomorphFormula() => Disp(BindComplex(
        Seq(Call("Nonempty", Realization), Sp, Rightarrow, Sp,
            Call("Homeomorph", Call("GeometricRealization", Call("join", F.Id("K"), Call("Dtwo"))),
                Call("OrdinarySuspension", Realization)))));
}
