using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology;

internal sealed class CompactMidpointIntervalDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "In a compact extended metric space, exact midpoints for finite-distance pairs yield endpoint-preserving isometric real intervals for those pairs.",
        H("Isometric intervals from compact midpoints"),
        Blocks(
            Paragraph(Text("Let Y be an extended metric space with its metric topology, and assume Y is compact. Its distance d takes values in ENNReal, the nonnegative reals together with infinity. A finite-distance midpoint means a point z with d(a,z)=d(z,b)=d(a,b)/2 whenever d(a,b) is finite. This hypothesis ranges over every finite-distance pair, including pairs of equal points.")),
            Describe.Lean(DescribeId.Create("compact-midpoints-isometric-interval"),
                DeclarationHandle.Create("D5/S3/Topology/CompactMidpointInterval.compact_midpoints_isometric_interval"),
                H("A real interval with the prescribed endpoints"),
                StatementSource.FromAuthor(F.Disp(Statement())),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Topology/bridsonhaefliger1999midpoint")),
                Blocks(
                    Paragraph(Text("Types denotes the universe of Y. Real(d(a,b)) is the real value of the finite extended distance. The source interval Icc(0,L) is the closed real interval with its usual induced metric. Its start and finish are 0 and L as subtype elements, with their membership proofs. Isometry(f) means equality of extended distances for every pair in this interval, so continuity and injectivity follow from the conclusion.")),
                    Paragraph(Text("Repeatedly insert exact midpoints into a finite chain of 2^n edges. The maximum edge length is L times (1/2)^n. These chains need not be coherent across n. At every real time t, use the point with index floor(t divided by the mesh). The resulting step map has the exact endpoints, and its distance between any two times s,t is at most their real distance plus twice the mesh. The simultaneous bound at every real time is essential.")),
                    Paragraph(Text("In the compact product of copies of Y indexed by the entire interval, take the closed sets of maps having these endpoints and satisfying the all-time bound at level n. Each set is nonempty, and the geometric errors make them decreasing. Compactness gives a map in their intersection. Passing to the limit in the error proves the 1-Lipschitz bound. This uses closed-set intersection; it assumes neither sequential compactness of an uncountable product nor continuity of the step maps.")),
                    Paragraph(Text("The endpoint distance is exactly L. For ordered times s at most t, apply the triangle inequality along 0,s,t,L. The outer distances are at most s and L-t. Their sum with the middle distance is at least L, so that middle distance is at least t-s. Together with the Lipschitz upper bound this proves isometry. A zero-length interval is handled separately by equality of the endpoints.")))),
            Paragraph(Text("The space Y may be empty and may have several components at infinite mutual distance. The theorem is conditional on selected points a,b and their finite distance. It asserts no interval joining an infinite-distance pair, no finite global diameter, no uniqueness of the interval and no curvature bound.")),
            Paragraph(Text("Bridson and Haefliger, Metric Spaces of Non-Positive Curvature (1999), I.1.4(1), states the classical complete metric midpoint criterion. That remark states the criterion without a proof. The implementation here constructs intervals in a compact extended metric space by finite refinement, all-time rounding and compact product intersection. It makes no mathematical novelty claim and does not claim the complete noncompact version.")),
            Paragraph(Text("For the original gluing quotient, apply FiniteOrbitChainMidpoint.compact_original_quotient_midpoints first, retaining its single metric, original quotient topology and representative-distance equality. Compactness descends from the finite family of compact pieces to this same original quotient topology. The present theorem then constructs isometric intervals for each finite-distance pair in that metric. To obtain a specified geometric realization one must still identify its actual pieces, partial isometries, full finite orbits, splitting property and marked quotient with these data.")))));

    private static Formula Statement()
    {
        var Y = Id("Y"); var a = Id("a"); var b = Id("b"); var z = Id("z"); var f = Id("f");
        var d = Edist(a, b);
        var midpoint = All("a", Y, All("b", Y, Implies(Lt(d, F.Infty),
            Exists("z", Y, And(Eq(Edist(a, z), Half(d)), Eq(Edist(z, b), Half(d)))))));
        var L = Call("Real", d);
        var interval = Call("Icc", F.D(0), L);
        var conclusion = All("a", Y, All("b", Y, Implies(Lt(d, F.Infty),
            Exists("f", new Formula.TypeArrow(interval, Y), And(
                Call("Isometry", f), Eq(Call("f", F.D(0)), a), Eq(Call("f", L), b))))));
        return All("Y", Id("Types"),
            F.Seq(F.OpenBracket, Call("EMetricSpace", Y), F.CloseBracket, F.Sp,
                F.OpenBracket, Call("CompactSpace", Y), F.CloseBracket, F.Sp,
                Implies(midpoint, conclusion)));
    }
    private static Formula Id(string s) => F.Id(s);
    private static Formula Call(string s, params Formula[] args) => new Formula.Apply(Id(s), [.. args]);
    private static Formula All(string s, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(s), type, body);
    private static Formula Exists(string s, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(s), type, body);
    private static Formula And(params Formula[] clauses)
    {
        var result = clauses[^1];
        for (var i = clauses.Length - 2; i >= 0; i--) result = new Formula.Logic(clauses[i], FormulaLogicOperator.And, result);
        return result;
    }
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Lt(Formula a, Formula b) => F.Seq(a, F.Sp, F.Lt, F.Sp, b);
    private static Formula Implies(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Half(Formula a) => new Formula.Fraction(a, F.D(2));
    private static Formula Edist(Formula a, Formula b) => Call("edist", a, b);
}
