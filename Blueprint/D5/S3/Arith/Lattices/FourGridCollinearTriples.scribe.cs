using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Lattices;

internal sealed class FourGridCollinearTriplesDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Lattices/FourGridCollinearTriples.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Analytic/mathar2010a178294");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Collinear triples in every finite Cartesian power of the four-point grid have an exact count.",
        H("Collinear Triples in the Four-Point Grid"),
        Blocks(
            Paragraph(Text(
                "The grid has four coordinates on each axis. Collinearity is expressed over "
                + "the integers by the vanishing of every two-by-two minor, while cardinality "
                + "three makes each counted subset unordered and distinct.")),
            Node("GridPoint", "The four-point Cartesian grid", GridPointFormula(),
                "A point assigns one of the four values in Fin(4) to each of d coordinates.",
                DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("Collinear", "Integral collinearity", CollinearFormula(),
                "For every ordered pair of coordinates, the two displacement vectors have "
                + "zero integral minor. Both coordinate binders range over Fin(d).",
                DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("IsCollinearTriple", "Unordered distinct collinear triples",
                IsCollinearTripleFormula(),
                "The finset has exactly three elements, and every ordered selection of three "
                + "members satisfies the integral minor equations.",
                DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("matharCount", "The sequence count", MatharCountFormula(),
                "The count is the cardinality of the collinear members of powersetCard(3) "
                + "applied to the full four-point d-grid.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("SameParity", "Same-parity endpoint coordinates", SameParityFormula(),
                "The two natural representatives have equal remainders modulo two.",
                DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("instDecidableRelFinOfNatNatSameParity", "Decidability of same-parity coordinates",
                SameParityDecidableFormula(),
                "The anonymous instance command generates this auto-named declaration; unfolding "
                + "SameParity reduces it to a decidable arithmetic condition.",
                DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("EqualOrExtreme", "Equal-or-extreme endpoint coordinates",
                EqualOrExtremeFormula(),
                "A permitted pair is equal, zero-to-three, or three-to-zero.",
                DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("instDecidableRelFinOfNatNatEqualOrExtreme",
                "Decidability of equal-or-extreme coordinates",
                EqualOrExtremeDecidableFormula(),
                "The anonymous instance command generates this auto-named declaration; unfolding "
                + "EqualOrExtreme reduces it to decidable equality and arithmetic conditions.",
                DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("CoordinatePairs", "Coordinatewise endpoint pairs", CoordinatePairsFormula(),
                "Each ordered pair of grid points satisfies the supplied relation at every coordinate.",
                DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("DistinctCoordinatePairs", "Distinct coordinatewise endpoint pairs",
                DistinctCoordinatePairsFormula(),
                "This subtype removes exactly the diagonal endpoint pairs.",
                DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("midpointCoordinate", "Integral midpoint coordinate",
                MidpointCoordinateFormula(),
                "The value is natural division of the endpoint sum by two. Its bound below four "
                + "supplies the dependent Fin(4) component.",
                DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("midpoint", "Coordinatewise midpoint", MidpointFormula(),
                "The point is obtained by applying midpointCoordinate independently on every axis.",
                DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("OrientedArithmeticProgression", "Oriented arithmetic progressions",
                OrientedArithmeticProgressionFormula(),
                "The endpoints differ, and their coordinatewise integral sum is twice the middle point.",
                DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("endpoint_pair_counts", "Counts of the two endpoint-code families",
                EndpointPairCountsFormula(),
                "There are 8^d same-parity coordinate pairs and 6^d equal-or-extreme pairs. "
                + "Removing the 4^d diagonal pairs gives both displayed conjuncts.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("oriented_arithmetic_progression_count",
                "Count of oriented arithmetic progressions",
                OrientedArithmeticProgressionCountFormula(),
                "A same-parity ordered endpoint pair has one integral midpoint, and every "
                + "oriented nonconstant arithmetic progression recovers its endpoint pair.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("mathar_collinear_triples", "Mathar's closed form",
                MatharCollinearTriplesFormula(),
                "Marked collinear triples split bijectively into oriented arithmetic progressions "
                + "and two orientations of the equal-or-extreme endpoint codes. Cardinality "
                + "transfer and the two preceding counts give the identity. The subtraction on "
                + "the right is natural-number truncated subtraction, exactly as written.",
                DescribeRole.Theorem, AssessedProvenance.FromLiterature(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a178294-four-grid-collinear-triples"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock.Describe Node(string name, string title, Formula formula,
        string prose, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? claim = null) => Describe.Lean(
        DescribeId.Create("a178294-" + name.Replace('_', '-').ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
        provenance, Blocks(Paragraph(Text(prose))), role, claim);

    private static Formula GridPointFormula()
    {
        var d = F.Id("d");
        return Disp(Bound([d], Naturals(), Equal(Call("GridPoint", d),
            Seq(Call("Fin", d), Sp, To, Sp, Call("Fin", D(4))))));
    }

    private static Formula CollinearFormula()
    {
        var d = F.Id("d"); var x = F.Id("x"); var y = F.Id("y"); var z = F.Id("z");
        var i = F.Id("i"); var j = F.Id("j");
        var left = Multiply(
            Subtract(IntCoordinate(y, i), IntCoordinate(x, i)),
            Subtract(IntCoordinate(z, j), IntCoordinate(x, j)));
        var right = Multiply(
            Subtract(IntCoordinate(y, j), IntCoordinate(x, j)),
            Subtract(IntCoordinate(z, i), IntCoordinate(x, i)));
        return Disp(Bound([d], Naturals(), Bound([x, y, z], Call("GridPoint", d),
            Seq(Call("Collinear", x, y, z), Sp, Iff, Sp,
                Parenthesized(Bound([i, j], Call("Fin", d), Equal(left, right)))))));
    }

    private static Formula IsCollinearTripleFormula()
    {
        var d = F.Id("d"); var s = F.Id("s");
        var x = F.Id("x"); var y = F.Id("y"); var z = F.Id("z");
        var members = InSet(x, s, InSet(y, s, InSet(z, s, Call("Collinear", x, y, z))));
        return Disp(Bound([d], Naturals(), Bound([s], FinsetOf(Call("GridPoint", d)),
            Seq(Call("IsCollinearTriple", s), Sp, Iff, Sp,
                Parenthesized(Conjunction(Equal(Call("card", s), D(3)), members))))));
    }

    private static Formula MatharCountFormula()
    {
        var d = F.Id("d");
        var grid = Typed(Name("univ"), FinsetOf(Call("GridPoint", d)));
        var triples = Call("powersetCard", D(3), Parenthesized(grid));
        var selected = Call("filter", Name("IsCollinearTriple"), triples);
        return Disp(Bound([d], Naturals(),
            Equal(Call("matharCount", d), Call("card", selected))));
    }

    private static Formula SameParityFormula()
    {
        var a = F.Id("a"); var b = F.Id("b");
        return Disp(Bound([a, b], Call("Fin", D(4)),
            Seq(Call("SameParity", a, b), Sp, Iff, Sp,
                Equal(Call("natMod", Call("val", a), D(2)),
                    Call("natMod", Call("val", b), D(2))))));
    }

    private static Formula SameParityDecidableFormula() =>
        Disp(Parenthesized(Call("DecidableRel", F.Id("SameParity"))));

    private static Formula EqualOrExtremeFormula()
    {
        var a = F.Id("a"); var b = F.Id("b");
        var forward = Conjunction(Equal(Call("val", a), D(0)), Equal(Call("val", b), D(3)));
        var reverse = Conjunction(Equal(Call("val", a), D(3)), Equal(Call("val", b), D(0)));
        return Disp(Bound([a, b], Call("Fin", D(4)),
            Seq(Call("EqualOrExtreme", a, b), Sp, Iff, Sp,
                Parenthesized(Disjunction(Equal(a, b), forward, reverse)))));
    }

    private static Formula EqualOrExtremeDecidableFormula() =>
        Disp(Parenthesized(Call("DecidableRel", F.Id("EqualOrExtreme"))));

    private static Formula CoordinatePairsFormula()
    {
        var relation = F.Id("relation"); var d = F.Id("d");
        var p = F.Id("p"); var i = F.Id("i");
        var point = Call("GridPoint", d);
        var property = Bound([i], Call("Fin", d), Apply(relation,
            Apply(Call("fst", p), i), Apply(Call("snd", p), i)));
        var carrier = Product(point, point);
        return Disp(Bound([relation], RelationType(), Bound([d], Naturals(),
            Equal(Call("CoordinatePairs", relation, d), SetBuilder(p, carrier, property)))));
    }

    private static Formula DistinctCoordinatePairsFormula()
    {
        var relation = F.Id("relation"); var d = F.Id("d"); var p = F.Id("p");
        var endpoints = Call("val", p);
        var property = NotEqual(Call("fst", endpoints), Call("snd", endpoints));
        return Disp(Bound([relation], RelationType(), Bound([d], Naturals(),
            Equal(Call("DistinctCoordinatePairs", relation, d),
                SetBuilder(p, Call("CoordinatePairs", relation, d), property)))));
    }

    private static Formula MidpointCoordinateFormula()
    {
        var a = F.Id("a"); var b = F.Id("b");
        var value = Call("natDiv", Add(Call("val", a), Call("val", b)), D(2));
        return Disp(Bound([a, b], Call("Fin", D(4)),
            Equal(Call("val", Call("midpointCoordinate", a, b)), value)));
    }

    private static Formula MidpointFormula()
    {
        var d = F.Id("d"); var x = F.Id("x"); var z = F.Id("z"); var i = F.Id("i");
        return Disp(Bound([d], Naturals(), Bound([x, z], Call("GridPoint", d),
            Bound([i], Call("Fin", d), Equal(Apply(Call("midpoint", x, z), i),
                Call("midpointCoordinate", Apply(x, i), Apply(z, i)))))));
    }

    private static Formula OrientedArithmeticProgressionFormula()
    {
        var d = F.Id("d"); var t = F.Id("t"); var i = F.Id("i");
        var x = Call("fst", t); var y = Call("fst", Call("snd", t));
        var z = Call("snd", Call("snd", t));
        var carrier = Product(Call("GridPoint", d),
            Parenthesized(Product(Call("GridPoint", d), Call("GridPoint", d))));
        var affine = Bound([i], Call("Fin", d), Equal(
            Add(IntCoordinate(x, i), IntCoordinate(z, i)),
            Multiply(D(2), IntCoordinate(y, i))));
        return Disp(Bound([d], Naturals(), Equal(Call("OrientedArithmeticProgression", d),
            SetBuilder(t, carrier, Conjunction(NotEqual(x, z), affine)))));
    }

    private static Formula EndpointPairCountsFormula()
    {
        var d = F.Id("d");
        var parity = Equal(Call("card", Call("DistinctCoordinatePairs", Name("SameParity"), d)),
            Subtract(Power(D(8), d), Power(D(4), d)));
        var extreme = Equal(Call("card", Call("DistinctCoordinatePairs", Name("EqualOrExtreme"), d)),
            Subtract(Power(D(6), d), Power(D(4), d)));
        return Disp(Bound([d], Naturals(), Conjunction(parity, extreme)));
    }

    private static Formula OrientedArithmeticProgressionCountFormula()
    {
        var d = F.Id("d");
        return Disp(Bound([d], Naturals(), Equal(
            Call("card", Call("OrientedArithmeticProgression", d)),
            Subtract(Power(D(8), d), Power(D(4), d)))));
    }

    private static Formula MatharCollinearTriplesFormula()
    {
        var d = F.Id("d");
        var left = Multiply(D(2), Call("matharCount", d));
        var right = Subtract(
            Add(Power(D(8), d), Multiply(D(2), Power(D(6), d))),
            Multiply(D(3), Power(D(4), d)));
        return Disp(Bound([d], Naturals(), Equal(left, right)));
    }

    private static Formula RelationType() => Seq(Call("Fin", D(4)), Sp, To, Sp,
        Call("Fin", D(4)), Sp, To, Sp, Name("Prop"));
    private static Formula FinsetOf(Formula type) => Call("Finset", type);
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Name(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Typed(Formula value, Formula type) =>
        Parenthesized(Seq(value, Sp, Colon, Sp, type));
    private static Formula Product(Formula left, Formula right) => Seq(left, Sp, Times, Sp, right);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula SetBuilder(Formula variable, Formula type, Formula property) =>
        Seq(OpenBrace, variable, Sp, Colon, Sp, type, Sp, Mid, Sp, property, CloseBrace);
    private static Formula Bound(Formula[] variables, Formula type, Formula body) =>
        Seq(Forall, Sp, Joined(variables, Comma), Sp, Colon, Sp, type, Comma, Sp, body);
    private static Formula InSet(Formula variable, Formula set, Formula body) =>
        Seq(Forall, Sp, variable, Sp, InMacro, Sp, set, Comma, Sp, body);
    private static Formula IntCoordinate(Formula point, Formula index) =>
        Call("intCast", Call("val", Apply(point, index)));
    private static Formula Apply(Formula function, params Formula[] arguments)
    {
        List<Formula> items = [function, Open];
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
    private static Formula Equal(Formula left, Formula right) => Seq(left, Sp, Eq, Sp, right);
    private static Formula NotEqual(Formula left, Formula right) => Seq(left, Sp, Neq, Sp, right);
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Power(Formula value, Formula exponent) => new Formula.Power(value, exponent);
    private static Formula Conjunction(params Formula[] values) => Joined(values, Land);
    private static Formula Disjunction(params Formula[] values) => Joined(values, Lor);
    private static Formula Joined(Formula[] values, Formula separator)
    {
        List<Formula> items = [];
        for (var index = 0; index < values.Length; index++)
        {
            if (index > 0) items.AddRange([Sp, separator, Sp]);
            items.Add(values[index]);
        }
        return Seq([.. items]);
    }
}
