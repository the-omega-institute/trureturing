using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Lattices;

internal sealed class ThinCheckerboardNoThreeInLineSeventeenDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Arith/Lattices/ThinCheckerboardNoThreeInLineSeventeen.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The odd-parity class of the 17 by 17 integer grid has no-three-in-line optimum 26.",
        H("Thin Checkerboard of Side Seventeen"),
        Blocks(
            Declaration("Point", "Integer lattice points",
                Equal(Name("Point"), Product(Integers(), Integers())),
                "Point abbreviates Prod Int Int; its two coordinates are integers.",
                DescribeRole.Definition),
            Declaration("LineKey", "Integer line equations",
                Equal(Name("LineKey"), Product(Integers(),
                    Parenthesized(Product(Integers(), Integers())))),
                "LineKey abbreviates Prod Int (Prod Int Int). The nested pair (a,(b,c)) represents a*x+b*y=c; properness is proved privately for every certificate line.",
                DescribeRole.Definition),
            Declaration("det", "Displacement determinant", DeterminantFormula(),
                "The defining expression is the integer determinant of q-p and r-p, exactly as in GICT Theorem 3.4.16. Subscripts denote the first and second integer coordinates.",
                DescribeRole.Definition),
            Declaration("Thin", "Odd-parity grid membership", ThinFormula(),
                "Both coordinates lie between zero and sixteen. intMod denotes Lean integer remainder, so the last equality expresses odd coordinate sum.",
                DescribeRole.Definition),
            Declaration("NTIL", "All-slopes no-three-in-line", NtilFormula(),
                "This predicate ranges over every ordered triple of members and requires nonzero integer determinant whenever the three points are pairwise distinct. It imposes no restriction on slopes.",
                DescribeRole.Definition),
            Declaration("onLine", "Integer line incidence", IncidenceFormula(),
                "fst and snd are product projections. Incidence is the displayed integer equation, with no geometric Collinear predicate involved.",
                DescribeRole.Definition),
            Declaration("witness", "The explicit point certificate",
                Typed(Name("witness"), PointSets()),
                "The defining finite set is the fixed list of 26 integer points in the Lean source, copied unchanged from the preregistered certificate. It is kernel-decided finite data; the three following theorems check cardinality, thin membership, and all distinct triples. The entries are not duplicated in this mirror.",
                DescribeRole.Definition),
            Declaration("weightedLines", "The weighted line certificate",
                Typed(Name("weightedLines"), Call("List",
                    Product(Name("LineKey"), Naturals()))),
                "The defining list contains the fixed 40 pairs of integer line coefficients and natural weights from the preregistered certificate, unchanged. These are kernel-decided finite data, not an assumed optimizer output. The entries are not duplicated here; the weights sum to 320 and the required coverage scale is 24.",
                DescribeRole.Definition),
            Declaration("witness_card", "The witness has 26 points",
                Equal(Call("card", Name("witness")), D(2, 6)),
                "Kernel reduction counts 26 distinct points.", DescribeRole.Theorem),
            Declaration("witness_thin", "Every witness point is thin",
                AllThin(Name("witness")),
                "Kernel reduction checks the coordinate bounds and odd parity for all 26 entries.",
                DescribeRole.Theorem),
            Declaration("witness_ntil", "Every distinct witness triple is noncollinear",
                Call("NTIL", Name("witness")),
                "Kernel reduction verifies every distinct ordered triple; equivalently all 2600 unordered triples have nonzero determinant. No native_decide is used.",
                DescribeRole.Theorem),
            Declaration("line", "Line at a certificate index", IndexedFormula("line", "fst"),
                "get is zero-based list lookup at val(i). Lean transports i from Fin 40 to Fin weightedLines.length using the kernel-checked length equality before taking the first projection.",
                DescribeRole.Definition),
            Declaration("weight", "Weight at a certificate index", IndexedFormula("weight", "snd"),
                "The same zero-based lookup and length transport is followed by the second projection, yielding a natural number.",
                DescribeRole.Definition),
            Declaration("cover", "Total incident line weight", CoverFormula(),
                "The sum is over all forty indices and takes natural values. ite(P,a,b) equals a when P holds and b otherwise.",
                DescribeRole.Definition),
            Declaration("weight_sum", "Total certificate weight",
                Equal(IndexedSum(Call("weight", F.Id("i"))), D(3, 2, 0)),
                "The Lean kernel checks the sum of the forty natural weights.", DescribeRole.Theorem),
            Declaration("cover_grid", "Every thin grid point has coverage at least 24",
                CoverGridFormula(),
                "val maps Fin 17 to the naturals, natMod denotes natural remainder, and ofNat explicitly embeds each coordinate into the integers before cover is applied. Kernel enumeration checks the whole 17 by 17 grid under its parity premise.",
                DescribeRole.Theorem),
            Declaration("upper_bound", "Every admissible set has at most 26 points",
                UpperFormula(F.Id("S")),
                "A proper integer line carries at most two points of an NTIL set. Double counting weighted incidences therefore gives 24*card(S) <= 2*320 = 640, and natural arithmetic yields card(S) <= 26.",
                DescribeRole.Theorem),
            Declaration("thinCheckerboard17_ntil_max_eq_26", "Exact optimum: attainment and universal bound",
                OptimumFormula(),
                "GICT Theorem 3.4.16 is mirrored as one conjunction: an admissible 26-point set exists and every admissible set has at most 26 points. Both preregistered escape certificates from Remark 3.4.17 are live in the proof; the remark is not claimed as covered. This exact finite result is derived in this repository. Prellberg, arXiv:2605.09215, Definition 2, Table 1, and Section 4 supply the problem context: Table 1 gives exact thin-checkerboard maxima through n=16, ending at 24. The present claim is only for n=17 and its odd-parity class. It asserts neither a result for other n nor a bridge to Mathlib Collinear, and makes no global novelty claim.",
                DescribeRole.Theorem))));

    private static DocumentBlock.Describe Declaration(
        string name, string title, Formula formula, string prose, DescribeRole role) =>
        Describe.Lean(
            DescribeId.Create(name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);

    private static Formula DeterminantFormula()
    {
        var p = F.Id("p"); var q = F.Id("q"); var r = F.Id("r");
        Formula Difference(Formula x, Formula y, byte coordinate) =>
            Parenthesized(Seq(Coordinate(x, coordinate), Sp, Minus, Sp, Coordinate(y, coordinate)));
        return Bound([p, q, r], Name("Point"),
            Equal(Call("det", p, q, r), Seq(
                Difference(q, p, 1), Sp, Cdot, Sp, Difference(r, p, 2),
                Sp, Minus, Sp,
                Difference(q, p, 2), Sp, Cdot, Sp, Difference(r, p, 1))));
    }

    private static Formula ThinFormula()
    {
        var p = F.Id("p");
        return Bound([p], Name("Point"), Seq(Call("Thin", p), Sp, Iff, Sp,
            Parenthesized(Conjunction(
                Seq(D(0), Sp, Leq, Sp, Coordinate(p, 1)),
                Seq(Coordinate(p, 1), Sp, Leq, Sp, D(1, 6)),
                Seq(D(0), Sp, Leq, Sp, Coordinate(p, 2)),
                Seq(Coordinate(p, 2), Sp, Leq, Sp, D(1, 6)),
                Equal(Call("intMod", Seq(Coordinate(p, 1), Sp, Plus, Sp, Coordinate(p, 2)), D(2)), D(1))))));
    }

    private static Formula NtilFormula()
    {
        var s = F.Id("S"); var p = F.Id("p"); var q = F.Id("q"); var r = F.Id("r");
        return Bound([s], PointSets(), Seq(Call("NTIL", s), Sp, Iff, Sp,
            Parenthesized(Seq(
                Forall, Sp, p, Sp, InMacro, Sp, s, Comma, Sp,
                Forall, Sp, q, Sp, InMacro, Sp, s, Comma, Sp,
                Forall, Sp, r, Sp, InMacro, Sp, s, Comma, Sp,
                NotEqual(p, q), Sp, Rightarrow, Sp,
                NotEqual(p, r), Sp, Rightarrow, Sp,
                NotEqual(q, r), Sp, Rightarrow, Sp,
                NotEqual(Call("det", p, q, r), D(0))))));
    }

    private static Formula IncidenceFormula()
    {
        var p = F.Id("p"); var l = F.Id("l");
        return Bound([p], Name("Point"), Bound([l], Name("LineKey"),
            Seq(Call("onLine", p, l), Sp, Iff, Sp,
                Equal(Seq(Call("fst", l), Sp, Cdot, Sp, Coordinate(p, 1), Sp, Plus, Sp,
                    Call("fst", Call("snd", l)), Sp, Cdot, Sp, Coordinate(p, 2)),
                    Call("snd", Call("snd", l))))));
    }

    private static Formula IndexedFormula(string name, string projection)
    {
        var i = F.Id("i");
        return Bound([i], Call("Fin", D(4, 0)), Equal(Call(name, i),
            Call(projection, Call("get", Name("weightedLines"), Call("val", i)))));
    }

    private static Formula CoverFormula()
    {
        var p = F.Id("p"); var i = F.Id("i");
        return Bound([p], Name("Point"), Equal(Call("cover", p),
            IndexedSum(Call("ite", Call("onLine", p, Call("line", i)), Call("weight", i), D(0)))));
    }

    private static Formula CoverGridFormula()
    {
        var x = F.Id("x"); var y = F.Id("y");
        return Bound([x, y], Call("Fin", D(1, 7)), Seq(
            Equal(Call("natMod", Seq(Call("val", x), Sp, Plus, Sp, Call("val", y)), D(2)), D(1)),
            Sp, Rightarrow, Sp, D(2, 4), Sp, Leq, Sp,
            Call("cover", Parenthesized(Seq(Call("ofNat", Call("val", x)), Comma, Sp,
                Call("ofNat", Call("val", y)))))));
    }

    private static Formula UpperFormula(Formula s) =>
        Bound([s], PointSets(), Seq(Parenthesized(AllThin(s)), Sp, Rightarrow, Sp,
            Call("NTIL", s), Sp, Rightarrow, Sp,
            Call("card", s), Sp, Leq, Sp, D(2, 6)));

    private static Formula OptimumFormula()
    {
        var s = F.Id("S"); var t = F.Id("T");
        var attained = Seq(Exists, Sp, Typed(s, PointSets()), Comma, Sp,
            Parenthesized(AllThin(s)), Sp, Land, Sp,
            Equal(Call("card", s), D(2, 6)), Sp, Land, Sp, Call("NTIL", s));
        return Seq(Parenthesized(attained), Sp, Land, Sp, Parenthesized(UpperFormula(t)));
    }

    private static Formula AllThin(Formula s) =>
        Seq(Forall, Sp, F.Id("p"), Sp, InMacro, Sp, s, Comma, Sp, Call("Thin", F.Id("p")));

    private static Formula IndexedSum(Formula term) =>
        Seq(new Formula.Subscript(Sum, Typed(F.Id("i"), Call("Fin", D(4, 0)))), Sp, term);

    private static Formula Bound(Formula[] variables, Formula type, Formula body) =>
        Seq(Forall, Sp, Joined(variables, Comma), Sp, Colon, Sp, type, Comma, Sp, body);

    private static Formula PointSets() => Call("Finset", Name("Point"));
    private static Formula Integers() => Seq(Mathbb, Grp(F.Id("Z")));
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Name(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Typed(Formula value, Formula type) => Seq(value, Sp, Colon, Sp, type);
    private static Formula Product(Formula left, Formula right) => Seq(left, Sp, Times, Sp, right);
    private static Formula Coordinate(Formula point, byte index) => new Formula.Subscript(point, D(index));
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
    private static Formula Conjunction(params Formula[] values) => Joined(values, Land);

    private static Formula Joined(Formula[] values, Formula separator)
    {
        List<Formula> items = [];
        for (int index = 0; index < values.Length; index++)
        {
            if (index > 0) items.AddRange([Sp, separator, Sp]);
            items.Add(values[index]);
        }
        return Seq([.. items]);
    }
}
