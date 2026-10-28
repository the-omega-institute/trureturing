using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuantumChannels;

internal sealed class GeneralizedPauliVolumeRatiosDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/QuantumChannels/GeneralizedPauliVolumeRatios";
    private static LibraryNoteRef Source =>
        LibraryNoteRef.Create("D5/L/QuadraticForms/siudzinska2020pauligeometry");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Three volume ratios for generalized Pauli eigenvalue regions hold in every natural dimension at least two.",
        H("Volume ratios for generalized Pauli channels"),
        Blocks(
            Definition("box-region", "boxRegion", "The box of positivity estimates", BoxFormula(),
                "The box consists of all real vectors x with d + 1 coordinates between −1/(d − 1) and one. "
                    + "It is the upper estimate for positive maps in GGPC_volume5.tex, lines 210–228; "
                    + "the coordinate inequalities are necessary for positivity, and are not asserted to be sufficient. "
                    + "The definition is a set for every natural d; its interpretation here uses d at least two."),
            Definition("cp-region", "cpRegion", "The complete positivity region", CpFormula(),
                "The sum of the coordinates is at least −1/(d − 1) and at most 1 + d times each coordinate. "
                    + "For d at least two, the latter family of inequalities is equivalent to the upper bound "
                    + "1 + d times the minimum coordinate in the generalized Fujiwara–Algoet condition "
                    + "of Appendix A (GGPC_volume5.tex, lines 359–364)."),
            Definition("generator-region", "generatorRegion", "The nonnegative complete positivity region", GeneratorFormula(),
                "Intersect the complete positivity region with the nonnegative orthant. "
                    + "These are the eigenvalue vectors called achievable with time-local generators "
                    + "in GGPC_volume5.tex, lines 256–267."),
            Definition("eb-region", "ebRegion", "The entanglement-breaking region with nonnegative coordinates", EbFormula(),
                "Within the nonnegative complete positivity region, impose that the coordinate sum is at most one. "
                    + "This is the source's entanglement-breaking criterion for nonnegative eigenvalues "
                    + "(GGPC_volume5.tex, lines 282–293)."),
            Definition("channel-volume", "channelVolume", "The weighted eigenvalue volume", VolumeFormula(),
                "Multiply the real value of the Lebesgue measure of s by the constant "
                    + "(√(d − 1)/d) to the power d + 1, as in GGPC_volume5.tex, lines 222–228. "
                    + "The natural d is cast to a real number before subtraction, division and the square root; "
                    + "the exponent d + 1 remains natural. ENNReal.toReal converts the extended nonnegative measure "
                    + "to a real number; for d at least two, all four regions below have finite positive measure."),
            Describe.Lean(
                DescribeId.Create("result"),
                DeclarationHandle.Create(Module + ".result"),
                H("The three ratios in every dimension at least two"),
                StatementSource.FromAuthor(Disp(ResultFormula())),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "The three identities are the conjectures in GGPC_volume5.tex, lines 243–246, "
                            + "276–279 and 302–305. They concern the four specified subsets of real coordinate space "
                            + "for every natural d at least two. They do not require the existence of d + 1 "
                            + "mutually unbiased bases in each such dimension.")),
                    Paragraph(Text(
                        "Fix d at least two, put m = d + 1, and let S be the standard simplex of nonnegative "
                            + "m-coordinate vectors whose coordinate sum is at most one. Its Lebesgue measure is 1/m!. "
                            + "Write u for the vector of ones. For a positive real c, consider the affine image "
                            + "T_c(S), where T_c(t) = u + c(t − (∑ⱼ tⱼ)u). "
                            + "The linear part has matrix c(I − J), with J the matrix of ones. "
                            + "Factor J as the product of an m-by-one column of ones and a one-by-m row of ones. "
                            + "The identity det(I − AB) = det(I − BA) reduces det(I − J) to the one-by-one "
                            + "determinant 1 − m = −d. Thus the absolute determinant of the linear part is d cᵐ. "
                            + "Translation invariance and the determinant formula for the image of Lebesgue measure "
                            + "give measure d cᵐ/m! for T_c(S).")),
                    Paragraph(Text(
                        "The coordinate sum of T_c(t) is m − cd∑ⱼ tⱼ. Consequently T_c(S) consists exactly "
                            + "of the vectors x with m − cd ≤ s and s ≤ 1 + d xⱼ for every j, where s = ∑ᵢ xᵢ. "
                            + "For the converse, set tᵢ = (d xᵢ − s + 1)/(cd). The upper inequalities make each tᵢ "
                            + "nonnegative, and ∑ᵢ tᵢ = (m − s)/(cd) is at most one by the lower inequality. "
                            + "Substituting these coordinates gives T_c(t) = x. "
                            + "Now put L = d/(d − 1). Since m − Ld = −1/(d − 1), the complete positivity region "
                            + "is T_L(S), and its measure is d Lᵐ/m!.")),
                    Paragraph(Text(
                        "The nonnegative complete positivity region is S ∪ T_1(S). Indeed, a vector in that "
                            + "region with coordinate sum at most one lies in S; if its sum is greater than one, "
                            + "the preceding characterization puts it in T_1(S). Conversely, nonnegativity and a sum "
                            + "at most one imply the complete positivity inequalities for every vector in S. "
                            + "For a vector in T_1(S), the sum is at least one, and its upper inequalities then "
                            + "force every coordinate to be nonnegative. The two simplices intersect only where "
                            + "the coordinate sum equals one. This hyperplane has zero Lebesgue measure. "
                            + "The set S is measurable as the intersection of its coordinate halfspaces and its sum "
                            + "halfspace, so the union has measure 1/m! + d/m! = (d + 1)/m!.")),
                    Paragraph(Text(
                        "The entanglement-breaking region is exactly S: membership gives nonnegative coordinates "
                            + "and a sum at most one, while these two conditions already imply complete positivity. "
                            + "Its measure is therefore 1/m!. The box is the closed coordinate interval with "
                            + "constant endpoints −1/(d − 1) and one. Each side has length L, and the product "
                            + "formula for the measure of a box gives its measure Lᵐ.")),
                    Paragraph(Text(
                        "All four measures are finite and positive because d, d − 1, L and m! are positive. "
                            + "The common weight (√(d − 1)/d)ᵐ is also positive, so it cancels from every quotient. "
                            + "The first quotient is (d Lᵐ/m!)/Lᵐ = d/m!. "
                            + "The second is ((d + 1)/m!)/(d Lᵐ/m!) = (d + 1)/(d Lᵐ); "
                            + "expanding m = d + 1 and L = d/(d − 1) gives "
                            + "((d² − 1)/d²)((d − 1)/d)ᵈ. "
                            + "The last quotient is (1/m!)/((d + 1)/m!) = 1/(d + 1)."))),
                DescribeRole.Theorem))));

    private static DocumentBlock Definition(string id, string declaration, string title, Formula formula, string prose) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Module + "." + declaration), H(title),
            StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula BoxFormula() => All("d", Naturals(),
        Equal(Typed(LocalCall("boxRegion", X("d")), RegionType()),
            SetOf("x", Coordinates(), All("i", Indices(),
                And(LE(Div(new Formula.Negate(D(1)), Subtract(RealD(), D(1))), At(X("x"), X("i"))),
                    LE(At(X("x"), X("i")), D(1)))))));

    private static Formula CpFormula() => All("d", Naturals(),
        Equal(Typed(LocalCall("cpRegion", X("d")), RegionType()),
            SetOf("x", Coordinates(),
                And(LE(Div(new Formula.Negate(D(1)), Subtract(RealD(), D(1))), CoordinateSum()),
                    All("j", Indices(), LE(CoordinateSum(),
                        Add(D(1), Multiply(RealD(), At(X("x"), X("j"))))))))));

    private static Formula GeneratorFormula() => All("d", Naturals(),
        Equal(Typed(LocalCall("generatorRegion", X("d")), RegionType()),
            Intersection(LocalCall("cpRegion", X("d")),
                SetOf("x", Coordinates(), All("i", Indices(), LE(D(0), At(X("x"), X("i"))))))));

    private static Formula EbFormula() => All("d", Naturals(),
        Equal(Typed(LocalCall("ebRegion", X("d")), RegionType()),
            Intersection(LocalCall("generatorRegion", X("d")),
                SetOf("x", Coordinates(), LE(CoordinateSum(), D(1))))));

    private static Formula VolumeFormula() => All("d", Naturals(), All("s", RegionType(),
        Equal(Typed(LocalCall("channelVolume", X("d"), X("s")), Reals()),
            Multiply(Pow(Div(At(Qualified("Real", "sqrt"), Subtract(RealD(), D(1))), RealD()),
                    Add(X("d"), D(1))),
                At(Qualified("ENNReal", "toReal"), At(Qualified("MeasureTheory", "volume"), X("s")))))));

    private static Formula ResultFormula() => All("d", Naturals(),
        Arrow(LE(Typed(D(2), Naturals()), X("d")),
            And(Equal(VolumeRatio("cpRegion", "boxRegion"), Div(RealD(), RealFactorial())),
                And(Equal(VolumeRatio("generatorRegion", "cpRegion"),
                        Multiply(Div(Subtract(Pow(RealD(), D(2)), D(1)), Pow(RealD(), D(2))),
                            Pow(Div(Subtract(RealD(), D(1)), RealD()), X("d")))),
                    Equal(VolumeRatio("ebRegion", "generatorRegion"), Div(D(1), Add(RealD(), D(1))))))));

    private static Formula VolumeRatio(string numerator, string denominator) =>
        Div(LocalCall("channelVolume", X("d"), LocalCall(numerator, X("d"))),
            LocalCall("channelVolume", X("d"), LocalCall(denominator, X("d"))));
    private static Formula CoordinateSum() => SumOver("i", Indices(), At(X("x"), X("i")));
    private static Formula RealD() => CastReal(X("d"));
    private static Formula RealFactorial() => CastReal(At(Qualified("Nat", "factorial"), Add(X("d"), D(1))));
    private static Formula CastReal(Formula value) => Typed(At(Qualified("Nat", "cast"), value), Reals());
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Indices() => At(Qualified("Fin"), Add(X("d"), D(1)));
    private static Formula Coordinates() => Arrow(Indices(), Reals());
    private static Formula RegionType() => At(Qualified("Set"), Coordinates());
    private static Formula LocalCall(string name, params Formula[] arguments) =>
        At(Qualified("D5", "S3", "QuantumChannels", "GeneralizedPauliVolumeRatios", name), arguments);
    private static Formula X(string name) => F.Id(name);
    private static Formula Qualified(params string[] parts)
    {
        var items = new System.Collections.Generic.List<Formula>();
        foreach (var part in parts)
        {
            if (items.Count > 0) items.Add(Dot);
            items.Add(F.Id(part));
        }
        return Seq(Operatorname, Grp(Seq([.. items])));
    }
    private static Formula At(Formula function, params Formula[] arguments) => new Formula.Apply(function, [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Left, Open, value, Right, Close);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(X(name), type), Comma, Sp, Parenthesized(body));
    private static Formula SetOf(string name, Formula type, Formula body) =>
        Seq(OpenBrace, X(name), Colon, Sp, type, Sp, Mid, Sp, Parenthesized(body), CloseBrace);
    private static Formula SumOver(string name, Formula type, Formula body) =>
        Seq(new Formula.Subscript(Sum, Seq(X(name), Colon, Sp, type)), Sp, Parenthesized(body));
    private static Formula LE(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(Parenthesized(domain), Parenthesized(codomain));
    private static Formula Intersection(Formula left, Formula right) =>
        At(Qualified("Set", "inter"), left, right);
    private static Formula Div(Formula numerator, Formula denominator) => new Formula.Fraction(numerator, denominator);
    private static Formula Pow(Formula value, Formula exponent) => new Formula.Power(Parenthesized(value), exponent);
}
