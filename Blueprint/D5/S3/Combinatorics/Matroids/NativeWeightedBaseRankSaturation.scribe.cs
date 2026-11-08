using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Matroids;

internal sealed class NativeWeightedBaseRankSaturationDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Combinatorics/Matroids/NativeWeightedBaseRankSaturation";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite native matroid minimum-weight bases are characterized by every real threshold rank.",
        H("Native weighted bases and threshold-rank saturation"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("native-weighted-base-weight"),
                DeclarationHandle.Create(Module + ".baseWeight"),
                H("The actual finite weight of a base"),
                StatementSource.FromAuthor(BaseWeightFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a finite carrier, baseWeight is the finite sum of the given real weight "
                        + "function over the actual base set. The ground is not silently replaced "
                        + "by the carrier."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("native-weighted-lower-weight-set"),
                DeclarationHandle.Create(Module + ".lowerWeightSet"),
                H("The native lower threshold set"),
                StatementSource.FromAuthor(LowerWeightSetFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The threshold set retains precisely elements of the native ground M.E whose "
                        + "real weight is at most t."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("native-weighted-base-rank-saturation"),
                DeclarationHandle.Create(Module + ".native_weighted_base_rank_saturation"),
                H("Attainment and the complete every-base threshold-rank iff"),
                StatementSource.FromAuthor(MainFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every finite carrier E in an arbitrary universe, every native matroid M on E, "
                            + "and every real weight function w, a minimum-weight base exists. For "
                            + "each base B, minimum total weight among all bases is equivalent to "
                            + "saturating the native rank of every real lower threshold: the finite "
                            + "cardinality of B intersect {e in M.E | w(e) <= t} equals the native "
                            + "eRk of that set cast with toNat.")),
                    Paragraph(Text(
                        "The proof uses direct finite attainment over the set of all bases. The forward "
                            + "direction is the native exchange argument: an unsaturated threshold admits "
                            + "a cheaper base exchange. The reverse direction compares sorted finite base "
                            + "weights from all threshold prefix inequalities, so ties, zero weights and "
                            + "signed weights remain in scope.")),
                    Paragraph(Text(
                        "The statement includes empty carriers and grounds, rank zero, loops, coloops, "
                            + "proper native grounds, nonrepresentable matroids and repeated real weights. "
                            + "It adds no nonempty-ground, positive-rank, positivity, distinctness, supplied "
                            + "optimum, rank-profile or finite-state premise, and it makes no algorithmic, "
                            + "complexity or oracle claim.")),
                    Paragraph(Text(
                        "Oki--Schwarcz, arXiv:2511.16021v3, Theorem 2.1 ("
                            + "https://arxiv.org/abs/2511.16021v3) gives a related rank-increment "
                            + "minimum-value formula. The present statement additionally characterizes "
                            + "every base by every real threshold and applies to native finite matroids "
                            + "with signed weights."))),
                DescribeRole.Theorem))));

    private static Formula MainFormula()
    {
        Formula e = F.Id("E"), m = F.Id("M"), w = F.Id("w");
        Formula b = F.Id("B"), c = F.Id("C"), t = F.Id("t");
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula typeU = new Formula.Subscript(F.Id("Type"), F.Id("u"));
        Formula setE = Call("Set", e);
        Formula matroidE = Call("Matroid", e);
        Formula isBase(Formula x) => QualifiedCall("Matroid", "IsBase", m, x);
        Formula total(Formula x) => Call("baseWeight", w, x);
        Formula lower(Formula x) => Call("lowerWeightSet", m, w, x);
        Formula inter(Formula left, Formula right) => QualifiedCall("Set", "inter", left, right);
        Formula ncard(Formula x) => QualifiedCall("Set", "ncard", x);
        Formula erank(Formula x) => QualifiedCall("Matroid", "eRk", m, x);
        Formula toNat(Formula x) => QualifiedCall("ENat", "toNat", x);
        Formula saturation = Equal(ncard(inter(b, lower(t))), toNat(erank(lower(t))));
        Formula minimum(Formula x) => All("C", setE,
            Imp(isBase(c), Leq(total(x), total(c))));
        Formula saturationAll = All("t", real, saturation);
        Formula minimumIffSaturation = Iff(minimum(b), saturationAll);
        Formula attainment = Some("B", setE, And(isBase(b), minimum(b)));
        Formula allBases = All("B", setE, Imp(isBase(b), minimumIffSaturation));
        Formula body = And(attainment, allBases);
        return Disp(All("E", typeU,
            Seq(Instance(Call("Finite", e)), Comma, Sp,
                All("M", matroidE,
                    All("w", new Formula.TypeArrow(e, real), body)))));
    }

    private static Formula BaseWeightFormula()
    {
        Formula w = F.Id("w"), b = F.Id("B"), e = F.Id("e");
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula typeU = new Formula.Subscript(F.Id("Type"), F.Id("u"));
        Formula setE = Call("Set", F.Id("E"));
        Formula sumIndex = Seq(e, Sp, InMacro, Sp,
            Call("toFinite", b), Dot, Operatorname, Grp(F.Id("toFinset")));
        Formula sum = new Formula.Subscript(Sum, Grp(sumIndex));
        return Disp(All("E", typeU,
            Seq(Instance(Call("Finite", F.Id("E"))), Comma, Sp,
                All("w", new Formula.TypeArrow(F.Id("E"), real),
                    All("B", setE,
                        Equal(Call("baseWeight", w, b),
                            Seq(sum, Sp, Call("w", e))))))));
    }

    private static Formula LowerWeightSetFormula()
    {
        Formula e = F.Id("E"), m = F.Id("M"), w = F.Id("w"), t = F.Id("t");
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula typeU = new Formula.Subscript(F.Id("Type"), F.Id("u"));
        Formula matroidE = Call("Matroid", e);
        Formula setE = Call("Set", e);
        Formula body = Seq(OpenBrace, F.Id("x"), Sp, Mid, Sp,
            F.Id("x"), Sp, InMacro, Sp, m, Dot, F.Id("E"), Sp, Land, Sp,
            Leq(Call("w", F.Id("x")), t), CloseBrace);
        return Disp(All("E", typeU,
            All("M", matroidE,
                All("w", new Formula.TypeArrow(e, real),
                    All("t", real,
                        Equal(Call("lowerWeightSet", m, w, t), body))))));
    }

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. arguments]);

    private static Formula QualifiedCall(string owner, string name, params Formula[] arguments) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(owner)), Dot, Operatorname, Grp(F.Id(name))),
            [.. arguments]);

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Parenthesized(Seq(F.Id(name), Colon, Sp, type)), Comma, Sp,
            Parenthesized(body));
    private static Formula Some(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, Parenthesized(Seq(F.Id(name), Colon, Sp, type)), Comma, Sp,
            Parenthesized(body));
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Imp(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Leq(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Instance(Formula typeclass) => Seq(OpenBracket, typeclass, CloseBracket);
}
