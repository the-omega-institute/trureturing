using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.Blueprint.D5.S3.Weil.Probability.CanonicalLiNonnegativeConverseFormula;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Probability;

internal sealed class CanonicalLiNonnegativeConverseDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Prove the A006 reverse implication at the original derivative-defined canonical Li coefficients.",
        H("CanonicalLiNonnegativeConverse"), Blocks(
            Describe.Lean(DescribeId.Create("canonical-li-nonnegative-implies-rh"),
                DeclarationHandle.Create("D5/S3/Weil/Probability/CanonicalLiNonnegativeConverse.canonical_li_nonnegative_implies_rh"),
                H("All positive-index canonical coefficients are nonnegative implies RH"),
                StatementSource.FromAuthor(Imp(All("n", Natural,
                    Imp(Le(Num(1), Id("n")), Le(Num(0), Call("canonicalLiCoefficient", Id("n"))))), RH)),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/flajolet2009analytic")),
                Blocks(
                    Paragraph(Text("The only premise is nonnegativity of canonicalLiCoefficient n for every natural n at least one. The conclusion is standard Mathlib RiemannHypothesis. The canonical derivative definition and the n+1 series shift are retained.")),
                    Paragraph(Text("The positive-boundary proof follows Theorem IV.6 and item IV.13. A genuine continuation at a finite positive radius gives convergence of the recentered series past the original boundary. Scalar uniqueness and nonnegative double summation imply original-series convergence there, contradicting the radius. The finite-subset identity is proved using map_add_univ; the inconsistent later exponents on printed p.242 are not copied.")),
                    Paragraph(Text("At real x in [0,1), the original xi argument (1-x) inverse is at least one and cannot be a strict-strip zero. Thus the actual generator is analytic there. Frozen analytic continuation uniqueness identifies the series along the real segment. The resulting convergence at every NNReal r<1, including zero, feeds the frozen canonical_li_disk_summability_implies_rh theorem.")),
                    Paragraph(Text("The Li specialization is repository assembly with the cited Pringsheim argument acknowledged. This is A006 reverse only. A007 reverse may later consume it; forward positivity, strictness and the fixed-lambda1 A013 bound remain unchanged."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("nonnegative-series-positive-boundary-obstruction"),
                DeclarationHandle.Create("D5/S3/Weil/Probability/CanonicalLiNonnegativeConverse.nonnegative_series_positive_boundary_obstruction"),
                H("A finite positive radius is singular for nonnegative coefficients"),
                StatementSource.FromAuthor(F.Disp(BoundaryStatement())),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/flajolet2009analytic")),
                Blocks(Paragraph(Text("For nonnegative real coefficients, an analytic complex function cannot agree with their power-series sum on a left interval at a finite positive radius. Theorem IV.6 and item IV.13, printed pages 240–242, give the Pringsheim argument. The displayed radius belongs to the scalar multilinear series with the real coefficients embedded in C. The real interval includes the condition x at least zero."))),
                DescribeRole.Theorem))));
    private static Formula BoundaryStatement()
    {
        Formula real = F.Seq(F.Mathbb, F.Grp(F.Id("R")));
        Formula complex = F.Seq(F.Mathbb, F.Grp(F.Id("C")));
        Formula nnreal = Id("NNReal");
        Formula a = Id("a"), n = Id("n"), r = Id("R"), g = Id("g"), x = Id("x"), e = Id("e");
        Formula cast(Formula value, Formula type) => Parenthesized(F.Seq(value, F.Colon, F.Sp, type));
        Formula app(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
        Formula q(string owner, string name) => F.Seq(F.Operatorname, F.Grp(F.Id(owner), F.Dot, F.Id(name)));
        Formula and(Formula u, Formula v) => new Formula.Logic(u, FormulaLogicOperator.And, v);
        Formula lt(Formula u, Formula v) => new Formula.Relation(u, FormulaRelationOperator.LessThan, v);
        Formula ex(string name, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
        Formula coefficients = F.Seq(Id("fun"), F.Sp, n, F.Colon, F.Sp, Natural, F.Sp, F.Mapsto, F.Sp, cast(app(a, n), complex));
        Formula series = app(q("FormalMultilinearSeries", "ofScalars"), complex, Parenthesized(coefficients));
        Formula radius = F.Seq(Parenthesized(series), F.Dot, Id("radius"));
        Formula sum = F.Seq(new Formula.Subscript(F.Seq(F.Sum, F.Apos), n), F.Sp,
            Multiply(cast(app(a, n), complex), new Formula.Power(cast(x, complex), n)));
        Formula agreement = ex("e", real, and(lt(Num(0), e), All("x", real,
            Imp(lt(Subtract(cast(r, real), e), x), Imp(lt(x, cast(r, real)), Imp(Le(Num(0), x),
                Equal(app(g, cast(x, complex)), sum)))))));
        return All("a", new Formula.TypeArrow(Natural, real), Imp(All("n", Natural, Le(Num(0), app(a, n))),
            All("R", nnreal, Imp(lt(Num(0), r), Imp(Equal(radius, cast(r, Id("ENNReal"))),
                All("g", new Formula.TypeArrow(complex, complex), Imp(Call("AnalyticAt", complex, g, cast(r, complex)),
                    Imp(agreement, Id("False")))))))));
    }
    private static Formula Parenthesized(Formula value) => F.Seq(F.Open, value, F.Close);

}

internal static class CanonicalLiNonnegativeConverseFormula
{
    internal static Formula Natural => F.Seq(F.Mathbb, F.Grp(F.Id("N")));
    internal static Formula RH => Id("RiemannHypothesis");
    internal static Formula All(string variable, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(variable), domain, body);
    internal static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    internal static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
}
