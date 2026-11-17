using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Patterns.Separable;

internal sealed class RecordAllIndexDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual separable right-maximum series satisfies the source weighted quadratic and the complete CKZ peak-three law.",
        H("Actual-Carrier CKZ Conjecture 2 for Separable Records"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("actual-weighted-quadratic"),
                DeclarationHandle.Create(
                    "D5/S1/Words/Patterns/Separable/RecordAllIndex.actual_weighted_quadratic"),
                H("The actual quadratic with singleton and proper-cut terms"),
                StatementSource.FromAuthor(Disp(Seq(
                    F.Id("J"), Sp, Eq, Sp,
                    F.Id("z"), Sp, Plus, Sp,
                    F.Id("z"), Sp, Cdot, Sp, Open, D(1), Sp, Plus, Sp,
                    Call("C", F.Id("q")), Close, Sp, Cdot, Sp, F.Id("J"),
                    Sp, Plus, Sp,
                    Call("C", F.Id("q")), Sp, Cdot, Sp, Open, D(1), Sp, Plus, Sp,
                    Call("C", F.Id("q")), Close, Sp, Cdot, Sp,
                    new Formula.Power(F.Id("J"), D(2))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "J is the positive bivariate series whose outer coefficient marks the "
                        + "strict right-maximum count and whose inner coefficient marks length. "
                        + "q is the positive-length counting series of the literal permutations "
                        + "of Fin n avoiding 2413 and 3142. z is the singleton term, and C is "
                        + "the constant-series embedding into the outer PowerSeries.")),
                    Paragraph(Text(
                        "The proof uses the minimum-cut enumeration on the actual carrier. "
                        + "It restricts the block record laws to exact record fibers, combines the "
                        + "opposite-sign transport with the actual Schröder cardinalities, and "
                        + "derives I0(1+q)=q from the scalar Schröder equation. The proper-cut "
                        + "series then satisfies R=C(q)J and the all-avoider series satisfies "
                        + "U=(1+C(q))J, yielding the displayed quadratic.")),
                    Paragraph(Text(
                        "The result is the source-faithful actual-carrier bridge needed before "
                        + "coefficient extraction. The same module proves the exact binomial "
                        + "coefficient normalization, identifies the Section 8 Newton kernels "
                        + "on the actual carrier, and extracts every length coefficient. "
                        + "Coefficientwise nonnegativity of the kernels gives the "
                        + "arbitrary-index decline from record three. Exact reversal and "
                        + "complement transports then give all four literal distributions, "
                        + "including the zero tail and the singleton convention."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actual-ckz-conjecture-two"),
                DeclarationHandle.Create(
                    "D5/S1/Words/Patterns/Separable/RecordAllIndex.actual_ckz_conjecture_two"),
                H("The complete source-faithful peak-three conclusion"),
                StatementSource.FromAuthor(Disp(CKZFormula())),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For n at least five, the carrier is the literal set of permutations "
                        + "of Fin n avoiding 2413 and 3142. The four counts are the actual "
                        + "positive irreducible and proper-cut fibers for strict right maxima, "
                        + "strict left minima, strict left maxima and strict right minima. "
                        + "The index is unshifted: k records means exactly k record positions.")),
                    Paragraph(Text(
                        "The first conjunct is the weak rise for k below three. The second is "
                        + "the weak decline for every k at least three. The final conjunct states "
                        + "the resulting global maximum at record count three for each of the "
                        + "four distributions and every natural index, including indices beyond "
                        + "the length through the explicit zero-tail branch.")),
                    Paragraph(Text(
                        "The proof starts from the actual direct-cut weighted quadratic. Its "
                        + "coefficient extraction is over the rationals, so signed differences "
                        + "retain equality rather than using natural-cardinality subtraction. "
                        + "The scalar Schröder equation supplies q=t+tq+q^2 and hence the exact "
                        + "time relation. The RecordNewtonPositivity theorem applies to "
                        + "the definitionally identical actual M and t series. The resulting "
                        + "finite binomial sums have nonnegative coefficients. RecordTransport "
                        + "supplies the other three statistics, with its singleton correction "
                        + "zero in the n at least five range.")),
                    Paragraph(Text(
                        "The statement is the weak peak formulation of Chen, Kitaev and Zhang, "
                        + "arXiv:2404.18517v1, Section 3, Conjecture 2; the journal reference is "
                        + "DOI 10.1016/j.dam.2024.05.004. It asserts neither uniqueness nor a "
                        + "finite length cutoff. The journal version of record body and "
                        + "exhaustive literature novelty remain unverified; the theorem "
                        + "establishes the stated mathematical inequalities."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("chenkitaevzhang-2024-separable-record-peak-three"),
                    ResolutionKind.Proved)))));

    private static Formula CKZFormula()
    {
        var n = F.Id("n");
        var k = F.Id("k");
        Formula Count(string name, string stat, Formula index) =>
            new Formula.FunctionCall(FormulaIdentifier.Create(name),
                [n, F.Id(stat), index]);
        Formula R(string stat, Formula index) => Count("irreducibleCount", stat, index);
        Formula CountD(string stat, Formula index) => Count("reducibleCount", stat, index);
        Formula rise = And(
            Le(R("rmax", k), R("rmax", Add(k, D(1)))),
            Le(R("lmin", k), R("lmin", Add(k, D(1)))),
            Le(CountD("lmax", k), CountD("lmax", Add(k, D(1)))),
            Le(CountD("rmin", k), CountD("rmin", Add(k, D(1)))));
        Formula decline = And(
            Le(R("rmax", Add(k, D(1))), R("rmax", k)),
            Le(R("lmin", Add(k, D(1))), R("lmin", k)),
            Le(CountD("lmax", Add(k, D(1))), CountD("lmax", k)),
            Le(CountD("rmin", Add(k, D(1))), CountD("rmin", k)));
        Formula peak = And(
            Le(R("rmax", k), R("rmax", D(3))),
            Le(R("lmin", k), R("lmin", D(3))),
            Le(CountD("lmax", k), CountD("lmax", D(3))),
            Le(CountD("rmin", k), CountD("rmin", D(3))));
        return All("n", Nat(), Imp(Le(D(5), n), And(
            All("k", Nat(), Imp(Lt(k, D(3)), rise)),
            All("k", Nat(), Imp(Le(D(3), k), decline)),
            All("k", Nat(), peak))));
    }

    private static Formula Nat() => new Formula.NamedConstant(FormulaIdentifier.Create("Nat"));
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Imp(Formula left, Formula right) =>
        new Formula.Logic(P(left), FormulaLogicOperator.Implies, P(right));
    private static Formula And(params Formula[] values)
    {
        Formula result = P(values[^1]);
        for (int i = values.Length - 2; i >= 0; i--)
            result = new Formula.Logic(P(values[i]), FormulaLogicOperator.And, result);
        return result;
    }
    private static Formula Le(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Lt(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula P(Formula value) => Seq(Open, value, Close);
}
