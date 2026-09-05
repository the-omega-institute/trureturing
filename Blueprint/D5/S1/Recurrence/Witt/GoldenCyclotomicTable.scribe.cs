using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Witt;

internal sealed class GoldenCyclotomicTableDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S1/Recurrence/Witt/GoldenCyclotomicTable."
            + "golden_cyclotomic_table_degree_five";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The golden admissible-word series has the stated signed cyclotomic factors through total degree five.",
        H("Golden Cyclotomic Table Through Degree Five"),
        Blocks(Describe.Lean(
            DescribeId.Create("golden-cyclotomic-table-through-degree-five"),
            DeclarationHandle.Create(Declaration),
            H("The cleared cyclotomic factors agree in every low bidegree"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The prefix coefficients are computed from the frozen admissible-word "
                        + "degree map. Bivariate convolution is the exact Cauchy product, so "
                        + "the equality checks the cleared formal factorization coefficient by "
                        + "coefficient rather than through numerical evaluation.")),
                Paragraph(Text(
                    "The positive factors occur at (1,0), (0,1), (2,1), (1,2), (4,1), "
                        + "(3,2), and (2,3). The negative factors occur at (2,0), (0,2), "
                        + "(3,1), and (2,2). Every omitted bidegree of total degree at most "
                        + "five has zero exponent.")),
                Paragraph(Text(
                    "In particular, this proves the previously unfrozen entries e22 = -1 "
                        + "and e41 = e32 = e23 = 1, while agreeing with the frozen pure and "
                        + "first-row laws on their overlap.")),
                Paragraph(Text(
                    "The source theorem also reports an all-stage zeta cascade and numerical "
                        + "staircase certificates. Those analytic and empirical clauses are not "
                        + "consequences of the current frozen API. The formal statement is "
                        + "therefore the exact finite cyclotomic core through total degree five "
                        + "and makes no unproved convergence or continuation claim.")),
                Paragraph(Text(
                    "The escape witness is the public coefficient identity itself: kernel "
                        + "reduction computes twenty-one new finite convolution equalities "
                        + "from the canonical word degrees. It cannot be obtained by projection "
                        + "or normalization of the frozen bivariate functional equation."))),
            DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(
            GidRef.Create("D5/S1/Recurrence/BivariateWordSeries"))]));

    private static Formula TheoremFormula()
    {
        Formula a = F.Id("a"), b = F.Id("b");
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));
        Formula left = Call(
            "convolution", F.Id("goldenPrefix"), F.Id("positiveWittFactors"), a, b);
        Formula right = Call("negativeWittFactors", a, b);

        return Disp(Seq(
            Forall, Sp, a, Comma, Sp, b, Sp, InMacro, Sp, naturals, Comma, Esc,
            a, Sp, Plus, Sp, b, Sp, Leq, Sp, D(5), Sp, Rightarrow, Sp,
            left, Sp, Eq, Sp, right, Dot));
    }

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. arguments]);
}
