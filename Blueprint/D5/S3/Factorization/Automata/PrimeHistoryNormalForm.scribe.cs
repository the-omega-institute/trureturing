using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Factorization.Automata;

internal sealed class PrimeHistoryNormalFormDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Complete guarded prime histories have canonical interval-translation semantics.",
        H("Prime History Normal Forms"),
        Blocks(
            Paragraph(Text(
                "A true command multiplies by the fixed prime, and a false command divides "
                + "exactly. The existing BoundedPrimeWalk transports this execution to the "
                + "exponent interval 0 through a. The new word data are the least and greatest "
                + "prefix displacements, including the empty prefix, and the final displacement. "
                + "These are not independently selected edge witnesses.")),
            Describe.Lean(
                DescribeId.Create("prime-history-exact-run"),
                DeclarationHandle.Create(
                    "D5/S3/Factorization/Automata/PrimeHistoryNormalForm.run_spec"),
                H("Every intermediate guard is captured by the prefix extrema"),
                StatementSource.FromAuthor(Disp(Seq(
                    F.Id("run"), Open, F.Id("a"), Comma, F.Id("e"), Comma, F.Id("w"), Close,
                    Sp, Eq, Sp, F.Id("some"), Open, F.Id("f"), Close))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The displayed success equation holds exactly when e+low(w)>=0, "
                    + "e+high(w)<=a, and f=e+displacement(w). The proof is induction on the "
                    + "actual repository runner, splitting both step guards. The statement "
                    + "therefore includes intermediate failure, not only final feasibility."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("prime-history-normal-correct"),
                DeclarationHandle.Create(
                    "D5/S3/Factorization/Automata/PrimeHistoryNormalForm.normal_correct"),
                H("Canonical normal form preserves the exact partial execution"),
                StatementSource.FromAuthor(Disp(Seq(
                    F.Id("integerReadout"), Open, F.Id("run"), Open,
                    F.Id("a"), Comma, F.Id("e"), Comma, F.Id("w"), Close, Close,
                    Sp, Eq, Sp, F.Id("evaluate"), Open, F.Id("normal"), Open,
                    F.Id("a"), Comma, F.Id("w"), Close, Comma, F.Id("e"), Close))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A realizable nonempty form has source interval [-low(w),a-high(w)] "
                    + "and the final displacement as translation. When high(w)-low(w)>a, "
                    + "the form is the unique empty map. Every legal exponent and every "
                    + "failure outcome is preserved. Equality of these forms does not "
                    + "preserve the exact original word, its length, or intermediate readings."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("prime-history-constructive-realization"),
                DeclarationHandle.Create(
                    "D5/S3/Factorization/Automata/PrimeHistoryNormalForm.normal_surjective"),
                H("Every admissible interval translation is actually realizable"),
                StatementSource.FromAuthor(Disp(Seq(
                    F.Id("range"), Open, F.Id("normal"), Open, F.Id("a"), Close, Close,
                    Sp, Eq, Sp, F.Id("allIntervalMaps")))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a nonempty form [l,u] with shift d, run l divisions, a-u+l "
                    + "multiplications and a-u-d divisions. Its three extrema are derived "
                    + "from the actual concatenation signatures. The admissibility conditions "
                    + "prove that all lengths are nonnegative. Capacity+1 multiplications "
                    + "realize the empty map. Thus the carrier has neither unrealized forms "
                    + "nor multiple encodings of the empty behavior."))),
                DescribeRole.Theorem),
            Paragraph(Text(
                "The three-invariant word structure is classical: the monogenic free inverse "
                + "monoid uses precisely a visited interval and a terminal displacement. "
                + "See Silva, arXiv:2205.08854v2, Section 2.2, equation (1). The present "
                + "source establishes its concrete bounded-prime execution and realization, "
                + "not a new discovery of that abstract normal form or a full formalization "
                + "of the free inverse monoid universal property."))),
        [DocumentEdge.Dependency.Create(
            GidRef.Create("D5/S3/Factorization/Automata/BoundedPrimeWalk"))]));
}
