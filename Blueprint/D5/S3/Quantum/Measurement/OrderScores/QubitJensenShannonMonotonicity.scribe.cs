using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Measurement.OrderScores;

internal sealed class QubitJensenShannonMonotonicityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Measurement/OrderScores/QubitJensenShannonMonotonicity.";
    private static readonly LibraryNoteRef Wu = LibraryNoteRef.Create("D5/L/Divergence/wu2026measurementorder");
    private static readonly Formula Half = new Formula.Fraction(D(1), D(2));
    private static readonly Formula Reals = Seq(Mathbb, Grp(F.Id("R")));
    private static readonly Formula Domain = Seq(OpenBracket, D(0), Comma, Sp, Half, CloseBracket);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Strict increase of Wu’s optimized qubit Lüders order score.",
        H("Monotonicity of the qubit Jensen–Shannon order score"),
        Blocks(
            Theorem("quantitative_increase", "Quantitative increase",
                "Starting from a lower-angle maximizer, one state at the larger angle weakly increases all even series coefficients. The quadratic coefficient gives the displayed gain in bits.",
                All("t", All("u", new Formula.Logic(
                    Both(new Formula.Relation(D(0), FormulaRelationOperator.LessThanOrEqual, F.Id("t")),
                        Both(new Formula.Relation(F.Id("t"), FormulaRelationOperator.LessThan, F.Id("u")),
                            new Formula.Relation(F.Id("u"), FormulaRelationOperator.LessThanOrEqual, Half))),
                    FormulaLogicOperator.Implies,
                    new Formula.Relation(new Formula.Fraction(
                        Sub(Sq("u"), Sq("t")), Seq(D(2), Sp, Op("ln"), Sp, D(2))),
                        FormulaRelationOperator.LessThanOrEqual, Sub(Score(F.Id("u")), Score(F.Id("t")))))))),
            Theorem("result", "Strict monotonicity on the closed interval",
                "The optimized score from Section II.C increases strictly on the full closed interval. The quantitative gain is positive for every strictly ordered pair, including the endpoints.",
                Apply(Op("StrictMonoOn"), F.Id("psi"), Domain)),
            Theorem("psi_half", "Orthogonal axes",
                "At the upper endpoint the maximizing circle interval collapses to one point. The optimal value is the binary entropy at 3/4 in bits minus 1/2.",
                new Formula.Relation(Score(Half), FormulaRelationOperator.Equal,
                    Sub(new Formula.Fraction(Apply(Op("binEntropy"), new Formula.Fraction(D(3), D(4))),
                        Seq(Op("ln"), Sp, D(2))), Half)))), []));

    private static DocumentBlock Theorem(string name, string title, string prose, Formula statement) =>
        Describe.Lean(DescribeId.Create(name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(Disp(statement)),
            AssessedProvenance.FromRepo(Wu), Blocks(Paragraph(DefinitionDsl.Text(prose))), DescribeRole.Theorem);

    private static Formula Op(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Apply(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula Score(Formula t) => Apply(Op("psi"), t);
    private static Formula Sq(string name) => Seq(F.Id(name), Caret, Grp(D(2)));
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Both(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula All(string v, Formula b) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(v), Reals, b);
}
