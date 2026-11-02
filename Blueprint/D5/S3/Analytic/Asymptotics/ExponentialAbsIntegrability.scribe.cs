using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Asymptotics;

internal sealed class ExponentialAbsIntegrabilityDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Asymptotics/braams2026barnesmittagport");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The two-sided real exponential is integrable at every positive rate.", H("Integrability of two-sided exponential decay"), Blocks(
            Describe.Lean(DescribeId.Create("exponentialabsintegrability-integrable-exp-neg-mul-abs"),
                DeclarationHandle.Create("D5/S3/Analytic/Asymptotics/ExponentialAbsIntegrability.integrable_exp_neg_mul_abs"),
                H("Exponential decay on the real line"), StatementSource.FromAuthor(Disp(All("a", R, Imp(Lt(Num(0), V("a")), Call("Integrable", Map("x", R, Call("exp", Negate(Mul(V("a"), Abs(V("x"))))))))))),
                AssessedProvenance.FromLiterature(Source), Blocks(Paragraph(Text("For every positive real a the real function x maps to exp(-a*abs(x)) is integrable with respect to Lebesgue measure. Splitting the line at zero reduces this to the two exponential half-line integrals."))),
                DescribeRole.Theorem))));

    private static Formula R => F.Id("Real");
    private static Formula V(string name) => F.Id(name);
    private static Formula Num(byte digit) => D(digit);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(F.Id(name), [.. args]);
    private static Formula Map(string name, Formula type, Formula value) =>
        Seq(Open, F.Id(name), Colon, type, Sp, Mapsto, Sp, value, Close);
    private static Formula Mul(Formula a, Formula b) => Seq(Open, a, Star, b, Close);
    private static Formula Negate(Formula a) => Seq(Minus, Open, a, Close);
    private static Formula Abs(Formula a) => new Formula.Absolute(a);
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
}
