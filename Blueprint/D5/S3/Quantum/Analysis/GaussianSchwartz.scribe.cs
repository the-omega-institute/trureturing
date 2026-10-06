using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Analysis;

internal sealed class GaussianSchwartzDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The standard Gaussian has rapid decay at every derivative order.",
        H("Gaussian Schwartz Maps"),
        Blocks(Describe.Lean(
            DescribeId.Create("gaussian-schwartz-existence"),
            DeclarationHandle.Create("D5/S3/Quantum/Analysis/GaussianSchwartz.exists_gaussian_schwartz"),
            H("A Gaussian Schwartz map on every real inner product space"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Analytic/loges2026gaussianschwartz")),
            Blocks(
                Paragraph(Text("Let E be a real normed inner product space. There is a real "
                    + "Schwartz map f on E whose value at each x is exp(-norm(x) squared / 2). "
                    + "Completeness and finite dimensionality are not required.")),
                Paragraph(Text("The derivatives of the squared norm are bounded by powers of "
                    + "2 plus the squared norm. The chain rule bounds each Gaussian derivative "
                    + "by a polynomial times the same Gaussian. Exponential decay bounds the "
                    + "tail, and a maximum on a compact interval bounds the remaining values."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula e = F.Id("E"), f = F.Id("f"), x = F.Id("x");
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula space = Call("Schwartz", e, real);
        Formula value = Seq(Exp, Open, Minus, Frac,
            Grp(Seq(Seq(Vert, Sp, x, Vert), Caret, Grp(D(2)))),
            Grp(D(2)), Close);
        Formula pointwise = new Formula.BindMany(FormulaQuantifier.ForAll,
            [new(FormulaIdentifier.Create("x"), e)], Equal(new Formula.Apply(f, [x]), value));
        Formula existence = new Formula.BindMany(FormulaQuantifier.Exists,
            [new(FormulaIdentifier.Create("f"), space)], pointwise);
        return new Formula.BindMany(FormulaQuantifier.ForAll,
            [new(FormulaIdentifier.Create("E"), F.Id("RealInnerProductSpace"))], existence);
    }
}
