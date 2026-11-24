using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.AURICOmega;

internal sealed class ProjectiveOverlapScalingDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Scale invariance of the Chapter 39 projective overlap.",
        H("Projective overlap under positive scaling"),
        Blocks(Describe.Lean(
            DescribeId.Create("projective-overlap-positive-scaling"),
            DeclarationHandle.Create("D5/S3/Quantum/AURICOmega/ProjectiveOverlapScaling.kappa_scale"),
            H("Common positive scales preserve overlap"),
            StatementSource.FromAuthor(Statement()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("For the book's Chapter 39 overlap of the integer homogeneous coordinates [P:Q], take p and q to be the magnitudes of P and Q. The scale k+1 ranges over all positive natural numbers.")),
                Paragraph(Text("The overlap kappa(p,q) is the exact ratio with numerator q squared and denominator p squared plus q squared. Equivalent compares finite ratios by cross multiplication and relates the undefined value to itself. The pair (0,0) therefore remains in the theorem, with undefined readings before and after scaling.")),
                Paragraph(Text("This is the direct application of Omega.Projective.kappa_scale to p, q, and k."))),
            DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula Statement()
    {
        Formula p = F.Id("p"), q = F.Id("q"), k = F.Id("k");
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));
        Formula scale = new Formula.Binary(k, FormulaBinaryOperator.Add, D(1));
        Formula scaledP = new Formula.Binary(p, FormulaBinaryOperator.Multiply, scale);
        Formula scaledQ = new Formula.Binary(q, FormulaBinaryOperator.Multiply, scale);
        return Disp(new Formula.BindMany(FormulaQuantifier.ForAll,
            [new(FormulaIdentifier.Create("p"), naturals),
             new(FormulaIdentifier.Create("q"), naturals),
             new(FormulaIdentifier.Create("k"), naturals)],
            Call("Equivalent", Call("kappa", scaledP, scaledQ), Call("kappa", p, q))));
    }
}
