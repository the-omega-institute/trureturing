using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Diagonal;

internal sealed class SechPathDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every finite step on a discrete hyperbolic-secant path stays strictly above zero.",
        H("Discrete Hyperbolic-Secant Path"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("discrete-sech-path-positive"),
                DeclarationHandle.Create("D5/S0/Diagonal/SechPath.discrete_sech_path_positive"),
                H("The discrete sech path is positive"),
                StatementSource.FromAuthor(F.Disp(TheoremFormula())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The real hyperbolic cosine is strictly positive at every real argument. "
                        + "Taking its reciprocal therefore keeps every finite discrete step "
                        + "strictly above zero, independently of the starting rapidity and step size."))),
                DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula k = F.Id("k");
        Formula naturals = F.Seq(F.Mathbb, F.Grp(F.Id("N")));
        Formula real = F.Seq(F.Mathbb, F.Grp(F.Id("R")));
        Formula argument = F.Seq(
            F.Id("eta0"), F.Sp, F.Plus, F.Sp,
            F.Open, k, F.Sp, F.Colon, F.Sp, real, F.Close,
            F.Sp, F.Cdot, F.Sp, F.Id("delta"));
        Formula cosh = F.Seq(
            F.Operatorname, F.Grp(F.Id("cosh")), F.Open, argument, F.Close);
        Formula reciprocal = F.Seq(F.Frac, F.Grp(F.D(1)), F.Grp(cosh));
        return F.Seq(
            F.Forall, F.Sp, k, F.Sp, F.Colon, F.Sp, naturals,
            F.Comma, F.Sp, F.D(0), F.Sp, F.Lt, F.Sp, reciprocal);
    }
}
