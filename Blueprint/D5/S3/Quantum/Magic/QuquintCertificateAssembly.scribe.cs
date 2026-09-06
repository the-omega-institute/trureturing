using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Magic;

internal sealed class QuquintCertificateAssemblyDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "All thirty-two explicit numerical branch matrices are negative definite.",
        H("Ququint Numerical Certificate Assembly"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("ququint-all-branches-negative"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Magic/QuquintCertificateAssembly.all_branches_negative"),
                H("All numerical branches are negative definite"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("s"), Colon, Name("Fin"), Sp, D(3, 2), Comma,
                    Name("Matrix"), Dot, Name("PosDef"), Parenthesized(Seq(
                    Minus, Branch, Parenthesized(Seq( F.Id("s")))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("branch is the public numerical matrix family in "
                    + "D5.S3.Quantum.Magic.QuquintCertificateData. The proof consumes "
                    + "all thirty-two LDL identities, verifies all 128 pivots are positive, "
                    + "and proves the lower triangular factors invertible. "
                    + "Matrix.PosDef.diagonal and "
                    + "IsUnit.posDef_star_right_conjugate_iff yield the result."))),
                DescribeRole.Theorem),
            Paragraph(Text("QuquintCertificateBridge identifies the numerical matrices with "
                + "the phase-point quadratic forms through "
                + "QuquintWignerCriticalGeometry.tangentEquiv. QuquintFiniteMaximum "
                + "consumes this certificate to prove strict second-variation negativity. "
                + "QuquintStrictDecrease.exact_change and directional_decrease prove the normalized "
                + "perturbation identity and strict mana decrease along each nonzero constrained tangent direction. "
                + "This does not classify other directions or critical points, cover other dimensions, "
                + "solve general mana extremisation, identify Claim C as an author-verbatim conjecture, "
                + "or assert global novelty beyond the recorded search.")))));

    private static Formula Branch => Seq(Name("D5"), Dot, Name("S3"), Dot,
        Name("Quantum"), Dot, Name("Magic"), Dot, Name("QuquintCertificateData"),
        Dot, Name("branch"));
    private static Formula Name(string name) => Seq(Mathrm, Grp(F.Id(name)));
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
}
