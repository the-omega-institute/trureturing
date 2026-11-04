using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.MetallicHankel;

internal sealed class MetallicHankelQuasipolynomialDefsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/MetallicHankel/MetallicHankelQuasipolynomialDefs.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/RecurrenceComposition/han2026shiftedmetallic");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Conjecture C asserts integer-valued rational quasipolynomials for every higher metallic Hankel shift.",
        H("The Complete Higher-Shift Quasipolynomial Claim"),
        Blocks(Describe.Lean(DescribeId.Create("metallic-hankel-quasipolynomial-defs-claim"),
            DeclarationHandle.Create(Prefix + "claim"), H("All parameters, residues and initial sizes"),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text("For each integer n>=1, there exists an integral formal power series Phi with constant coefficient one satisfying q Phi^2+((1+q^n)(1-q)-q[n]_q)Phi=1, with [n]_q the sum of q^i over 0<=i<n. For every such Phi and every shift ell>=n+3, put rho=2n(n+1) for even n and rho=4n(n+1) for odd n. There exists a family Q_r of rational polynomials, for all residues 0<=r<rho, such that Q_r(z) is an integer for every integer z and Delta_(r+m rho)^(ell)=Q_r(m) for every nonnegative integer m. The determinant is that of the matrix with entry [q^(ell+a+b)]Phi on indices 0<=a,b<r+m rho. Its empty value is one. The claim includes n=1, r=m=0, all initial sizes and vanishing determinants, with the displayed allowed period and no assertion of minimality or degree. No eventual qualification is imposed."))),
            DescribeRole.Definition)), []));
}
