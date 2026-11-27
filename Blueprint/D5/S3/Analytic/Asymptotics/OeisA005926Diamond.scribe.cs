using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Asymptotics;

internal sealed class OeisA005926DiamondDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Analytic/Asymptotics/OeisA005926Diamond.";
    private static readonly LibraryNoteRef GeneratingFunctionSource =
        LibraryNoteRef.Create("D5/L/Asymptotics/morris2026a005926");
    private static readonly LibraryNoteRef ConjectureSource =
        LibraryNoteRef.Create("D5/L/Asymptotics/kotesovec2026a005926");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The summatory function of the diamond theta coefficients has leading constant π/48.",
        H("Vaclav Kotesovec’s summatory conjecture for OEIS A005926"),
        Blocks(
            Node("thetaSeries", "The diamond theta series",
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(GeneratingFunctionSource),
                "For T(j) = j(j+1)/2, ψ(X) is the formal series with a unit monomial in each degree T(j). Over the integers, the source series is X³(ψ(X⁸)³ + ψ(−X⁸)³). Its coefficient of degree k is a(k). The substitutions use PowerSeries.expand and PowerSeries.rescale.",
                DescribeRole.Definition),
            Node("theta_coefficient_lattice", "The exact coefficient as a lattice shell",
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(ConjectureSource),
                "For each degree k, a(k) is twice the number of ordered integer triples z with ∑ᵢ(4zᵢ+1)² = k and ∑ᵢ zᵢ even. Cauchy products allow each ψ factor to be truncated at triangular indices j ≤ k for this coefficient. The two cubes give weight 1 + (−1)^(T(j₁)+T(j₂)+T(j₃)), which is two for even triangular sum and zero for odd triangular sum. The bijection from integer z to natural j uses j = 2z for z ≥ 0 and j = −2z−1 for z < 0. It gives T(j) = 2z²+z and preserves the required parity.",
                DescribeRole.Theorem),
            Node("theta_inclusive_cutoff", "The exact sum through N",
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(ConjectureSource),
                "The shift by three gives a(k)=0 for k<3. Summing the shells for 1 ≤ k ≤ N gives twice the number of ordered integer triples with even coordinate sum and ∑ᵢ(4zᵢ+1)² ≤ N. At N=0 the interval and the lattice region both give zero.",
                DescribeRole.Theorem),
            Node("result", "The normalized sums tend to π/48",
                StatementSource.FromAuthor(Limit()), AssessedProvenance.FromRepo(ConjectureSource),
                "Vaclav Kotesovec stated the conjecture in OEIS A005926 revision 49 on November 26, 2026. The parity condition partitions the triples into the four residue classes 000, 011, 101, and 110 modulo two. In the squared-norm coordinates these give four translates of the lattice of spacing eight. Each class is counted by a shifted closed ball of radius √N/8, so division by N^(3/2) contributes (4π/3)/8³ per class. The four classes and weight two give π/48 for natural N tending to infinity through all cutoffs.",
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a005926-diamond-summatory-asymptotic"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Node(string declaration, string title, StatementSource statement,
        AssessedProvenance provenance, string prose, DescribeRole role,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create("a005926-" + declaration.ToLowerInvariant().Replace('_', '-')),
            DeclarationHandle.Create(Prefix + declaration), H(title), statement, provenance,
            Blocks(Paragraph(Text(prose))), role, openProblemResolutionClaim: resolution);

    private static Formula Limit()
    {
        Formula n = F.Id("N"), k = F.Id("k");
        Formula sum = Seq(Sum, Underscore, Grp(k, Eq, D(1)), Caret, Grp(n), Sp,
            new Formula.Apply(F.Id("a"), [k]));
        Formula scale = new Formula.Power(n, new Formula.Fraction(D(3), D(2)));
        return Disp(Seq(Lim, Underscore, Grp(n, Sp, To, Sp, Infty), Sp,
            new Formula.Fraction(sum, scale), Sp, Eq, Sp, new Formula.Fraction(Pi, D(4, 8))));
    }
}
