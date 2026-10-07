using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Nonnesting;

internal sealed class NonnestingOneThreeTwoTwoDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Nonnesting/NonnestingOneThreeTwoTwo.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/elizalde2024pattern");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Nonnesting permutations avoiding 1322 have the asserted binomial enumeration.",
        H("Enumeration of Nonnesting Permutations Avoiding 1322"),
        Blocks(
            Node("nonnesting-nonnestingonethreetwotwo-result", "The 1322 enumeration", "result",
                "For every positive n, n times the number of nonnesting permutations of the multiset with two copies of each letter from one through n avoiding 1322 equals the sum, over k from zero through n minus one, of the product of the binomial coefficients choosing k from 3n and choosing n minus one from 2n minus k minus two.", DescribeRole.Theorem,
                new OpenProblemResolutionClaim(ProblemSlugRef.Create("elizalde-luo-nonnesting-1322"), ResolutionKind.Proved)),
            Describe.Lean(
                DescribeId.Create("nonnesting-nonnestingonethreetwotwo-lagrange-coefficient"),
                DeclarationHandle.Create(Prefix + "lagrange_coefficient"),
                H("The reusable Lagrange coefficient supplier"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/PermutationPatterns/gessel2016lagrange")),
                Blocks(Paragraph(Text("Let r and Φ be rational formal power series, with constantCoeff r = 0 and r = X times PowerSeries.subst r Φ. For natural n and k with 1 ≤ k ≤ n, the rational cast of n times coeff n (r^k) equals the rational cast of k times coeff (n − k) (Φ^n). This is the power specialization of Gessel’s Theorem 2.1.1, equation (2.1.1). The existing proof remains owned here; the original result and the Catalan bridge consume this one public theorem. Zero constant coefficient supplies HasSubst r; the proof handles n = k separately and cancels the rational cast of n − k only in the positive-difference case. This generic coefficient theorem carries no P13 enumeration or resolution claim."))),
                DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(Disp(F.Id("claim1322"))), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
