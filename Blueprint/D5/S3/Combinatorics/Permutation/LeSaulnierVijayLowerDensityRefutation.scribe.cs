using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Permutation;

internal sealed class LeSaulnierVijayLowerDensityRefutationDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Combinatorics/Permutation/LeSaulnierVijayLowerDensityRefutation.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A staged set of positive integers admits a progression-free permutation and has "
            + "lower density at least four fifteenths, exceeding one quarter.",
        H("Refutation of the LeSaulnier-Vijay lower-density conjecture"),
        Blocks(
            Definition("three-free", "Progression-free enumeration", "ThreeFree",
                "For a subset T of the natural numbers, ThreeFree(T) means there exists a map "
                + "pi from the natural numbers to the natural numbers which is injective, has "
                + "range exactly T, and satisfies pi(i)+pi(k) unequal to 2*pi(j) for every "
                + "triple of natural indices i<j<k. The equation covers progressions in both "
                + "numerical directions. The map is an enumeration of the entire infinite set; "
                + "finite sets do not satisfy this definition."),
            Definition("lower-density", "Lower asymptotic density", "lowerDensity",
                "For a subset T of the natural numbers, lowerDensity(T) is the real-valued "
                + "Filter.liminf, along Filter.atTop on natural n, of the cardinality of "
                + "T intersected with the inclusive interval [1,n], cast to the reals and "
                + "divided by n. This is the source's lower density for positive integers. "
                + "The single term n=0 does not affect the limit inferior."),
            Definition("quarter-density-claim", "The conjectured quarter-density bound", "claim",
                "The claim states: for every subset T of the natural numbers, if zero is not "
                + "in T and ThreeFree(T) holds, then lowerDensity(T) is at most one quarter. "
                + "This is the upper-bound content of the conjecture beta(3)=1/4, together "
                + "with the paper's established lower bound beta(3)>=1/4."),
            Describe.Lean(
                DescribeId.Create("quarter-density-refutation"),
                DeclarationHandle.Create(Prefix + "result"),
                H("The quarter-density conjecture is false"),
                StatementSource.FromAuthor(Disp(Seq(Neg, Sp, F.Id("claim")))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Let M(k)=(11^k+1)/2. The counterexample is the singleton {1} together "
                    + "with, for each natural k, both inclusive intervals [2*M(k),3*M(k)-1] "
                    + "and [6*M(k)-2,11*M(k)-5]. Every arithmetic progression in this set "
                    + "lies in one stage. Within a stage, the binary-reversal rank places "
                    + "the middle term of every three-term progression before both endpoints "
                    + "or after both. Disjoint increasing rank ranges order the stages; "
                    + "enumerating the infinite rank image gives the literal injective "
                    + "permutation required by ThreeFree. The counting bound "
                    + "15*card(S intersect [1,n])>=4*n for every n>=1 gives lowerDensity(S) "
                    + ">=4/15. Since 4/15>1/4 and zero is absent, the conjectured universal "
                    + "bound contradicts this explicit example."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("lesaulnier-vijay-2011-beta3-lower-density"),
                    ResolutionKind.Refuted)))));

    private static DocumentBlock Definition(string id, string title, string declaration,
        string prose) => Describe.Lean(
            DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration),
            H(title),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))),
            DescribeRole.Definition);
}
