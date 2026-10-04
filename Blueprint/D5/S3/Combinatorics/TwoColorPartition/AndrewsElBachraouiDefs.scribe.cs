using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.TwoColorPartition;

internal sealed class AndrewsElBachraouiDefsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/TwoColorPartition/AndrewsElBachraouiDefs.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/andrews2025positive");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite truncations define the two-color partition series and their three sign statements.",
        H("Andrews and El Bachraoui Two-Color Partition Series"),
        Blocks(
            Node("andrews-el-bachraoui-defs-geom", "Geometric coefficient series", "geom", "For a natural number d, geom d is the integer power series whose coefficient at t is one when d divides t and zero otherwise.", DescribeRole.Definition),
            Node("andrews-el-bachraoui-defs-ctrunc", "Finite C-prime truncation", "cTrunc", "For natural numbers k, m and N, cTrunc k m N is the finite sum over j from zero through N of q raised to m times (2j+1), multiplied by the finite products with factors 1 minus q raised to the two prescribed even exponents and two geometric denominators.", DescribeRole.Definition),
            Node("andrews-el-bachraoui-defs-dtrunc", "Finite D-prime truncation", "dTrunc", "For natural numbers k, m and N, dTrunc k m N is the finite sum over j from zero through N of q raised to m times (2j+2), multiplied by the finite products with factors 1 minus q raised to the prescribed even exponents and two geometric denominators.", DescribeRole.Definition),
            Node("andrews-el-bachraoui-defs-ccoeff", "C-prime coefficients", "cCoeff", "The coefficient cCoeff k m n is the coefficient of degree n in the truncation cTrunc k m n.", DescribeRole.Definition),
            Node("andrews-el-bachraoui-defs-dcoeff", "D-prime coefficients", "dCoeff", "The coefficient dCoeff k m n is the coefficient of degree n in the truncation dTrunc k m n.", DescribeRole.Definition),
            Node("andrews-el-bachraoui-defs-conjecture-two", "C-prime positivity statement", "conjectureTwo", "The statement conjectureTwo says that cCoeff 2 4 n is nonnegative for every natural number n.", DescribeRole.Definition),
            Node("andrews-el-bachraoui-defs-conjecture-three", "D-prime positivity statement", "conjectureThree", "The statement conjectureThree says that dCoeff 2 2 n is nonnegative for every natural number n.", DescribeRole.Definition),
            Node("andrews-el-bachraoui-defs-conjecture-four", "D-prime exceptional signs", "conjectureFour", "The statement conjectureFour says that dCoeff 2 3 n is negative exactly when n is 10 or 22.", DescribeRole.Definition)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
