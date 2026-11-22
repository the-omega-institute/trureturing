using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Rotors;

internal sealed class ProductBranchLevelsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Rotors/ProductBranchLevels.";
    private static readonly Formula A = F.Id("a"), B = F.Id("b"), C = F.Id("c");
    private static Formula At(string name, params Formula[] args) =>
        Seq(F.Id(name), Open, Seq(args), Close);

    private static Formula Levels()
    {
        var least = Seq(Mathrm, Grp(F.Id("min")));
        return Disp(Seq(D(0), Lt, A, Sp, Le, Sp, B, Sp, Rightarrow, Sp,
            least, At("E", Gt, D(0)), Eq, D(3), A, Comma, Quad, Sp,
            least, At("E", Gt, D(3), A), Eq, At("L", A, Comma, B)));
    }

    private static Formula Fiber() => Disp(Seq(D(0), Lt, A, Sp, Rightarrow, Sp,
        Open, At("L", A, Comma, B), Eq, At("L", A, Comma, C), Sp, Leftrightarrow, Sp,
        B, Eq, C, Sp, Lor, Sp, OpenBrace, B, Comma, C, CloseBrace, Eq,
        OpenBrace, A, Comma, D(2), A, CloseBrace, Sp, Lor, Sp,
        Open, D(8), A, Sp, Le, Sp, D(3), B, Sp, Land, Sp,
        D(8), A, Sp, Le, Sp, D(3), C, Close, Close));

    private static DocumentBlock.Describe DescribeEntry(string id, string declaration, string title, string text) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), DescribeRole.Definition);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For a fixed product rotor branch list with ordered positive coefficients, two distinct positive levels determine the smaller coefficient and classify all ambiguities in the larger one.",
        H("The first two positive energies of a product rotor ladder"),
        Blocks(
            DescribeEntry("rotor-branch", "energy", "Product rotor branch",
                "For nonnegative integral indices l and k, the listed energy is a l(l+2)+b k(k+2)."),
            DescribeEntry("rotor-above", "above", "Branches above a threshold",
                "Write E(>t) for the set of branch values strictly above t. Each distinct energy appears once."),
            DescribeEntry("rotor-second", "secondLevel", "Second-level formula",
                "Write L(a,b) for 6a when a=b and for min(3b,8a) otherwise."),
            Describe.Lean(DescribeId.Create("first-two"), DeclarationHandle.Create(Prefix + "first_two_positive_levels"),
                H("The lowest two distinct positive branch energies"), StatementSource.FromAuthor(Levels()),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The first positive value is 3a. The next distinct value equals 6a for equal coefficients. For a<b it equals the smaller of 3b and 8a. The indices (1,0), (1,1), (0,1) and (2,0) realize these candidates. Each single-rotor factor is zero, three, or at least eight. These alternatives bound every other branch from below."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("second-fiber"), DeclarationHandle.Create(Prefix + "second_level_fiber"),
                H("All parameter collisions of the second-level formula"), StatementSource.FromAuthor(Fiber()),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Fix a>0. The two first energies coincide for ordered candidates b,c≥a exactly in the listed cases. The value at b=a recurs at b=2a. For b≥8a/3 the second value stays equal to 8a. On the intervening unequal branch below the cutoff, L(a,b)=3b. The mathematical equality criterion for L itself holds for arbitrary real b and c."))), DescribeRole.Theorem))));
}
