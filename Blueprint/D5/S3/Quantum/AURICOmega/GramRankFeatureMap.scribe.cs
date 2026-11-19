using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.AURICOmega;

internal sealed class GramRankFeatureMapDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/AURICOmega/GramRankFeatureMap.";
    private static LibraryNoteRef Source => LibraryNoteRef.Create("D5/L/HilbertOperators/aronszajn1950theory");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For the reading of a ternary comparison structure, a uniform bound r on the rank of all finite Gram matrices is equivalent to the reading being the Gram kernel of a map into Euclidean r-space.",
        H("Finite Gram rank and Euclidean feature maps"),
        Blocks(
            Node("gram-rank-le-iff-has-feature-rank", "gramRankLE_iff_hasFeatureRank",
                "Gram rank at most r and feature maps into Euclidean r-space",
                StatementSource.FromAuthor(EquivalenceFormula()), AssessedProvenance.FromRepo(Source),
                "Let C be a ternary comparison structure on M and r a natural number. "
                    + "The left side says that for every n and every family x : Fin n -> M the matrix with entries kappa (x i) (x j) has rank at most r. "
                    + "The right side says that there is a map f from M into the Euclidean space of dimension r with kappa x y equal to the real inner product of f x and f y for all x and y. "
                    + "If such an f exists, each Gram matrix of the reading is the Gram matrix of the vectors f (x i) in an r-dimensional space, "
                    + "so it factors through r coordinates and has rank at most r. "
                    + "Conversely, the reading is symmetric with nonnegative finite Gram forms, so it is a positive semidefinite kernel, "
                    + "and its reproducing kernel Hilbert space contains kernel functions k x with inner product kappa x y between k x and k y. "
                    + "A linearly independent family of kernel functions has an invertible Gram matrix, so by the rank bound it has at most r members. "
                    + "A maximal such family therefore exists, spans every kernel function, and spans a subspace of dimension at most r. "
                    + "Coordinates of the kernel functions in an orthonormal basis of that subspace, padded by zero coordinates up to dimension r, give the map f.",
                DescribeRole.Theorem))));

    private static DocumentBlock Node(
        string id, string selector, string title, StatementSource statement,
        AssessedProvenance provenance, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("gram-rank-feature-map-" + id),
            DeclarationHandle.Create(Prefix + selector), H(title), statement, provenance,
            Blocks(Paragraph(Text(prose))), role);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
    private static Formula Logic(Formula x, FormulaLogicOperator op, Formula y) => new Formula.Logic(x, op, y);
    private static Formula ForAll(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);

    private static Formula M => F.Id("M");
    private static Formula C => F.Id("C");
    private static Formula Naturals => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula TypeStar => Seq(Operatorname, Grp(F.Id("Type")), Star);

    private static Formula EquivalenceFormula()
    {
        Formula r = F.Id("r");
        return Disp(ForAll("M", TypeStar, ForAll("C", Call("TernaryComparison", M),
            ForAll("r", Naturals,
                Logic(Call("GramRankLE", C, r), FormulaLogicOperator.Iff, Call("HasFeatureRank", C, r))))));
    }
}
