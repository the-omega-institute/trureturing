using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.AURICOmega;

internal sealed class GramIsometryExtensionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/AURICOmega/GramIsometryExtension.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A permutation of the index set of a spanning family in a real inner product space that preserves all pairwise inner products extends to exactly one linear isometry equivalence.",
        H("Isometric extension of Gram-preserving permutations"),
        Blocks(
            Node("exists-unique", "existsUnique_linearIsometryEquiv_of_gram_preserving",
                "Gram-preserving permutations extend uniquely to isometries",
                StatementSource.FromAuthor(ExtensionFormula()), AssessedProvenance.FromRepo(),
                "Let E be a real inner product space and let phi be a family of vectors of E, indexed by a type iota, whose range spans E as a real vector space; no finite dimensionality or completeness of E is assumed, and the span is the algebraic span, not its closure. "
                    + "Let sigma be a permutation of iota with <phi(sigma a), phi(sigma b)> = <phi a, phi b> for all indices a and b. "
                    + "Then there is exactly one linear isometry equivalence U of E onto itself with U(phi a) = phi(sigma a) for every index a. "
                    + "For existence, write L for the linear map sending a finitely supported coefficient function c on iota to the finite combination of the vectors phi a with coefficients c a, and L' for the same map built from the reindexed family a -> phi(sigma a). "
                    + "Bilinearity of the inner product and the hypothesis on sigma give <L' c, L' d> = <L c, L d> for all coefficient functions c and d, so L' c and L c have the same norm. "
                    + "Hence the kernel of L is contained in the kernel of L', and L' factors through L, which is surjective because the range of phi spans E. "
                    + "The induced linear map U of E onto itself satisfies U(L c) = L' c, preserves norms, and is surjective because the range of the reindexed family is again the range of phi; it is therefore a linear isometry equivalence, and evaluating at the coefficient function of a single index gives U(phi a) = phi(sigma a). "
                    + "For uniqueness, two linear maps that agree on a spanning set agree everywhere.",
                DescribeRole.Theorem))));

    private static DocumentBlock Node(
        string id, string selector, string title, StatementSource statement,
        AssessedProvenance provenance, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("gram-isometry-extension-" + id),
            DeclarationHandle.Create(Prefix + selector), H(title), statement, provenance,
            Blocks(Paragraph(Text(prose))), role);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
    private static Formula Ap(Formula function, Formula argument) => new Formula.Apply(function, [argument]);
    private static Formula Reals => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula TypeStar => Seq(Operatorname, Grp(F.Id("Type")), Star);
    private static Formula Inner(Formula x, Formula y) =>
        new Formula.Subscript(Seq(Langle, Sp, x, Comma, Sp, y, Sp, Rangle), Reals);

    private static Formula ExtensionFormula()
    {
        Formula e = F.Id("E"), a = F.Id("a"), b = F.Id("b"), u = F.Id("U");
        Formula spans = Seq(Call("span", Reals, Call("range", Varphi)), Sp, Eq, Sp,
            Operatorname, Grp(F.Id("top")));
        Formula gram = Seq(Inner(Ap(Varphi, Ap(SigmaLower, a)), Ap(Varphi, Ap(SigmaLower, b))), Sp, Eq, Sp,
            Inner(Ap(Varphi, a), Ap(Varphi, b)));
        Formula extension = Seq(Ap(u, Ap(Varphi, a)), Sp, Eq, Sp, Ap(Varphi, Ap(SigmaLower, a)));
        return Disp(Seq(
            Forall, Sp, Iota, Comma, Sp, e, Colon, Sp, TypeStar, Comma, Sp,
            OpenBracket, Call("NormedAddCommGroup", e), CloseBracket, Comma, Sp,
            OpenBracket, Call("InnerProductSpace", Reals, e), CloseBracket, Comma, Sp,
            Forall, Sp, Varphi, Colon, Sp, Iota, Sp, To, Sp, e, Comma, Sp,
            spans, Sp, Rightarrow, Sp,
            Forall, Sp, SigmaLower, Colon, Sp, Call("Perm", Iota), Comma, Sp,
            Open, Forall, Sp, a, Comma, Sp, b, Colon, Sp, Iota, Comma, Sp, gram, Close, Sp, Rightarrow, Sp,
            Exists, Bang, Sp, u, Colon, Sp, Call("LinearIsometryEquiv", Reals, e, e), Comma, Sp,
            Forall, Sp, a, Colon, Sp, Iota, Comma, Sp, extension));
    }
}
