using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Permanental;

internal sealed class PanSkanderaWangAllSplitsChainDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Permanental/PanSkanderaWangAllSplitsChain.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Combinatorics/pan2026permanental");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "TNN means that every square submatrix selected by increasing row and column embeddings has nonnegative determinant.",
        H("PanSkanderaWangAllSplitsChain"),
        Blocks(
            Node("tnn", "TNN", "TNN",
                TNNFormula(),
                "Source, Section 1 (p. 139): “We call A ∈ Matₙ×ₙ(ℝ) totally nonnegative if each of its minors is negative.” The next sentence specifies the defining inequalities det(Aᵢ,ⱼ) ≥ 0. The word negative in the first sentence conflicts with those displayed inequalities; TNN uses the displayed nonnegative inequalities. Every square submatrix selected by increasing row and column embeddings has nonnegative determinant. OrderEmbedding denotes the increasing order embeddings in the Lean statement, including the empty minor.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("principalpermanent", "principalPermanent", "principalPermanent",
                principalPermanentFormula(),
                "The principal permanent uses Matrix.permanent on the literal subtype of indices belonging to s. Here val on a subtype is its underlying Fin n index; an empty principal permanent is one.",
                DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("evenindices", "evenIndices", "evenIndices",
                evenIndicesFormula(),
                "Lean indices start at zero. Filtering by (val i + 1) mod 2 = 0 therefore selects the even indices printed in the paper.",
                DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("prefixindices", "prefixIndices", "prefixIndices",
                prefixIndicesFormula(),
                "The initial h indices are selected by val i < h, with no restriction on h in this definition.",
                DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("monomial", "monomial", "monomial",
                monomialFormula(),
                "The operator prod multiplies its function over every element of the finite domain. The monomial places the permutation value in the column index.",
                DescribeRole.Definition, AssessedProvenance.FromRepo(Source))),
        []));

    private static DocumentBlock Node(string id, string title, string declaration,
        Formula formula, string prose, DescribeRole role, AssessedProvenance provenance) =>
        Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(formula), provenance, Blocks(Paragraph(Text(prose))), role);

    private static Formula TNNFormula() => Disp(
        All("n", Naturals(), All("A", Call("Matrix", Call("Fin", F.Id("n")), Call("Fin", F.Id("n")), Reals()), Iff(Call("TNN", F.Id("A")), All("k", Naturals(), All("r", Call("OrderEmbedding", Call("Fin", F.Id("k")), Call("Fin", F.Id("n"))), All("c", Call("OrderEmbedding", Call("Fin", F.Id("k")), Call("Fin", F.Id("n"))), LessEqual(D(0), Call("det", Call("submatrix", F.Id("A"), F.Id("r"), F.Id("c")))))))))));

    private static Formula principalPermanentFormula() => Disp(
        All("n", Naturals(), All("A", Call("Matrix", Call("Fin", F.Id("n")), Call("Fin", F.Id("n")), Reals()), All("s", Call("Finset", Call("Fin", F.Id("n"))), Equal(Call("principalPermanent", F.Id("A"), F.Id("s")), Call("permanent", Call("submatrix", F.Id("A"), LambdaOf("i", F.Id("s"), Call("val", F.Id("i"))), LambdaOf("j", F.Id("s"), Call("val", F.Id("j"))))))))));

    private static Formula evenIndicesFormula() => Disp(
        All("n", Naturals(), Equal(Call("evenIndices", F.Id("n")), Call("filter", Call("univ", Call("Fin", F.Id("n"))), LambdaOf("i", Call("Fin", F.Id("n")), Equal(new Formula.Modulo(Add(Call("val", F.Id("i")), D(1)), D(2)), D(0)))))));

    private static Formula prefixIndicesFormula() => Disp(
        All("n", Naturals(), All("h", Naturals(), Equal(Call("prefixIndices", F.Id("n"), F.Id("h")), Call("filter", Call("univ", Call("Fin", F.Id("n"))), LambdaOf("i", Call("Fin", F.Id("n")), LessThan(Call("val", F.Id("i")), F.Id("h"))))))));

    private static Formula monomialFormula() => Disp(
        All("n", Naturals(), All("A", Call("Matrix", Call("Fin", F.Id("n")), Call("Fin", F.Id("n")), Reals()), All("w", Call("Perm", Call("Fin", F.Id("n"))), Equal(Call("monomial", F.Id("A"), F.Id("w")), Call("prod", LambdaOf("k", Call("Fin", F.Id("n")), App(F.Id("A"), F.Id("k"), App(F.Id("w"), F.Id("k"))))))))));
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula App(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);

    private static Formula LambdaOf(string name, Formula domain, Formula body) =>
        Seq(F.Id("fun"), Sp, Parenthesized(Seq(F.Id(name), Sp, Colon, Sp, domain)),
            Sp, Mapsto, Sp, body);

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);

    private static Formula Naturals() => Seq(Mathbb, Sp, Grp(F.Id("N")));

    private static Formula Reals() => Seq(Mathbb, Sp, Grp(F.Id("R")));

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula LessEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);

    private static Formula LessThan(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);

    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);

    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));
}
