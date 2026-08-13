using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Diagonal.Probability;

internal sealed class EquivariantEscapeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        var addressRepresentative = new Formula.Subscript(F.Id("a"), D(0));

        return DocumentDefinition.Create(ScribeNode.Create(
            "Uniform equivariant listings have the exact transitive escape probability.",
            H("Uniform Equivariant Escape Probability"),
            Blocks(
                Describe.Lean(
                DescribeId.Create("transitive-uniform-equivariant-escape-probability"),
                DeclarationHandle.Create(
                    "D5/S0/Diagonal/Probability/EquivariantEscape."
                    + "transitive_equivariant_escape_probability"),
                H("Transitive uniform equivariant escape probability"),
                StatementSource.FromAuthor(Disp(Seq(
                    Call("PescEq", F.Id("f")), Sp, Eq, Sp, D(1), Sp, Minus, Sp,
                    Frac, Grp(Call("card", Call("Fix", F.Id("f")))),
                    Grp(
                        Call("card", F.Id("Y")), Caret,
                        Grp(Call("card", Call("StabilizerOrbit", addressRepresentative)))),
                    Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For a transitive group action, choose an address representative a_0. "
                        + "Let omega be the number of stabilizer orbits on addresses, n the "
                        + "cardinality of Y, and k the number of fixed points of f. The canonical "
                        + "stabilizer-orbit coordinates identify all equivariant listings with "
                        + "n^omega parameter choices. Exactly n^omega-k choices escape, so the "
                        + "uniform PMF assigns the escape event probability 1-k/n^omega.")),
                    Paragraph(Text(
                        "A subgroup G of Sym(A) acts faithfully on A. The Lean theorem is freely "
                        + "more general: it assumes only a group action and transitivity, so it also "
                        + "covers nonfaithful actions without weakening the source claim.")),
                    Paragraph(Text(
                        "The imported general orbit-product theorem and its regular Z3, regular Z4, "
                        + "and nonregular S3 arithmetic checks retain the source's general-case and "
                        + "redundant-verification clauses."))),
                    DescribeRole.Theorem)),
            [
                DocumentEdge.Dependency.Create(
                    GidRef.Create("D5/S0/Diagonal/EquivariantEscape")),
            ]));
    }
}
