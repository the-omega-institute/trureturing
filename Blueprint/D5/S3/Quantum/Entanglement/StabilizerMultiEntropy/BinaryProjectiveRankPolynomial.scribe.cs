using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.StabilizerMultiEntropy;

internal sealed class BinaryProjectiveRankPolynomialDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Quantum/Entanglement/StabilizerMultiEntropy/BinaryProjectiveRankPolynomial.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual binary projective rank sum has an exact product normalization over every field.",
        H("Normalized binary projective rank polynomial"),
        Blocks(
            Describe.Lean(DescribeId.Create("binary-projective-rank-factor"),
                DeclarationHandle.Create(Owner + "normalized_factor"),
                H("Exact normalized evaluation"),
                StatementSource.FromAuthor(Statement()), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For dimension d, take every subset U of the nonzero vectors of the binary d-dimensional space. "
                        + "The normalized rank sum W(d,q) adds (-1)^|U| times (q^(-1)) raised to the binary dimension of the span of U. "
                        + "The factor P(d,q) is the product of (1 - 2^j/q) over 0 <= j < d. "
                        + "These definitions include the empty projective configuration.")),
                    Paragraph(Text("This is the normalized form of the classical characteristic polynomial of binary projective geometry "
                        + "in the Crapo–Rota framework. The proof counts injections using inclusion–exclusion at sizes 2^m, "
                        + "then uses infinitely many integral evaluations and specializes the polynomial identity in the given field. "
                        + "The mathematical use here is the unbounded signed-marginal obstruction in the accompanying graph-state coverage classification."))),
                DescribeRole.Theorem))));

    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);

    private static Formula Statement()
    {
        var d = F.Id("d");
        var q = F.Id("q");
        return Disp(All("d", Seq(Mathbb, Grp(F.Id("N"))),
            All("R", F.Id("Fields"),
                All("q", Call("Nonzero", F.Id("R")), Equal(Call("W", d, q), Call("P", d, q))))));
    }
}
