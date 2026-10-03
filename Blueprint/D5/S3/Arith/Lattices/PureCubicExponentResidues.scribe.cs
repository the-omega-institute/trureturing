using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Lattices;

internal sealed class PureCubicExponentResiduesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every positive integer has canonical coprime squarefree factors for its cubic exponent residues.",
        H("Cubic Exponent Residues"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("pure-cubic-exponent-residues"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/Lattices/PureCubicExponentResidues.pure_cubic_exponent_residues"),
                H("Canonical mixed-radicand factors"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let B be a positive integer. For each prime p, divide its exponent in B "
                            + "by three. Let c contain the quotient of each division, let m contain "
                            + "the primes with remainder one, and let n contain the primes with "
                            + "remainder two.")),
                    Paragraph(Text(
                        "The three factors are positive. Both m and n are squarefree, they are "
                            + "coprime, and B equals c cubed times m times n squared. For every p, "
                            + "the exponent in c is the quotient, while the exponents in m and n "
                            + "are respectively one exactly for remainders one and two. These "
                            + "conditions uniquely determine c, m, and n.")),
                    Paragraph(Text(
                        "The quotient B divided by c cubed has every prime exponent below three, "
                            + "and its radical is m times n. The proof compares prime exponents "
                            + "after Euclidean division; disjoint remainder classes give "
                            + "coprimality."))),
                DescribeRole.Theorem))));
}
