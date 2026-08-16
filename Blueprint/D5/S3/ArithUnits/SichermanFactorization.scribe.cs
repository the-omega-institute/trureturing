using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ArithUnits;

internal sealed class SichermanFactorizationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An explicit polynomial has two distinct nonnegative-coefficient factorizations.",
        H("A Distinct Polynomial Factorization Pair"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("sicherman-polynomial-has-distinct-factorizations"),
                DeclarationHandle.Create(
                    "D5/S3/ArithUnits/SichermanFactorization."
                    + "sicherman_polynomial_has_distinct_factorizations"),
                H("The Sicherman polynomial has two distinct factorization pairs"),
                StatementSource.FromAuthor(Disp(Seq(
                    Open, D(1), Plus, F.Id("X"), Close,
                    Open, D(1), Plus, F.Id("X"), Caret, Grp(D(2)), Plus,
                    F.Id("X"), Caret, Grp(D(4)), Close,
                    Eq,
                    Open, D(1), Plus, F.Id("X"), Plus,
                    F.Id("X"), Caret, Grp(D(2)), Close,
                    Open, D(1), Plus, F.Id("X"), Caret, Grp(D(3)), Close,
                    Sp, Land, Sp,
                    Open, D(1), Plus, F.Id("X"), Comma, Sp,
                    D(1), Plus, F.Id("X"), Caret, Grp(D(2)), Plus,
                    F.Id("X"), Caret, Grp(D(4)), Close,
                    Neq,
                    Open, D(1), Plus, F.Id("X"), Plus,
                    F.Id("X"), Caret, Grp(D(2)), Comma, Sp,
                    D(1), Plus, F.Id("X"), Caret, Grp(D(3)), Close, Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "This is a clause-level closure of appendix E.146. It formalizes the "
                        + "displayed identity over the natural-coefficient polynomial semiring "
                        + "and proves that the two ordered factor pairs are different.")),
                    Paragraph(Text(
                        "It does not establish a general failure of unique factorization for "
                        + "natural-coefficient polynomials, classify ambiguous spectra, or "
                        + "formalize the atom's quantum-information interpretation.")),
                    Paragraph(Text(
                        "Pinned Mathlib was searched before proving. No exact declaration was "
                        + "found. The product identity is closed by commutative-semiring "
                        + "normalization, and distinctness follows because the first factors "
                        + "have different coefficients at degree two."))),
                DescribeRole.Theorem))));
}
