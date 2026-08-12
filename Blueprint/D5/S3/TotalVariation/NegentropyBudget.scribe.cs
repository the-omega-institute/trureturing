using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.TotalVariation;

internal sealed class NegentropyBudgetDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        Header(
            "D5/S3/TotalVariation/NegentropyBudget",
            "Distance from the uniform law is controlled by the finite Shannon entropy deficit in nats."),
        H("The Finite Negentropy Budget"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("total-variation-from-uniform-is-bounded-by-the-entropy-deficit"),
                DeclarationHandle.Create("D5/S3/TotalVariation/NegentropyBudget.total_variation_uniform_le_sqrt_entropy_deficit"),
                H("Total variation from uniform is bounded by the entropy deficit"),
                StatementSource.FromAuthor(Disp(Seq(
                                    Begin, Grp(F.Id("gathered")),
                                    Forall, Sp, Iota, Esc,
                                    OpenBracket,
                                    Operatorname, Grp(F.Id("Fintype")), Open, Iota, Close,
                                    CloseBracket, Sp,
                                    OpenBracket,
                                    Operatorname, Grp(F.Id("Nonempty")), Open, Iota, Close,
                                    CloseBracket, Comma, RowBreak,
                                    Forall, Sp, F.Id("r"), Colon, Sp,
                                    Iota, To, Sp, Mathbb, Grp(F.Id("R")), Comma, RowBreak,
                                    Open,
                                    Open, Forall, Sp, F.Id("i"), Comma, Sp,
                                    D(0), Le, Sp, F.Id("r"), Open, F.Id("i"), Close, Close,
                                    Sp, Land, Sp,
                                    Sum, Underscore, Grp(F.Id("i")),
                                    F.Id("r"), Open, F.Id("i"), Close, Eq, D(1),
                                    Close, Sp, Rightarrow, RowBreak,
                                    D(2), Sp,
                                    Operatorname, Grp(F.Id("TV")), Open,
                                    F.Id("r"), Comma, Sp,
                                    Open, F.Id("i"), Mapsto, Sp,
                                    Operatorname, Grp(F.Id("card")), Open, Iota, Close,
                                    Caret, Grp(Minus, D(1)), Close, Close,
                                    Sp, Le, Sp,
                                    Sqrt, Grp(
                                        D(2), Sp, Open,
                                        Log, Open,
                                        Operatorname, Grp(F.Id("card")), Open, Iota, Close,
                                        Close, Minus, F.Id("H"), Open, F.Id("r"), Close,
                                        Close), Dot,
                                    End, Grp(F.Id("gathered"))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                                    Paragraph(Text(
                                        "Let r be a nonnegative normalized mass function on a nonempty finite " +
                                        "alphabet and let u be the uniform mass. The theorem proves 2 TV(r,u) " +
                                        "<= sqrt(2(log |iota| - H(r))). Total variation uses the repository's " +
                                        "probability normalization, and the logarithm and Shannon entropy are " +
                                        "both measured in nats.")),
                                    Paragraph(Text(
                                        "The proof is an assembly of previously frozen results. Pinsker gives " +
                                        "2 TV(r,u)^2 <= D(r||u), the entropy-divergence identity rewrites the " +
                                        "right side as log |iota| - H(r), and total-variation nonnegativity " +
                                        "allows mathlib's square-root order lemma to convert the squared bound " +
                                        "to the displayed form. No analytic inequality is re-proved here.")),
                                    Paragraph(Text(
                                        "The statement is deliberately about a finite probability mass r. The " +
                                        "repository has no state-dependent quantity muStar and no theorem " +
                                        "identifying finite Shannon entropy of a supplied spectrum with a " +
                                        "density matrix's von Neumann entropy. The observer perturbation " +
                                        "seminorm concerns permutation update defects and is not such a " +
                                        "quantity. Accordingly, this theorem does not claim a muStar bound.")),
                                    Paragraph(Text(
                                        "No forgetting monotonicity, endpoint saturation, fourth-order qubit " +
                                        "expansion, pure-end rank estimate, or numerical certificate is asserted. " +
                                        "The existing total-variation data-processing theorem applies a channel " +
                                        "to both reference masses; it does not preserve this uniform reference " +
                                        "without an additional uniform-preservation hypothesis."))),
                DescribeRole.Theorem
            ))));
}
