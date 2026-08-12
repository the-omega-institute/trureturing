using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Entropy;

internal sealed class MutualInformationSymmDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite joint Shannon entropy and mutual information in nats are invariant under coordinate swap without distributional hypotheses.",
        H("Symmetry of Finite Mutual Information"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("joint-entropy-is-invariant-under-coordinate-swap"),
                DeclarationHandle.Create("D5/S3/Entropy/MutualInformationSymm.entropy_swap"),
                H("Joint entropy is invariant under coordinate swap"),
                StatementSource.FromAuthor(Disp(Seq(
                                    Begin, Grp(F.Id("gathered")),
                                    Forall, Sp, Iota, Comma, Sp, Kappa, Esc,
                                    OpenBracket,
                                    Operatorname, Grp(F.Id("Fintype")), Open, Iota, Close,
                                    CloseBracket, Sp,
                                    OpenBracket,
                                    Operatorname, Grp(F.Id("Fintype")), Open, Kappa, Close,
                                    CloseBracket, Comma, RowBreak,
                                    Forall, Sp, F.Id("p"), Colon, Sp,
                                    Iota, Times, Kappa, To, Sp, Mathbb, Grp(F.Id("R")), Comma, RowBreak,
                                    Operatorname, Grp(F.Id("shannonEntropy")), Open,
                                    Open,
                                    Open, F.Id("j"), Comma, Sp, F.Id("i"), Close, Mapsto, Sp,
                                    F.Id("p"), Open, F.Id("i"), Comma, Sp, F.Id("j"), Close,
                                    Close, Close, Eq, RowBreak,
                                    Operatorname, Grp(F.Id("shannonEntropy")), Open, F.Id("p"), Close, Dot,
                                    End, Grp(F.Id("gathered"))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                                    Paragraph(Text(
                                        "Only the two Fintype instances occur as hypotheses. Neither " +
                                        "pointwise nonnegativity nor normalization is required. This is a " +
                                        "strictly stronger hypothesis profile than that of every neighboring " +
                                        "result in the bucket, all of which assume pointwise nonnegativity and " +
                                        "some of which also assume normalization. The reason is structural: " +
                                        "symmetry is a property of the finite sum's index set, not of the " +
                                        "measure. Coordinate swap merely reindexes the sum, so no probabilistic " +
                                        "axiom participates.")),
                                    Paragraph(Text(
                                        "The equality is not definitional. In particular, rfl fails because " +
                                        "the left side is summed over kappa times iota while the right side is " +
                                        "summed over iota times kappa. Unfolding shannonEntropy and applying " +
                                        "Fintype.sum_prod_type exposes the two nested finite sums; " +
                                        "Finset.sum_comm then exchanges their order. This reindexing is the " +
                                        "entire content of the proof, no more and no less."))),
                DescribeRole.Theorem
            ),
            Describe.Lean(
                DescribeId.Create("finite-mutual-information-is-symmetric"),
                DeclarationHandle.Create("D5/S3/Entropy/MutualInformationSymm.mutual_information_symm"),
                H("Finite mutual information is symmetric"),
                StatementSource.FromAuthor(Disp(Seq(
                                    Begin, Grp(F.Id("gathered")),
                                    Forall, Sp, Iota, Comma, Sp, Kappa, Esc,
                                    OpenBracket,
                                    Operatorname, Grp(F.Id("Fintype")), Open, Iota, Close,
                                    CloseBracket, Sp,
                                    OpenBracket,
                                    Operatorname, Grp(F.Id("Fintype")), Open, Kappa, Close,
                                    CloseBracket, Comma, RowBreak,
                                    Forall, Sp, F.Id("p"), Colon, Sp,
                                    Iota, Times, Kappa, To, Sp, Mathbb, Grp(F.Id("R")), Comma, RowBreak,
                                    Operatorname, Grp(F.Id("mutualInformation")), Open,
                                    Open,
                                    Open, F.Id("j"), Comma, Sp, F.Id("i"), Close, Mapsto, Sp,
                                    F.Id("p"), Open, F.Id("i"), Comma, Sp, F.Id("j"), Close,
                                    Close, Close, Eq, RowBreak,
                                    Operatorname, Grp(F.Id("mutualInformation")), Open, F.Id("p"), Close, Dot,
                                    End, Grp(F.Id("gathered"))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                                    Paragraph(Text(
                                        "Mutual-information symmetry has the same unconditional signature: " +
                                        "only finiteness is assumed. A shorter composition through the frozen " +
                                        "mutual_information_eq_entropy_sub identity would make symmetry nearly " +
                                        "immediate from the entropy balance I = H(X) + H(Y) - H(X,Y). That route " +
                                        "is deliberately not used. The entropy-balance identity assumes " +
                                        "pointwise nonnegativity, so composing through it would contaminate an " +
                                        "unconditional statement with an avoidable hypothesis. Direct unfolding " +
                                        "preserves the actual strength of the result.")),
                                    Paragraph(Text(
                                        "This equality is likewise not definitional, and rfl fails for the same " +
                                        "mismatch between the index types kappa times iota and iota times kappa. " +
                                        "After mutualInformation, klDivergence, and marginal are unfolded, " +
                                        "Fintype.sum_prod_type and Finset.sum_comm discharge the coordinate " +
                                        "reindexing. The swap also exchanges the two marginal factors in the " +
                                        "reference product, and mul_comm restores their order. It does not make " +
                                        "the swapped marginal equal to the first marginal: the two marginals " +
                                        "exchange roles. The theorem contains exactly these reindexings and no " +
                                        "additional probabilistic assertion.")),
                                    Paragraph(Text(
                                        "Before this theorem, the bucket already contained mutual-information " +
                                        "nonnegativity, the equivalence between zero mutual information and " +
                                        "independence, the entropy decomposition of mutual information, the " +
                                        "entropy chain rule, conditioning reduces entropy, and both equality " +
                                        "cases of 0 <= H <= log card. Symmetry was the remaining elementary " +
                                        "property of mutual information. The coordinate swap that every " +
                                        "neighboring statement performs by hand in its own binder is now a " +
                                        "named, reusable fact.")),
                                    Paragraph(Text(
                                        "The units are nats because the underlying entropy and divergence use " +
                                        "Real.log. Nothing is claimed about conditional mutual information, " +
                                        "about a continuous or measure-theoretic analogue, or about systems " +
                                        "with more than two coordinates."))),
                DescribeRole.Theorem
            ))));
}
