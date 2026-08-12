using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Entropy;

internal sealed class MutualInformationEntropyDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create("Finite mutual information in nats decomposes into marginal and joint Shannon entropies, yielding entropy subadditivity.", H("Mutual Information as an Entropy Balance"), Blocks(
            Describe.Lean(DescribeId.Create("mutual-information-is-the-entropy-balance"), DeclarationHandle.Create("D5/S3/Entropy/MutualInformationEntropy.mutual_information_eq_entropy_sub"), H("Mutual information is the entropy balance"), StatementSource.FromAuthor(Disp(Seq(
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
                    Open,
                    Forall, Sp, F.Id("i"), Comma, Sp, F.Id("j"), Comma, Sp,
                    D(0), Le, Sp, F.Id("p"), Open,
                    F.Id("i"), Comma, F.Id("j"), Close,
                    Close, Sp, Rightarrow, RowBreak,
                    Operatorname, Grp(F.Id("mutualInformation")), Open, F.Id("p"), Close, Eq,
                    Operatorname, Grp(F.Id("shannonEntropy")), Open,
                    Operatorname, Grp(F.Id("marginal")), Open, F.Id("p"), Close,
                    Close, Plus,
                    Operatorname, Grp(F.Id("shannonEntropy")), Open,
                    Operatorname, Grp(F.Id("marginal")), Open,
                    Open, F.Id("j"), Comma, F.Id("i"), Close, Mapsto, Sp,
                    F.Id("p"), Open, F.Id("i"), Comma, F.Id("j"), Close,
                    Close, Close, Minus,
                    Operatorname, Grp(F.Id("shannonEntropy")), Open, F.Id("p"), Close, Dot,
                    End, Grp(F.Id("gathered"))))), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text(
                        "The decomposition is the identity tying this bucket's two definitions " +
                        "together: mutual information equals the sum of the two marginal " +
                        "entropies minus the joint entropy. Both marginal entropies use the " +
                        "repository's single marginal definition; the second applies it to the " +
                        "coordinate-swapped joint. The units are nats because the definitions " +
                        "use Real.log. This module defines nothing of its own.")),
                    Paragraph(Text(
                        "This theorem is the general pin. The sibling module " +
                        "D5/S3/Entropy/MutualInformationProduct constrains the " +
                        "mutual-information definition only on product joints, and is blind to " +
                        "a reference that agrees there but differs on correlated joints. The " +
                        "decomposition holds for every admissible joint, including correlated " +
                        "joints, so it constrains the definition exactly where the product-law " +
                        "identity could not. It does not by itself make the mutual-information " +
                        "definition beyond question; it establishes this specific consistency " +
                        "relation with the imported entropy and marginal definitions.")),
                    Paragraph(Text(
                        "The hypotheses are deliberately minimal: the decomposition needs only " +
                        "nonnegativity of the joint, and normalization is not required. This " +
                        "asymmetry matters because a reader may expect both results to require a " +
                        "probability distribution. Zero-mass cells are handled by cases without " +
                        "assuming positive marginals. In particular, a cell may vanish while " +
                        "both of its marginals are positive; that case is covered, not " +
                        "excluded."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("joint-entropy-is-subadditive"), DeclarationHandle.Create("D5/S3/Entropy/MutualInformationEntropy.entropy_subadditive"), H("Joint entropy is subadditive"), StatementSource.FromAuthor(Disp(Seq(
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
                    Open,
                    Open,
                    Forall, Sp, F.Id("i"), Comma, Sp, F.Id("j"), Comma, Sp,
                    D(0), Le, Sp, F.Id("p"), Open,
                    F.Id("i"), Comma, F.Id("j"), Close,
                    Close, Sp, Land, Sp,
                    Sum, Underscore, Grp(F.Id("i"), Comma, F.Id("j")),
                    F.Id("p"), Open, F.Id("i"), Comma, F.Id("j"), Close, Eq, D(1),
                    Close, Sp, Rightarrow, RowBreak,
                    Operatorname, Grp(F.Id("shannonEntropy")), Open, F.Id("p"), Close, Le,
                    Operatorname, Grp(F.Id("shannonEntropy")), Open,
                    Operatorname, Grp(F.Id("marginal")), Open, F.Id("p"), Close,
                    Close, Plus,
                    Operatorname, Grp(F.Id("shannonEntropy")), Open,
                    Operatorname, Grp(F.Id("marginal")), Open,
                    Open, F.Id("j"), Comma, F.Id("i"), Close, Mapsto, Sp,
                    F.Id("p"), Open, F.Id("i"), Comma, F.Id("j"), Close,
                    Close, Close, Dot,
                    End, Grp(F.Id("gathered"))))), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text(
                        "Entropy subadditivity is derived, not independently proven. The proof " +
                        "rewrites the decomposition against the frozen " +
                        "mutual_information_nonneg theorem; nothing about nonnegativity is " +
                        "re-proved. Normalization enters only here, because it is required to " +
                        "invoke that frozen nonnegativity theorem.")),
                    Paragraph(Text(
                        "The conclusion is H(X,Y) <= H(X) + H(Y) for the two marginals of a " +
                        "finite joint, in nats. It does not give an equality condition for " +
                        "subadditivity: no characterization of when H(X,Y) = H(X) + H(Y), " +
                        "equivalently independence, is claimed. It says nothing about " +
                        "conditional entropy or conditional mutual information, and nothing " +
                        "beyond two coordinates."))), DescribeRole.Theorem))));
}
