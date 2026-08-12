using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Entropy;

internal sealed class MutualInformationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create("Finite classical mutual information in nats is nonnegative for every nonnegative normalized joint mass function.", H("Nonnegativity of Finite Classical Mutual Information"), Blocks(
            Describe.Lean(DescribeId.Create("finite-classical-mutual-information-is-nonnegative"), DeclarationHandle.Create("D5/S3/Entropy/MutualInformation.mutual_information_nonneg"), H("Finite classical mutual information is nonnegative"), StatementSource.FromAuthor(Disp(Seq(
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
                    Open, Forall, Sp, F.Id("i"), Comma, Sp, F.Id("j"), Comma, Sp,
                    D(0), Le, Sp, F.Id("p"), Open,
                    F.Id("i"), Comma, F.Id("j"), Close, Close,
                    Sp, Land, Sp,
                    Sum, Underscore, Grp(F.Id("i"), Comma, F.Id("j")),
                    F.Id("p"), Open, F.Id("i"), Comma, F.Id("j"), Close, Eq, D(1),
                    Close, Sp, Rightarrow, RowBreak,
                    D(0), Le, Sp,
                    Operatorname, Grp(F.Id("mutualInformation")), Open, F.Id("p"), Close, Dot,
                    End, Grp(F.Id("gathered"))))), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text(
                        "Mutual information is the divergence of the joint distribution from " +
                        "the product of its own two marginals. The marginal definition from " +
                        "D5/S3/Divergence/ChainRule is deliberately reused for both coordinates: " +
                        "the first directly, and the second by evaluating that same marginal on " +
                        "the swapped joint fun r => p (r.2, r.1), so no second marginal is " +
                        "defined. This reuse is deliberate: marginal remains the single source " +
                        "of truth.")),
                    Paragraph(Text(
                        "The bound is D5/S3/Divergence/GrandmotherTheorem.kl_divergence_nonneg " +
                        "applied to the product reference; all three of its premises are " +
                        "discharged here, not assumed. The product of marginals is nonnegative " +
                        "because each marginal is a finite sum of nonnegative joint masses. The " +
                        "product reference is normalized: each marginal sum collapses to the " +
                        "joint sum, and the product of the two unit sums is one. It is absolutely " +
                        "continuous because each joint mass is bounded by each of its marginals, " +
                        "so a vanishing product forces a vanishing joint mass. Nothing about " +
                        "nonnegativity of divergence is re-proved.")),
                    Paragraph(Text(
                        "The nonnegativity bound holds for any admissible reference and therefore " +
                        "does not by itself certify that the reference is the product of the " +
                        "joint's own marginals. The mutual-information content resides entirely " +
                        "in the definition, which is where a reader should look. Concretely, the " +
                        "reference at (i, j) is the first marginal at i times the second marginal " +
                        "at j, and the second marginal is obtained by evaluating the same marginal " +
                        "function on the coordinate-swapped joint fun r => p (r.2, r.1); a reader " +
                        "must not misread this as a second copy of the first marginal.")),
                    Paragraph(Text(
                        "The hypotheses are nonnegativity and normalization of the joint only, " +
                        "not strict positivity. Zero-mass cells are permitted. The units are " +
                        "nats, consistent with klDivergence and with the bucket's entropy " +
                        "definition.")),
                    Paragraph(Text(
                        "This module proves nonnegativity only; it does not characterize the " +
                        "equality case that I = 0 exactly when the joint equals the product of " +
                        "its marginals, equivalently independence. It does not relate mutual " +
                        "information to Shannon entropy: no I = H(X) + H(Y) - H(X,Y) identity is " +
                        "established here. It says nothing about conditional mutual information " +
                        "or about more than two coordinates."))), DescribeRole.Theorem))));
}
