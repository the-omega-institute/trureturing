using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Estimation.DecisionRisk;

internal sealed class FixedMarginalGenericFeaturesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A fixed data marginal relates universal signed-loss quality to one randomized reconstruction rule.",
        H("Fixed-marginal generic features"),
        Blocks(Describe.Lean(
            DescribeId.Create("fixed-marginal-generic-features"),
            DeclarationHandle.Create("D5/S3/Estimation/DecisionRisk/FixedMarginalGenericFeatures.generic_quality_iff_reconstruction"),
            H("Universal decision quality and reconstruction"),
            StatementSource.FromAuthor(Statement()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("Let X and Z be arbitrary finite types, q a nonnegative real mass of total one on X, and phi a row-stochastic encoder from X to Z. For epsilon greater than zero, universal quality means that every finite hypothesis type, normalized prior, nonempty finite action type, compatible experiment with data marginal q, and real signed loss has feature Bayes risk minus data Bayes risk at most epsilon times the maximum absolute loss. All four type universes are independent.")),
                Paragraph(Text("The Bayes risk is the real sInf of finiteBayesCost over every row-stochastic randomized decision. Negative losses remain signed. The finite maximum is lossNorm, the real supremum of the finite nonempty set of absolute loss values. Normalization supplies nonemptiness of the data and hypothesis types; the encoder then supplies nonemptiness of the feature type. No support condition is imposed on any entry.")),
                Paragraph(Text("This universal quality condition holds precisely when a single stochastic decoder from Z to X has q-weighted mismatch probability at most epsilon divided by two. The decoder is common to all compatible decision problems. Its error is the sum over x, z and y of q(x) phi(x,z) d(z,y) times the indicator of y different from x.")),
                Paragraph(Text("For the forward transport estimate, compose an optimal data decision with the decoder. Its conditional expected loss lies between minus and plus the maximum absolute loss. Replacing x by a reconstructed y changes this conditional loss by at most twice that maximum, and changes nothing when y equals x. Averaging against the common joint law and using its marginal q gives twice the reconstruction error as the normalized risk bound.")),
                Paragraph(Text("For necessity, relabel the data type into finite hypothesis and action types in their independent universes. Use the identity experiment and the signed loss minus one for correct reconstruction and plus one for a mismatch. Its data Bayes risk is minus one, and its feature risk is twice the minimum mismatch probability minus one. A finite observationwise argmin attains this real minimum, including on null observation fibers. Applying universal quality yields an attaining decoder at half the quality bound.")),
                Paragraph(Text("The source is van Rooyen and Williamson, Le Cam meets LeCun: Deficiency and Generic Feature Learning, arXiv:1402.4884v2, Definition 3 and Theorem 3; Section 2 specifies signed loss normalization and Section 7.5 uses full l1 variational distance. The mismatch indicator and factor two here follow from the signed reconstruction loss directly. The result concerns finite stochastic experiments and makes no measurable infinite-space claim."))),
            DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. args]);
    private static Formula Statement()
    {
        Formula x = F.Id("X"), z = F.Id("Z"), q = F.Id("q"), phi = F.Id("phi");
        Formula eps = F.Id("epsilon"), d = F.Id("d");
        Formula assumptions = Seq(Call("Fintype", x), Sp, Land, Sp, Call("Fintype", z),
            Sp, Land, Sp, Call("Nonnegative", q), Sp, Land, Sp, Call("sum", q), Sp, Eq, Sp, D(1),
            Sp, Land, Sp, Call("IsRowStochastic", phi), Sp, Land, Sp, D(0), Sp, Lt, Sp, eps);
        Formula conclusion = Seq(Call("GenericQuality", q, phi, eps), Sp, Leftrightarrow, Sp,
            Exists, Sp, d, Colon, Sp, Call("FiniteMarkovKernel", z, x), Comma, Sp,
            Call("reconstructionError", q, phi, d), Sp, Leq, Sp,
            Seq(Frac, Grp(eps), Grp(D(2))));
        return Disp(Seq(Forall, Sp, x, Comma, Sp, z, Comma, Sp, q, Comma, Sp, phi, Comma, Sp, eps,
            Comma, Sp, Grp(assumptions), Sp, Rightarrow, Sp, Grp(conclusion)));
    }
}
