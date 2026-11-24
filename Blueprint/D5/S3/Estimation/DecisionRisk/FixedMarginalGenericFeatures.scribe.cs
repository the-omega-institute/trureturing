using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Estimation.DecisionRisk;

internal sealed class FixedMarginalGenericFeaturesDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Estimation/vanrooyenwilliamson2014genericfeatures");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A fixed data marginal relates universal signed-loss quality to one randomized reconstruction rule.",
        H("Fixed-marginal generic features"),
        Blocks(Describe.Lean(
            DescribeId.Create("fixed-marginal-generic-features"),
            DeclarationHandle.Create("D5/S3/Estimation/DecisionRisk/FixedMarginalGenericFeatures.generic_quality_iff_reconstruction"),
            H("Universal decision quality and reconstruction"),
            StatementSource.FromAuthor(Statement()),
            AssessedProvenance.FromLiterature(Source),
            Blocks(
                Paragraph(Text("Here X : Type u and Z : Type v are finite types, q : X → ℝ, phi : X → Z → ℝ and epsilon : ℝ. The decoder d : FiniteMarkovKernel Z X has an underlying row-stochastic array of type Z → X → ℝ. GenericQuality quantifies finite hypothesis types Theta : Type w and nonempty finite action types A : Type t, with prior pi : Theta → ℝ, experiment T : Theta → X → ℝ and loss L : Theta → A → ℝ; u, v, w and t are independent universes.")),
                Paragraph(Text("Let X and Z be arbitrary finite types, q a nonnegative real mass of total one on X, and phi a row-stochastic encoder from X to Z. For epsilon greater than zero, universal quality means that every finite hypothesis type, normalized prior, nonempty finite action type, compatible experiment with data marginal q, and real signed loss has feature Bayes risk minus data Bayes risk at most epsilon times the maximum absolute loss. All four type universes are independent.")),
                Paragraph(Text("The Bayes risk is the real sInf of finiteBayesCost over every row-stochastic randomized decision. Negative losses remain signed. The finite maximum is lossNorm, the real supremum of the finite nonempty set of absolute loss values. Normalization supplies nonemptiness of the data and hypothesis types; the encoder then supplies nonemptiness of the feature type. No support condition is imposed on any entry.")),
                Paragraph(Text("This universal quality condition holds precisely when a single stochastic decoder from Z to X has q-weighted mismatch probability at most epsilon divided by two. The decoder is common to all compatible decision problems. Its error is the sum over x, z and y of q(x) phi(x,z) d(z,y) times the indicator of y different from x.")),
                Paragraph(Text("For the forward transport estimate, compose an optimal data decision with the decoder. Its conditional expected loss lies between minus and plus the maximum absolute loss. Replacing x by a reconstructed y changes this conditional loss by at most twice that maximum, and changes nothing when y equals x. Averaging against the common joint law and using its marginal q gives twice the reconstruction error as the normalized risk bound.")),
                Paragraph(Text("For necessity, relabel the data type into finite hypothesis and action types in their independent universes. Use the identity experiment and the signed loss minus one for correct reconstruction and plus one for a mismatch. Its data Bayes risk is minus one, and its feature risk is twice the minimum mismatch probability minus one. A finite observationwise argmin attains this real minimum, including on null observation fibers. Applying universal quality yields an attaining decoder at half the quality bound.")),
                Paragraph(Text("The source is van Rooyen and Williamson, Le Cam meets LeCun: Deficiency and Generic Feature Learning, arXiv:1402.4884v2, Definition 3 and Theorem 3; Section 2 specifies signed loss normalization and Section 7.5 uses full l1 variational distance. The mismatch indicator and factor two here follow from the signed reconstruction loss directly. The result concerns finite stochastic experiments and makes no measurable infinite-space claim."))),
            DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("finite-real-bayes-cost-expansion"),
                DeclarationHandle.Create("D5/S3/Estimation/DecisionRisk/FixedMarginalGenericFeatures.finite_bayes_cost_expansion"),
                H("Expected cost as a coefficient table"),
                StatementSource.FromAuthor(ExpansionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Here Theta, O and A are arbitrary finite types; p : Theta → ℝ, L : Theta → A → ℝ, T : Theta → O → ℝ and d : O → A → ℝ. The sum indices are theta : Theta, x : O and a : A.")),
                    Paragraph(Text("For arbitrary finite state, observation and action types, the real expected loss equals the sum over observations and actions of the decision entry times its unnormalized posterior loss coefficient. This finite-sum identity is valid for arbitrary real arrays and does not require stochasticity or signs."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("finite-real-bayes-cost-minimizer"),
                DeclarationHandle.Create("D5/S3/Estimation/DecisionRisk/FixedMarginalGenericFeatures.finite_bayes_cost_minimizer"),
                H("Finite real Bayes costs attain a minimum"),
                StatementSource.FromAuthor(MinimumFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Here Theta, O and A are finite types with Nonempty A; p : Theta → ℝ, L : Theta → A → ℝ and T : Theta → O → ℝ. The decisions d, k : FiniteMarkovKernel O A have underlying row-stochastic arrays of type O → A → ℝ, with theta : Theta, x : O and a : A indexing states, observations and actions.")),
                    Paragraph(Text("For arbitrary finite state and observation types and a nonempty finite action type, every real coefficient table has an observationwise minimizing action. The corresponding point-mass decision minimizes finiteBayesCost over all stochastic decisions. The prior, experiment and loss need not have nonnegative entries for this finite linear minimization statement. In a statistical decision problem the prior and experiment satisfy their usual stochastic laws, and signed losses remain allowed."))),
                DescribeRole.Lemma))));


    private static Formula ExpansionFormula()
    {
        Formula prior = F.Id("p"), loss = F.Id("L"), experiment = F.Id("T"), decision = F.Id("d");
        Formula obs = F.Id("x"), act = F.Id("a"), state = F.Id("theta");
        Formula product = Seq(Call("entry", decision, obs, act), Sp, Cdot, Sp,
            Call("sum", state, Seq(Call("entry", prior, state), Sp, Cdot, Sp,
                Call("entry", experiment, state, obs), Sp, Cdot, Sp, Call("entry", loss, state, act))));
        return Disp(Seq(Forall, Sp, prior, Comma, Sp, loss, Comma, Sp, experiment, Comma, Sp, decision,
            Comma, Sp, Call("finiteBayesCost", prior, loss, experiment, decision), Sp, Eq, Sp,
            Call("sum", obs, Call("sum", act, product))));
    }

    private static Formula MinimumFormula()
    {
        Formula state = F.Id("Theta"), obs = F.Id("O"), act = F.Id("A");
        Formula prior = F.Id("p"), loss = F.Id("L"), experiment = F.Id("T");
        Formula d = F.Id("d"), k = F.Id("k");
        return Disp(Seq(Forall, Sp, state, Comma, Sp, obs, Comma, Sp, act, Comma, Sp,
            Call("Fintype", state), Sp, Land, Sp, Call("Fintype", obs), Sp, Land, Sp,
            Call("Fintype", act), Sp, Land, Sp, Call("Nonempty", act), Sp, Rightarrow, Sp,
            Forall, Sp, prior, Comma, Sp, loss, Comma, Sp, experiment, Comma, Sp,
            Exists, Sp, d, Colon, Sp, Call("FiniteMarkovKernel", obs, act), Comma, Sp,
            Forall, Sp, k, Colon, Sp, Call("FiniteMarkovKernel", obs, act), Comma, Sp,
            Call("finiteBayesCost", prior, loss, experiment, d), Sp, Leq, Sp,
            Call("finiteBayesCost", prior, loss, experiment, k)));
    }

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
