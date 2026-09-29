using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Fourier;

internal sealed class GaussianIsometryDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every complete real Hilbert space has an isometric realization by jointly centered Gaussian random variables on one product probability space.",
        H("A common Gaussian realization of a real Hilbert space"),
        Blocks(Describe.Lean(
            DescribeId.Create("hilbert-gaussian-isometry"),
            DeclarationHandle.Create("D5/S3/Fourier/GaussianIsometry.exists_gaussian_isometry"),
            H("The Gaussian isometry"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("Let H be any complete real inner product space. There are an index type of the same universe as H and a real linear isometry W from H into L2 of the product of standard real Gaussian measures indexed by that type. No separability, finite dimension, or nonzero dimension is required.")),
                Paragraph(Text("For every h, the representative of W(h) has centered Gaussian law with variance equal to the squared norm of h. The whole family is a Gaussian process: every finite subfamily has a joint Gaussian law. For all h and k its covariance is their real inner product. All these statements use the same product measure and the same map W. Linearity holds in L2, so identities between representatives hold almost everywhere for each fixed finite relation.")),
                Paragraph(Text("Choose a Hilbert basis and use the independent coordinate variables of the product measure as an orthonormal family in L2. The orthogonal series isometry extends their finite linear combinations to the entire Hilbert space. The centered Gaussian law with variance equal to squared norm is closed under L2 limits, as follows from convergence in distribution and characteristic functions. Finite Gaussian sums therefore give the law of every image vector. Linearity then gives joint Gaussianity, and the L2 inner product gives the covariance.")),
                Paragraph(Text("For a real L2 space with a control measure, this is the common isonormal process acting on all square-integrable real test functions. For a finite control measure, applying that one map to cosine and negative sine tests defines the two components of a complex Fourier coordinate. The theorem concerns L2 random variables and their joint laws; continuous sample versions, differentiability, and convergence of a prescribed data sequence require further results."))),
            DescribeRole.Theorem))));

    private static Formula R => F.Seq(F.Mathbb, F.Grp(F.Id("R")));
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll,
            [new Formula.BoundVariable(FormulaIdentifier.Create(name), domain)], body);
    private static Formula Exists(string name, Formula domain, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.Exists,
            [new Formula.BoundVariable(FormulaIdentifier.Create(name), domain)], body);
    private static Formula At(Formula f, Formula x) => F.Seq(f, F.Open, x, F.Close);
    private static Formula Lambda(string name, Formula domain, Formula body) =>
        F.Seq(F.Open, F.Id(name), F.Colon, domain, F.Mapsto, F.Sp, body, F.Close);

    private static Formula TheoremFormula()
    {
        Formula u = F.Id("u"), hSpace = F.Id("H"), index = F.Id("iota"),
            w = F.Id("W"), h = F.Id("h"), k = F.Id("k"), omega = F.Id("omega");
        Formula type = Call("Type", u);
        Formula p = Call("infinitePi", Lambda("i", index, Call("gaussianReal", F.D(0), F.D(1))));
        Formula sample = Call("Function", index, R);
        Formula readH = Lambda("omega", sample, At(Call("representative", At(w, h)), omega));
        Formula readK = Lambda("omega", sample, At(Call("representative", At(w, k)), omega));
        Formula laws = All("h", hSpace, Call("HasLaw", readH,
            Call("gaussianReal", F.D(0), Call("toNNReal", new Formula.Power(Call("norm", h), F.D(2)))), p));
        Formula joint = Call("IsGaussianProcess", Lambda("h", hSpace, readH), p);
        Formula covariance = All("h", hSpace, All("k", hSpace,
            new Formula.Relation(Call("covariance", readH, readK, p), FormulaRelationOperator.Equal,
                Call("inner", h, k))));
        Formula conclusion = Exists("iota", type,
            Exists("W", Call("LinearIsometry", R, hSpace, Call("Lp", R, F.D(2), p)),
                And(laws, And(joint, covariance))));
        Formula hypotheses = And(Call("NormedAddCommGroup", hSpace),
            And(Call("InnerProductSpace", R, hSpace), Call("CompleteSpace", hSpace)));
        return F.Disp(All("u", Call("UniverseLevel"), All("H", type,
            new Formula.Logic(hypotheses, FormulaLogicOperator.Implies, conclusion))));
    }
}
