using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Fourier.Asymptotics;

internal sealed class TorusSubgroupHaarContinuityDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Fourier/Asymptotics/TorusSubgroupHaarContinuity.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Normalized Haar probabilities on closed finite-torus subgroups vary weakly continuously with the Hausdorff distance.",
        H("Haar Measures of Converging Torus Subgroups"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("ambient-normalized-subgroup-haar"),
                DeclarationHandle.Create(Module + "ambientHaar"),
                H("The ambient Haar probability"),
                StatementSource.FromAuthor(DefinitionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let I be any finite index type and let T be the product of copies of the unit complex circle indexed by I. "
                        + "For each closed subgroup H of T, use the Borel sigma algebra on H and its Haar measure mH, "
                        + "normalized on the whole compact group H so that mH(H)=1. "
                        + "The inclusion iotaH from H into T is continuous. Its pushforward is the Borel probability muH on the same ambient torus T. "
                        + "Thus the normalization belongs to Haar measure on H, including when H is a proper subgroup of T."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("hausdorff-subgroup-haar-weak-continuity"),
                DeclarationHandle.Create(Module + "result"),
                H("Hausdorff convergence implies weak convergence"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every finite I, every sequence Hn of closed subgroups of T, and every closed subgroup H of T, "
                        + "Hausdorff-distance convergence of Hn to H implies convergence of muHn to muH in the weak topology "
                        + "of Borel probability measures on T. Equivalently, the integrals of every continuous complex-valued "
                        + "function on T converge. No positive dimension, connectedness, ambient density, subgroup containment, "
                        + "or eventual stabilization is required. Finite subgroups, proper subgroups, disconnected subgroups, "
                        + "and the empty product all lie in the quantified domain.")),
                    Paragraph(Text(
                        "Consider a continuous character of T. If it equals one on H, uniform continuity and Hausdorff "
                        + "approximation make it uniformly close to one on Hn, so its Haar integrals tend to one. "
                        + "If it is nontrivial on H, choose a point where its value differs from one. Nearby points of Hn "
                        + "eventually have the same nontriviality property. Translation invariance then forces the "
                        + "character integral to vanish on each such subgroup and on H.")),
                    Paragraph(Text(
                        "Coordinatewise circle homeomorphisms identify these characters with the multivariate Fourier monomials "
                        + "on the additive unit torus. Their complex linear span is dense among continuous functions. "
                        + "Integration against a probability has norm at most one, so convergence extends from that span "
                        + "to every continuous observable. This is weak convergence of the actual inclusion pushforwards."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
    private static Formula ForAll(string name, Formula domain, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll,
            [new Formula.BoundVariable(FormulaIdentifier.Create(name), domain)], body);
    private static Formula Eq(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Torus => new Formula.Power(F.Seq(F.Operatorname, F.Grp(F.Id("Circle"))), F.Id("I"));
    private static Formula Groups => Call("ClosedSubgroups", Torus);
    private static Formula Naturals => F.Seq(F.Mathbb, F.Grp(F.Id("N")));
    private static Formula Mu(Formula subgroup) => F.Seq(F.Mu, F.Underscore, F.Grp(subgroup));

    private static Formula DefinitionFormula()
    {
        Formula h = F.Id("H");
        Formula m = F.Seq(F.Id("m"), F.Underscore, F.Grp(h));
        Formula inclusion = F.Seq(F.Iota, F.Underscore, F.Grp(h));
        Formula pushforward = F.Seq(F.Open, inclusion, F.Close, F.Underscore, F.Grp(F.Star), F.Sp, m);
        Formula normalization = Eq(F.Seq(m, F.Open, h, F.Close), F.D(1));
        return F.Disp(ForAll("I", F.Seq(F.Operatorname, F.Grp(F.Id("FiniteTypes"))), ForAll("H", Groups,
            new Formula.Logic(Eq(Mu(h), pushforward), FormulaLogicOperator.And, normalization))));
    }

    private static Formula TheoremFormula()
    {
        Formula n = F.Id("n");
        Formula h = F.Id("H");
        Formula sequence = F.Id("K");
        Formula kn = F.Seq(sequence, F.Underscore, F.Grp(n));
        Formula limit = F.Seq(F.Lim, F.Underscore, F.Grp(n, F.Sp, F.To, F.Sp, F.Infty),
            F.Sp, Call("HausdorffDistance", kn, h));
        Formula weak = F.Seq(Mu(kn), F.Sp, F.Longrightarrow, F.Sp, Mu(h), F.Quad,
            F.Open, n, F.Sp, F.To, F.Sp, F.Infty, F.Close);
        Formula sequences = F.Seq(Naturals, F.Sp, F.To, F.Sp, Groups);
        return F.Disp(ForAll("I", F.Seq(F.Operatorname, F.Grp(F.Id("FiniteTypes"))), ForAll("K", sequences,
            ForAll("H", Groups, new Formula.Logic(Eq(limit, F.D(0)),
                FormulaLogicOperator.Implies, weak)))));
    }
}
