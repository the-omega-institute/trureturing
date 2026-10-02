using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Linear;

internal sealed class GaussianObservationLawDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Gaussian observation laws and conditional information", H("Gaussian observation laws and conditional information"), Blocks(
            Describe.Lean(DescribeId.Create("gaussian-observation-law"),
                DeclarationHandle.Create("D5/S3/Observer/Linear/GaussianObservationLaw.gaussian_observation_law"),
                H("Posterior disintegration, likelihood and conditional free energy"),
                StatementSource.FromAuthor(TheoremFormula()), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("Let n and p be arbitrary finite index sets, including empty sets, and let M be any real p by n matrix. Let beta be positive and let sigma be any real number with sigma squared positive. Put tau equal to the inverse of sigma squared. The input is the centered Gaussian law on the Euclidean space indexed by n plus p, with block diagonal covariance beta inverse times the identity on n and tau inverse times the identity on p. Its signal and noise coordinate maps have those respective centered Gaussian laws and are independent. Write X and N for these coordinates, Y=MX+N, P for the actual pushforward law of (Y,X), and mu for the actual law of Y.")),
                    Paragraph(Text("Define Q=beta I+tau M transpose M, Sigma=Q inverse, and A=tau Sigma M transpose. The posterior kernel K(y) is the pushforward of the centered Gaussian law with covariance Sigma along x mapped to Ay+x. It disintegrates the same actual joint law: P=mu tensor K. No injectivity or rank condition is imposed on M.")),
                    Paragraph(Text("Let ell be the log likelihood ratio obtained from the actual Radon–Nikodym derivative of P with respect to the product of its marginals. It is integrable under P. The ENNReal Kullback–Leibler divergence I is finite before its conversion to a real number. Its real value is both the integral of ell and one half the difference between the log determinant of beta inverse I and the log determinant of Sigma. The display gives the equivalent observation-Gramian formula.")),
                    Paragraph(Text("For a probability law nu on the signal space, h(nu) is minus the integral under nu of the logarithm of its Radon–Nikodym density with respect to Euclidean volume. Define F(beta,nu) as the expected squared Euclidean norm divided by two, minus beta inverse times h(nu). The mean posterior value of this same functional, minus its prior value, equals beta inverse times I. All laws, densities and likelihoods refer to the same joint experiment. A negative sigma is allowed, and empty determinants equal one.")),
                    Paragraph(Text("The precision is positive definite because its prior term is positive definite and its observation term is positive semidefinite. The innovation X-AY has covariance Sigma and zero cross covariance with Y, hence is independent of Y; reconstructing X gives the posterior disintegration. Integrable products of the scalar standard Gaussian density give the independent Gaussian density, and affine Haar transport with the absolute inverse determinant gives the nondegenerate density. Its Radon–Nikodym ratio yields the actual likelihood. Gaussian second moments prove logarithmic integrability, and integration gives the determinant identity. Mean conditional energy equals prior energy, so the entropy difference also gives the conditional free-energy identity."))), DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula p = F.Id("P"), mu = Mu, k = F.Id("K"), m = F.Id("M");
        Formula covariance = Sigma, prior = Seq(Beta, Caret, Grp(Minus, D(1)), F.Id("I"));
        Formula inverseBeta = Seq(Beta, Caret, Grp(Minus, D(1)));
        Formula transpose = Seq(m, Caret, Grp(F.Id("T")));
        Formula gram = Seq(F.Id("I"), Plus, Frac, Grp(Tau), Grp(Beta), transpose, m);
        Formula posteriorFree = Seq(Int, Call("F", Beta, Call("K", F.Id("y"))), Sp, F.Id("d"), mu);
        Formula free = Seq(posteriorFree, Minus, Call("F", Beta, Seq(Call("N", D(0), prior))), Eq,
            inverseBeta, Call("I", F.Id("X"), F.Id("Y")));
        Formula info = Seq(Call("I", F.Id("X"), F.Id("Y")), Eq,
            Frac, Grp(D(1)), Grp(D(2)), Log, Call("det", gram));
        return Disp(Seq(Begin, Grp(F.Id("gathered")), p, Eq, Call("compProd", mu, k),
            Comma, Sp, Ell, InMacro, Sp, F.Id("L"), Caret, Grp(D(1)), Open, p, Close,
            Comma, Sp, Call("I", F.Id("X"), F.Id("Y")), Lt, Infty,
            RowBreak, Grp(), Call("I", F.Id("X"), F.Id("Y")), Eq,
            Int, Ell, Sp, F.Id("d"), p, Eq,
            Frac, Grp(Log, Call("det", prior), Minus, Log, Call("det", covariance)), Grp(D(2)),
            RowBreak, Grp(), info, RowBreak, Grp(), free, End, Grp(F.Id("gathered"))));
    }

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }
}
