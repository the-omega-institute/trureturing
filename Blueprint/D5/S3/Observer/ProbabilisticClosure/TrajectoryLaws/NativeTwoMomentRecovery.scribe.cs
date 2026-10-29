using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws;

internal sealed class NativeTwoMomentRecoveryDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        Formula nu = Call("posterior", F.Id("mu"), F.Id("H"));
        Formula rho = Call("posterior", F.Id("mu"), F.Id("G"));
        Formula statement = All("mu", F.Id("PMFDepth"),
            All("s", F.Id("ActivePhase"), All("t", F.Id("ActivePhase"),
            All("H", Call("PhaseHistory", F.Id("s")),
            All("G", Call("PhaseHistory", F.Id("t")),
                Seq(Call("moment", nu, D(1)), Eq,
                    Call("moment", rho, D(1)), Comma, Sp,
                    Call("moment", nu, D(2)), Eq,
                    Call("moment", rho, D(2)), Rightarrow, nu, Eq, rho))))));
        return DocumentDefinition.Create(ScribeNode.Create(
            "Two response moments determine actual posteriors of one installed prior.",
            H("Two response moments and the same installed prior"), Blocks(
                Paragraph(Text("Depth is the set of positive natural numbers. Its response rate is r_k=fib(k+1)/fib(k+3), with 0<r_k<1. An arbitrary PMF mu on Depth is installed before a run; one hidden depth supplies every Read in that run. PhaseHistory(s) consists of every finite operation list H.h and acquired native state H.c such that run(H.h)=some(H.c) and the state has active fourth-segment phase s. The two histories may have different phases, lengths, counts, rejected pairs, return loops and partial parses.")),
                Paragraph(Text("Write posterior(mu,H) for the original DepthLaw.posterior(mu,H.h,H.c,H.run). If A_H and B_H count every acquired read 0 and read 1 in readLetters(H.h), then this PMF has mass mu(k)*r_k^A_H*(1-r_k)^B_H divided by the sum of these masses. The original positive normalizer makes this definition valid for every actual history. Zero prior masses remain zero, and finite or countably infinite support is allowed. For a depth PMF sigma, moment(sigma,j) is the absolutely convergent sum of sigma(k).toReal*r_k^j.")),
                Describe.Lean(DescribeId.Create("same-prior-two-moments-posterior-unique"),
                    DeclarationHandle.Create("D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeTwoMomentRecovery.same_prior_two_moments_posterior_unique"),
                    H("Posterior uniqueness from the first two response moments"),
                    StatementSource.FromAuthor(Disp(statement)), AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text("Compare two histories under the same mu and exchange their order if necessary so that a=A_H-A_G is nonnegative. On the positive support of mu, the logarithm of their posterior mass ratio is g(x)=a*log(x)+b*log(1-x)+c, where b=B_H-B_G and c=log(Z_G)-log(Z_H). The shared prior cancels. If b is nonnegative, g is concave on (0,1). If b is negative, g is nondecreasing there. Consequently its positive set is a convex open interval.")),
                        Paragraph(Text("If the posteriors differ, their equal total mass gives a depth where the first mass is strictly larger. Thus the positive set of g is nonempty. Let l and u be its infimum and supremum in [0,1]. Openness makes P(x)=(x-l)*(u-x) strictly positive wherever g(x)>0, and interval convexity makes P(x) nonpositive wherever g(x)<=0. Multiplying P(r_k) by the posterior mass difference therefore gives nonnegative terms, with a strictly positive term at the selected supported depth. Unsupported depths contribute zero.")),
                        Paragraph(Text("Each polynomial-weighted sum converges absolutely: expand P into a linear combination of 1, x and x^2, use PMF real summability and 0<=r_k<=1. The equal zeroth, first and second moments make the sum of the nonnegative differences zero, contradicting its strictly positive term. This includes singleton and two-point support and uses no nondegeneracy condition.")),
                        Paragraph(Text("The conclusion is equality of posterior probability laws. It does not identify the sampled depth, equate history counts or phases, provide a stability modulus or grant a finite-cost exact-real measurement. The shared installed prior is part of the theorem; arbitrary unrelated depth PMFs are outside this implication."))),
                    DescribeRole.Theorem))));
    }

    private static Formula Seq(params Formula[] xs) => F.Seq(xs);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, F.Id(name), Colon, type, Comma, Sp, Open, body, Close);
    private static Formula Call(string name, params Formula[] xs)
    {
        var parts = new Formula[xs.Length * 2 - 1];
        for (int i = 0; i < xs.Length; i++)
        {
            parts[i * 2] = xs[i];
            if (i > 0) parts[i * 2 - 1] = Comma;
        }
        return Seq(Operatorname, Grp(F.Id(name)), Open, Seq(parts), Close);
    }
}
