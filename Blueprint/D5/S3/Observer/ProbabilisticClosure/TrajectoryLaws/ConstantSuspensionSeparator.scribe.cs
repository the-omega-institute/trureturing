using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws;

internal sealed class ConstantSuspensionSeparatorDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/ConstantSuspensionSeparator.";

    public DocumentDefinition Create()
    {
        Formula table = F.Id("R"), s = F.Id("s"), ep = F.Id("ep"), eb = F.Id("eb");
        Formula real = F.Id("Real");
        Formula conclusion = Seq(Fraction(D(1), D(3, 5, 2, 0, 0)), Lt, Call("max", ep, eb));
        Formula assumptions = Seq(Call("inRegularInterval", s), Land,
            Call("constantOnPositiveSupport", table, s), Land,
            D(0), Le, Sp, ep, Land, D(0), Le, Sp, eb, Land,
            Call("completeEndpointBounds", table, ep, eb));
        Formula statement = All("X", F.Id("FiniteType"), All("Y", F.Id("FiniteType"),
            All("R", Call("RegularTable", F.Id("X"), F.Id("Y")),
            All("s", real, All("ep", real, All("eb", real,
                Seq(Open, assumptions, Close, Rightarrow, conclusion)))))));
        return DocumentDefinition.Create(ScribeNode.Create(
            "A finite stationary generator with constant suspended emission cannot simultaneously center both endpoint complete laws within excess one over 35200.",
            H("Constant suspended emission separates complete endpoint laws"), Blocks(
                Paragraph(Text("RegularTable quantifies over arbitrary finite carriers X and Y, nonnegative stochastic update tables B:X to Y and A:Y to X, and probability rows pi and tau satisfying pi B=tau and tau A=pi. The emission probabilities u on X and v on Y lie in the closed interval [1/3,2/5]. No positive-entry, irreducibility, aperiodicity, independence or reversibility condition is imposed.")),
                Paragraph(Text("The output carrier is the existing RawTail=Option(List(Letter)), with Letter=Fin(2), alpha=0 and beta=1. None remains an outcome for noncompletion. Each Q(x) and W(y) is a normalized measure on the entire carrier. The table requires exact same-update recursion for every set E: Q(x)(E) equals u(x) times the indicator that [alpha] belongs to E, plus (1-u(x)) times the B(x,.) average of W evaluated on the beta-prefix preimage of E. The W recursion has immediate [beta] mass 1-v(y), followed by v(y) times the A(y,.) average of Q on the alpha-prefix preimage. Prefixing fixes none. No law is conditioned on completion.")),
                Paragraph(Text("Write Qbar and Wbar for the pi and tau averages. FullTVBound(mean,P,radius) means that the absolute difference between mean(E) and P(E) is at most radius for every complete event E. This is the event-supremum total variation convention. P is the existing Bernoulli stopped-word law, identified with the actual first-completion process by "),
                    Ref("D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FourthSegmentStoppedLaw"), Text(".")),
                Paragraph(Text("In the displayed theorem, ep and eb denote epsilon_p and epsilon_beta, and inRegularInterval(s) means 1/3<=s<=2/5. constantOnPositiveSupport(R,s) means v(y)=s whenever tau(y)>0; values at zero-weight labels need not equal s. completeEndpointBounds requires FullTVBound for Qbar against both p endpoint laws, each with radius 1116529/22781250+epsilon_p, and for Wbar against both beta endpoint laws, each with radius 239/6750+epsilon_beta. The two endpoint alpha probabilities are exactly 1/3 and 2/5.")),
                Describe.Lean(DescribeId.Create("constant-suspension-endpoint-word"),
                    DeclarationHandle.Create(Prefix + "endpoint_p_word"),
                    H("Every pure p type-one word has its exact singleton mass"),
                    StatementSource.FromAuthor(Disp(All("r", F.Id("unitInterval"),
                        All("j", F.Id("Nat"), Seq(
                            Call("realMass", Call("explicitStoppedWordLaw", F.Id("p"), F.Id("r")),
                                Call("some", Call("pWord", F.Id("j"), D(1)))), Eq,
                            Call("endpointTypeOne", F.Id("r"), F.Id("j"))))))),
                    AssessedProvenance.FromRepo(), Blocks(
                        Paragraph(Text("realMass(mu,x)=mu.real({x}). For every r in the full closed unit interval and j natural, endpointTypeOne(r,j)=(1-r)^2[r(1-r)]^j is the mass of the original pWord(j,1)=(beta alpha)^j beta beta. The complete law and its infinite outcome are retained, including r=0 and r=1."))),
                    DescribeRole.Theorem),
                Describe.Lean(DescribeId.Create("constant-suspension-separator"),
                    DeclarationHandle.Create(Prefix + "constant_suspension_separator"),
                    H("Uniform strict separation over every finite regular table"),
                    StatementSource.FromAuthor(Disp(statement)), AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text("The acquired return table C=BA has stationary row pi. With U=1-u, one four-coordinate probability distribution has mass pi(i)C(i,j)C(j,k)C(k,l). Every coordinate has marginal pi. Positive-weight rows have no positive transition into a zero-weight row. This support fact permits the suspended constancy hypothesis to be used exactly where the recursion has positive weight.")),
                        Paragraph(Text("Let m be the common mean of U and M_j the product expectation of the first j coordinates of that one distribution. The full law recursions give Qbar(pWord(j,1))=(1-s)s^j M_(j+1) for j=0,1,2,3, and Wbar(E_beta)=1-s+s(1-s)m for E_beta={[beta],alpha::pWord(0,1)}. The proof first establishes the word recursion for arbitrary natural j and the complete-event identity Wbar=(1-s)delta_beta+s alpha-prefix(Qbar). The suspended event and all four words therefore refer to the same table and the same m.")),
                        Paragraph(Text("The consumed product bounds are M_2<=(19/15)m-2/5, M_3<=(271/225)m-38/75 and M_4>=(4/15)(4m-29/15). They are classical box-envelope instances described in "),
                            Ref("D5/L/Analytic/xu2020polyhedral"), Text(". Their finite proofs use polynomial nonnegativity inside the live derivation; no claim is made that their separate equality cases can be attained together.")),
                        Paragraph(Text("Apply the full endpoint bounds to E_p={pWord(0,1),pWord(1,1),pWord(2,1)}, E_beta, and E_p union {pWord(3,1)}. Exact endpoint masses yield the two midpoint errors and Qbar(pWord(3,1))<=1944/390625+2 epsilon_p. The last bound follows by subtracting the E_p lower bound from the larger event's upper bound. It does not replace the full-law hypothesis by a finite-probe hypothesis.")),
                        Paragraph(Text("Set c=1489/6750. The same-law estimates imply Cp-F(s)<=epsilon_p+5 epsilon_beta and G(s)-1944/390625<=2 epsilon_p+epsilon_beta/5, where Cp=11758471/22781250, F(s)=(1-c/s)(1+19s/15+271s^2/225)-(2/5)s(1-s)(1+19s/15), and G(s)=(4/15)(31s^3/15+29s^4/15-4cs^2). Both functions increase on the regular interval. At s=3679/10000 their respective strict gaps exceed 1/4000 and 1/16000. The two exhaustive sides of this cut imply the displayed strict lower bound."))),
                    DescribeRole.Theorem),
                Paragraph(Text("This theorem concerns the stated regular finite table and its complete laws. It does not establish extraction of such a table from every original history, an isomorphism with the full record and event transcript, or the clipping comparison for arbitrary original emissions. Those bridges are required before an original-observer lower bound of 1/195200 can be asserted. The reduction also makes no resource-preservation claim.")),
                Describe.Lean(DescribeId.Create("endpoint-probability"),
                    DeclarationHandle.Create(Prefix + "endpoint_probability"),
                    H("Normalization of every complete stopped-word law"),
                    StatementSource.FromAuthor(Disp(All("phase", Call("ActivePhase"),
                        All("r", Call("unitInterval"),
                            Call("IsProbabilityMeasure", Call("explicitStoppedWordLaw",
                                F.Id("phase"), F.Id("r"))))))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text("This is the probability normalization of the existing actual fourth-segment pushforward for either active phase and every unit-interval parameter. The infinite return outcome remains in the carrier. The absolute-risk estimates consume this original supplier directly."))),
                    DescribeRole.Theorem))));
    }

    private static Formula Seq(params Formula[] parts) => F.Seq(parts);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Fraction(Formula numerator, Formula denominator) =>
        new Formula.Fraction(numerator, denominator);
}
