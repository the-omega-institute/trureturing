using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.GoldenResource;

internal sealed class DivisorAssociationFiberDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/GoldenResource/DivisorAssociationFiber.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The four-block association quotient has a unique boundary representative and an exact image count for every finite exponent box.",
        H("Divisor Association Fibers"),
        Blocks(
            Paragraph(Text("A source is a quadruple of natural exponents (a,b,c,k). "
                + "The box bounds them by arbitrary natural numbers A,B,C,D, including zero. "
                + "The observation q(a,b,c,k)=(a+k,b,c+k) joins the first and third coordinates "
                + "through the fourth exponent. This describes an association quotient; "
                + "it does not identify the arithmetic block 7 with the product 2 times 5.")),
            Entry("box", "The complete finite source box",
                "The Cartesian product of ranges of lengths A+1, B+1, C+1, D+1.",
                DescribeRole.Definition),
            Entry("q", "Observed association position",
                "The position retains a+k, b, and c+k, so it can forget the original k.",
                DescribeRole.Definition),
            Entry("labels", "The exact hidden-label interval",
                "For position (u,v,w), the labels are the natural integers from "
                + "max(u-A,w-C) to min(D,u,w), provided v is at most B; otherwise "
                + "the interval is empty. Natural subtraction incorporates the zero lower bound.",
                DescribeRole.Definition),
            Entry("fiberEquiv", "Recovering complete sources",
                "The fiber of (u,v,w) is in bijection with its exact label interval. "
                + "A label k restores (u-k,v,w-k,k). Both inverse identities hold, "
                + "including empty and degenerate fibers.", DescribeRole.Definition),
            Entry("boundary", "Unique boundary sources",
                "The retained sources satisfy k=D or a=0 or c=0. Each observed "
                + "position has exactly one such representative: its hidden exponent "
                + "is min(D,u,w). This gives a canonical representative even when "
                + "the fiber contains three or more sources.", DescribeRole.Definition),
            Entry("image_card", "Exact size of the association quotient",
                "For every natural A,B,C,D, the image has "
                + "(B+1)((A+1)(C+1)+D(A+C+1)) positions. The proof constructs "
                + "the unique boundary representative, then removes the interior "
                + "sources with positive a and c and k below D from the complete box. "
                + "For the 5040 exponent box (4,2,1,1), this yields 48 positions "
                + "from 60 sources; the interpretation requires the existing "
                + "prime-exponent divisor language. Counts and geometric positions "
                + "alone supply no Robin inequality or proof of the Riemann hypothesis.",
                DescribeRole.Theorem),
            Paragraph(Text("Application to a specified source generator. On the complete box, "
                + "give a source (a,b,c,k) the arithmetic divisor 2^a 3^b 5^c 7^k. "
                + "For each coordinate i with prime p_i in (2,3,5,7), a legal increment "
                + "has rate 1/p_i and its reverse decrement has rate 1. Suppress an increment "
                + "exactly at that coordinate's upper bound and a decrement exactly at zero. "
                + "These are specified test dynamics, not dynamics deduced from integer maximality. "
                + "The unnormalized weight w(s)=1/(2^a 3^b 5^c 7^k) satisfies "
                + "w(s)/p_i=w(s+e_i) on every legal edge. Normalizing by the sum of all source "
                + "weights gives a full-support reversible law; the coordinate box is connected.")),
            Paragraph(Text("Write y=q(s)=(u,v,w), and put "
                + "v_2=(1,0,0), v_3=(0,1,0), v_5=(0,0,1), v_7=(1,0,1). "
                + "For every observable g on positions the complete pullback-generator law is "
                + "L(g composed with q)(s)=sum_i [1{s_i<cap_i}(g(y+v_i)-g(y))/p_i "
                + "+1{s_i>0}(g(y-v_i)-g(y))], with cap=(A,B,C,D). "
                + "A decremented position is evaluated only on its legal branch. The formula "
                + "holds at every source, including faces, corners and boxes with zero side lengths. "
                + "The guards still use the full source. The existing fiberEquiv reconstructs "
                + "s=(u-k,v,w-k,k), so retaining (y,k) makes every guard and response available. "
                + "The 2,3,5 moves retain k; a 7 increment or decrement changes both endpoint "
                + "coordinates and k by the same signed unit. This transports the specified chain "
                + "with its source memory, without choosing a new conditional source after a jump.")),
            Paragraph(Text("For every A>=1, C>=1, D>=1 and every B>=0, compare "
                + "s=(0,0,C-1,1) and t=(1,0,C,0). Both sources are legal and have "
                + "q(s)=q(t)=(1,0,C). For g(y)=1{y=(1,0,C+1)}, the legal 5 increment "
                + "at s gives L(g composed with q)(s)=1/5. The same increment at t is blocked, "
                + "and none of its other one-coordinate moves reaches the target, giving zero. "
                + "Consequently no position-only operator G can satisfy "
                + "L(g composed with q)=G(g) composed with q on the entire box for all g. "
                + "This is the fiber-constancy obstruction behind "
                + "StrongLumpabilityDescent.strong_lumpability_descent_tfae, applied after finite "
                + "uniformization if stochastic rows are used. It is an application, not a new "
                + "criterion. Failure of this all-source descent alone says nothing about whether "
                + "a particular stationary observed path is Markov.")),
            Paragraph(Text("The stationary path requires a separate compression argument. "
                + "For the complete 5040 divisor box (4,2,1,1), the normalization is Z=403/105 "
                + "and pi(s)=w(s)/Z. Let P be conditional expectation onto q-measurable "
                + "functions in L2(pi), S_t=exp(tL), and T_t=P S_t restricted to range(P). "
                + "Detailed balance makes S_t self-adjoint. The coisometric restriction to "
                + "range(P) supplies F in CompressedPowerDefect.compressed_power_defect, "
                + "with F* the inclusion and F*F=P. Its two-step identity, applied to S_t, "
                + "and orthogonal decomposition give, for every f in range(P) and t>=0, "
                + "<f,(T_(2t)-T_t^2)f>_pi=||(I-P)S_t f||_pi^2. "
                + "Finite matrix differentiation gives the small-time limit "
                + "t^(-2)<f,(T_(2t)-T_t^2)f>_pi -> ||(I-P)Lf||_pi^2.")),
            Paragraph(Text("Take f(s)=1{q(s)=(1,0,2)}. The fiber at (1,0,1) consists "
                + "exactly of the divisors 7 and 10. Its mass is 17/(70Z), and its conditional "
                + "probabilities are 10/17 and 7/17. The generator responses there are 1/5 "
                + "and zero. Thus its conditional-variance contribution is "
                + "[17/(70Z)](10/17)(7/17)(1/5)^2=1/(425Z)=21/34255. "
                + "The other contributions are nonnegative, so the small-time coefficient "
                + "is positive. Under the stationary source law, T_t is the observed lag-t "
                + "conditional transition operator. A stationary Markov path on this "
                + "full-support image would satisfy Chapman-Kolmogorov, contrary to the "
                + "positive defect for sufficiently small positive t. The ordinary finite "
                + "matrix argument therefore excludes stationary Markov behavior for this "
                + "specified observation. This exposition applies the existing algebraic "
                + "supplier; it adds no Lean theorem about continuous-time path laws.")),
            Paragraph(Text("The consumer is the proposed prime/kernel jump term in the "
                + "thermodynamic-action model, which still needs source lifts, height updates "
                + "and cost units. The weighted pushforward in the divisor-association theory "
                + "already supplies the static arithmetic law; stationary weights do not "
                + "supply pathwise closure. The five legal FIB windows remain "
                + "000,100,010,101,001. The label 25 means the joint endpoint word 101, "
                + "with native quantity 2+5=7, not the arithmetic number 25 or two independent "
                + "births. Golden prime classification modulo 5 is a separate arithmetic "
                + "readout and does not select a jump generator.")),
            Paragraph(Text("No correspondence from the original Robin maximizing integers "
                + "to these specified rates has been supplied. The complete test boxes do not "
                + "assert that the original maximizing family admits these perturbations. "
                + "That correspondence must retain "
                + "every prime valuation, every prime-power layer and logarithmic weight, "
                + "the unchanged complete selected set S_X, the original moving-window kernel "
                + "and its endpoints, discrete and geometric costs, and one fixed favorable "
                + "coefficient with the original cofinal quantifiers. For example 5040 and "
                + "5040 times 11 share the four retained valuations while their valuation at "
                + "11, logarithmic size and divisor response differ. Neither a fixed box "
                + "nor its stationary law represents that full domain; these two integers "
                + "are not asserted to be original maximizing witnesses. The source-complete "
                + "Mobius/von-Mangoldt response and the EL.9/EL.14 signed lower bounds "
                + "therefore retain their missing arithmetic transport and favorable-coefficient "
                + "obligations. This test supplies no RH proof.")),
            Paragraph(Text("The source-bound escape audit for image_card remains "
                + "declared_unresolved: IE-C050 ClosedTruthReadout, unclassified_form, "
                + "source.residual_requires_open. Its faithful equivalence, variation, "
                + "sensitivity and actual-observation dependence proofs compile, but "
                + "source-binding validation is unfinished. The exact gap is tracked "
                + "at https://github.com/the-omega-institute/trureturing/issues/15780. "
                + "This audit status does not replace the Lean proof of the cardinality formula.")))));

    private static DocumentBlock Entry(string selector, string title, string prose,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create(selector.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + selector), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
