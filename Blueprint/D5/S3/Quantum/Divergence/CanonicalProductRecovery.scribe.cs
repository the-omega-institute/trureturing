using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Divergence;

internal sealed class CanonicalProductRecoveryDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual marginal support cancels singular tensor logarithms in product recovery.",
        H("Canonical Product Recovery"),
        Blocks(Describe.Lean(
            DescribeId.Create("canonical-product-recovery-chain"),
            DeclarationHandle.Create(
                "D5/S3/Quantum/Divergence/CanonicalProductRecovery.canonical_product_recovery_chain"),
            H("Singular joint states satisfy the product-reference chain rule"),
            StatementSource.FromAuthor(ChainFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(
                    Text("The whole chain is a repository-derived composition of known mechanisms, "
                        + "with no novelty claim. The adapted Alex Meiburg Physlib sources and "
                        + "the paper's full-rank boundary are attributed in "),
                    Ref("D5/L/QuantumStates/meiburg2026singulartensorrecovery"),
                    Text(".")),
                Paragraph(Text(
                "In the statement c and d denote gammaA and gammaB; underlyingMatrix is "
                + "CStarMatrix.ofMatrix.symm applied to the state matrix, and infinity is WithTop top. "
                + "The marginal and recovered state use the existing partial trace and product state. "
                + "Only the reference factors are positive definite. The proof contracts actual "
                + "marginal zero directions, retains support projections in the tensor logarithm, "
                + "and cancels them under the same joint-state weighted trace. "
                + "Every divergence in the displayed chain is in its supported finite branch. "
                + "The finite statement does not establish oscillator operator domains or Gibbs traces.")),
                Paragraph(
                    Text("The supported finite Pinsker application in "),
                    Ref("D5/S3/Quantum/Divergence/CanonicalChannelDPI"),
                    Text(" applies to this same joint state and its recovered state. Write mat(tau) = "
                        + "CStarMatrix.ofMatrix.symm tau.1 and D(tau||upsilon) = "
                        + "finiteTraceLogRelativeEntropy tau upsilon, using natural logarithms. "
                        + "For the finite decidable carriers a and b, put rhoA = "
                        + "fromLegacyDensityState(marginalRight(toLegacyDensityState rho)), rhoB = "
                        + "fromLegacyDensityState(marginalLeft(toLegacyDensityState rho)), "
                        + "sigma = fromLegacyDensityState(productState(toLegacyDensityState rhoA, "
                        + "toLegacyDensityState gammaB)), and omega = "
                        + "fromLegacyDensityState(productState(toLegacyDensityState gammaA, "
                        + "toLegacyDensityState gammaB)). Thus sigma is the actual recovered state, "
                        + "not an independently chosen state with the same marginal.")),
                Paragraph(Text(
                    "Use the Pinsker parameters n = a x b and the ordered pair (rho,sigma). "
                        + "DensityState means a positive semidefinite complex matrix of trace one. "
                        + "The chain theorem supplies SupportContained rho sigma, namely "
                        + "ker(mat(sigma)) contained in ker(mat(rho)); it is not an added recovery "
                        + "assumption. The trace-one reference states make a and b nonempty, as in "
                        + "the chain proof, so the finite nonempty carrier condition is satisfied. "
                        + "Only gammaA and gammaB have the positive-definiteness hypotheses of the "
                        + "displayed chain. Neither rho nor rhoA nor sigma is required to be invertible, "
                        + "and rho may be correlated and need not commute with sigma.")),
                Paragraph(Text(
                    "The measurement is formed from this very difference A = mat(rho)-mat(sigma). "
                        + "Choose the Hermitian spectral unitary U and eigenvalues lambda_i of A, "
                        + "and set s(i) = decide(0 < lambda_i). The Kraus rows "
                        + "K_i(y,j) = conjugate(U(j,i)) if y = s(i), and zero otherwise, "
                        + "give a QuantumChannel Phi from a x b to Bool since sum_i K_i* K_i = I. "
                        + "Here * is conjugate transpose. On every complex matrix X, its underlying "
                        + "matrix action is diag_y(sum_i if y = s(i) then (U* X U)(i,i) else 0). "
                        + "Both outputs are the actual Phi.mapState images, and their support "
                        + "inclusion is preserved. If p and q are their respective real true diagonal "
                        + "entries, then the unhalved norm N = traceNorm(A) equals 2(p-q). "
                        + "This uses the same spectral positive mass and zero trace of A; an "
                        + "attaining measurement is not an input hypothesis.")),
                Paragraph(
                    Text("For these outputs, support transfer gives q = 0 implies p = 0 and "
                        + "1-q = 0 implies 1-p = 0. Their trace-log entropy is the Bernoulli "
                        + "KL value k = p log(p/q) + (1-p) log((1-p)/(1-q)), with the supported "
                        + "zero terms interpreted by the totalized logarithm. The diagonal-log "
                        + "calculation and channel data processing described in "),
                    Ref("D5/S3/Quantum/Divergence/CanonicalChannelDPI"),
                    Text(" give k <= D(rho||sigma); "),
                    Ref("D5/S3/TotalVariation/Pinsker.binary_pinsker"),
                    Text(" gives 2(p-q)^2 <= k, including the endpoints. Substituting N = 2(p-q) "
                        + "therefore gives N^2 <= 2 D(rho||sigma) and D(rho||sigma) >= 0. "
                        + "The cap N <= 2 follows from "),
                    Ref("D5/S3/Quantum/Foundation/FiniteTraceDistance.traceDistance_le_one"),
                    Text(" because traceDistance(rho,sigma) = N/2.")),
                Paragraph(Text(
                    "The product-recovery correspondence identifies the entropy in that bound "
                        + "without changing either state: Delta = D(rho||omega)-D(rhoA||gammaA) "
                        + "= D(rho||sigma) = quantumMutualInformation(toLegacyDensityState rho) "
                        + "+ D(rhoB||gammaB). Consequently N^2 <= 2 Delta, Delta >= 0, and N <= 2; "
                        + "equivalently 2 traceDistance(rho,sigma)^2 <= Delta. These are finite "
                        + "consequences of the displayed chain and the supported Pinsker application. "
                        + "The general Pinsker application itself works on every finite decidable "
                        + "nonempty carrier with only the support inclusion on the state pair; it "
                        + "requires no tensor decomposition or faithful reference state. Dimension "
                        + "one, singular states, and zero measurement probabilities remain included.")),
                Paragraph(Text(
                    "These statements concern finite density matrices and a mathematical quantum "
                        + "channel. They do not identify the reference factors with Gibbs states "
                        + "of a common Hamiltonian, realize the channel by Weyl or oscillator "
                        + "dynamics, or supply infinite-dimensional operator domains, thermal "
                        + "trace-class bounds, or a conservation-law implementation. Those physical "
                        + "identifications require their own hypotheses and arguments."))),
            DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var i = 0; i < arguments.Length; i++)
        {
            if (i > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[i]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula All(Formula variable, Formula type, Formula body) =>
        Seq(Forall, Sp, variable, Colon, Sp, type, Comma, Sp, body);

    private static Formula ChainFormula()
    {
        var a = F.Id("a");
        var b = F.Id("b");
        var c = F.Id("c");
        var d = F.Id("d");
        var r = Call("fromLegacyDensityState", Call("marginalRight", Call("toLegacyDensityState", Rho)));
        var t = Call("fromLegacyDensityState", Call("marginalLeft", Call("toLegacyDensityState", Rho)));
        var rec = Call("fromLegacyDensityState", Call("productState", Call("toLegacyDensityState", r), Call("toLegacyDensityState", d)));
        var reference = Call("fromLegacyDensityState", Call("productState", Call("toLegacyDensityState", c), Call("toLegacyDensityState", d)));
        Formula Fin(Formula x, Formula y) => Call("finiteTraceLogRelativeEntropy", x, y);
        Formula Ext(Formula x, Formula y) => Call("extendedQuantumRelativeEntropy", x, y);
        Formula Finite(Formula x, Formula y) => Seq(Ext(x, y), Sp, Neq, Sp, Infty);
        var result = Seq(
            Call("SupportContained", Rho, rec), Sp, Land, Sp,
            Fin(Rho, reference), Sp, Minus, Sp, Fin(r, c), Sp, Eq, Sp, Fin(Rho, rec), Sp, Land, Sp,
            Ext(Rho, reference), Sp, Eq, Sp, Ext(Rho, rec), Sp, Plus, Sp, Ext(r, c), Sp, Land, Sp,
            Finite(Rho, reference), Sp, Land, Sp,
            Finite(Rho, rec), Sp, Land, Sp,
            Finite(r, c), Sp, Land, Sp,
            Finite(t, d), Sp, Land, Sp,
            Fin(Rho, rec), Sp, Eq, Sp,
            Call("quantumMutualInformation", Call("toLegacyDensityState", Rho)), Sp, Plus, Sp, Fin(t, d));
        var conditions = Seq(
            Call("PosDef", Call("underlyingMatrix", c)), Sp, Land, Sp,
            Call("PosDef", Call("underlyingMatrix", d)), Sp, Rightarrow, Sp, Open, result, Close);
        var instances = Seq(
            OpenBracket, Call("Fintype", a), CloseBracket, Sp,
            OpenBracket, Call("DecidableEq", a), CloseBracket, Sp,
            OpenBracket, Call("Fintype", b), CloseBracket, Sp,
            OpenBracket, Call("DecidableEq", b), CloseBracket, Sp,
            All(Rho, Call("DensityState", Seq(a, Sp, Times, Sp, b)),
                All(c, Call("DensityState", a), All(d, Call("DensityState", b), conditions))));
        return Disp(All(a, Seq(Operatorname, Grp(F.Id("Type"))), All(b, Seq(Operatorname, Grp(F.Id("Type"))), instances)));
    }
}
