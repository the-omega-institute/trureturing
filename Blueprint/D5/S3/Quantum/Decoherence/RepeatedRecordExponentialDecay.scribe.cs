using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Decoherence;

internal sealed class RepeatedRecordExponentialDecayDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Quantum/Decoherence/RepeatedRecordExponentialDecay."
            + "repeated_record_exponential_decay";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Repeated finite records contract cross-class coherence at the uniform Gram rate.",
        H("Repeated Record Exponential Decay"),
        Blocks(Describe.Lean(
            DescribeId.Create("repeated-record-exponential-decay"),
            DeclarationHandle.Create(Declaration),
            H("Repeated records converge exponentially to record-class pinching"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The record amplitudes construct both the Gram channel and the class "
                        + "projectors. The projector sum therefore uses the actual equality "
                        + "classes of environment records.")),
                Paragraph(Text(
                    "The first clause is the exact entrywise iterate. The second computes "
                        + "the projector sum, and the final clause is its Frobenius norm "
                        + "contraction under the stated cross-class Gram bound.")),
                Paragraph(Text(
                    "For a repeated-collision application, each system address labels a "
                        + "normalized environment amplitude vector. The Gram coefficient "
                        + "uses the amplitude at the first address times the conjugate "
                        + "amplitude at the second, summed over environment coordinates. "
                        + "The environment_marginal_channel theorem identifies this "
                        + "entry multiplier with tracing out a controlled record. Repeating "
                        + "the same reduced channel can be realized with fresh, initially "
                        + "uncorrelated environment registers and the same recording map. "
                        + "A correlated or reused environment is not covered merely by "
                        + "assigning it the same one-step overlap.")),
                Paragraph(Text(
                    "The error is relative to record-class pinching, in the Frobenius "
                        + "norm, the square root of the sum of squared entry magnitudes. "
                        + "It is bounded by the initial discarded coherence times the "
                        + "uniform cross-class overlap bound raised to the collision count. "
                        + "No positivity or trace-one premise is imposed on the system "
                        + "matrix, so density matrices are included as a special case. "
                        + "The estimate is not stated in trace norm or diamond norm, "
                        + "and does not by itself give a measurement discrimination error.")),
                Paragraph(Text(
                    "The equality classes contain identical amplitude vectors, not rays "
                        + "modulo phase. Distinct normalized vectors differing only by a "
                        + "phase have overlap of unit magnitude, so the strict cross-class "
                        + "bound excludes them. Distinctness alone therefore does not "
                        + "supply the decay hypothesis. Within each equality class the "
                        + "coherence is retained; complete basis dephasing requires "
                        + "singleton classes. Orthogonal distinct classes permit a zero "
                        + "bound and hence exact pinching after any positive collision count.")),
                Paragraph(Text(
                    "This application replaces a demand for exact orthogonality by a "
                        + "quantitative sufficient condition for small residual coherence. "
                        + "Normalization, the overlap bound and the repeated-channel "
                        + "description remain model premises. Their applicability to a "
                        + "particular experiment requires separate physical evidence; "
                        + "the mathematical estimate does not establish those premises.")),
                Paragraph(Text(
                    "A phase-adjusted application groups normalized records by their "
                        + "complex rays. Choose one unit representative for each ray, "
                        + "and repeat that representative at every system address in its "
                        + "class. Each original record is its representative multiplied "
                        + "by a scalar of unit modulus. Equality in Cauchy--Schwarz "
                        + "characterizes proportional unit vectors, so representatives "
                        + "of distinct rays have overlap magnitude strictly below one. "
                        + "Taking the maximum over the finitely many cross-ray pairs "
                        + "gives a uniform strict bound; if there are no such pairs, "
                        + "zero is a valid bound.")),
                Paragraph(Text(
                    "The phase correspondence must also be carried through the "
                        + "dynamics. The original Gram coefficient is the representative "
                        + "Gram coefficient times the first address's phase and the "
                        + "conjugate of the second address's phase. Entrywise "
                        + "multiplication therefore commutes with the associated diagonal "
                        + "phase action. At repetition count N, the original iterate is "
                        + "the representative-channel iterate conjugated by the diagonal "
                        + "matrix of the address phases raised to N. This preserves "
                        + "the original channel; replacing each record by its rank-one "
                        + "density matrix would instead change the Gram coefficient "
                        + "to its squared magnitude and would not give this identity.")),
                Paragraph(Text(
                    "Apply the stated theorem to these representative records. Their "
                        + "equal-vector pinching retains exactly the original same-ray "
                        + "entries. Diagonal conjugation by unit phases preserves the "
                        + "Frobenius norm, so the same decay rate bounds the distance "
                        + "from the original iterate to the conjugated ray pinching. "
                        + "The comparison is a moving coherent-block orbit: within a "
                        + "ray, an entry is multiplied by the two addresses' relative "
                        + "phase to N and need not approach a stationary value. The "
                        + "bound covers arbitrary complex system matrices and N equal "
                        + "to zero; empty finite system carriers are retained.")),
                Paragraph(Text(
                    "In this ray formulation the strict separation follows from finite "
                        + "unit-record geometry, whereas normalization, the specified "
                        + "controlled coupling and repeated application of one reduced "
                        + "channel remain premises of the physical model. The "
                        + "conditional phases belong to the coupling: the individual "
                        + "environment density matrices alone do not determine them. "
                        + "A rotating reference frame consequently needs the coupling "
                        + "or a phase calibration. This application does not establish "
                        + "a correlated-environment evolution, experimental support, "
                        + "or complete stationary dephasing.")),
                Paragraph(Text(
                    "A retained environment can instead be compared with the reset "
                        + "model without defining its true trajectory as channel powers. "
                        + "Let tau_k be actual joint density states evolved by a fixed "
                        + "unitary U, rho_k their system marginals, eta a fixed reference "
                        + "environment state, and R(rho) the system marginal of "
                        + "U(rho tensor eta)U-adjoint. Write D for half the trace norm "
                        + "of a state difference and delta_k = D(tau_k, rho_k tensor eta). "
                        + "Contractivity under the actual unitary and partial-trace "
                        + "channels, together with invariance on tensoring a density "
                        + "state, gives D(rho_N, R^N(rho_0)) at most the sum of delta_k "
                        + "for k from zero to N minus one. The reference eta may be mixed; "
                        + "this estimate neither assumes nor proves small defects.")),
                Paragraph(Text(
                    "For a pure reference basis state a, the controlled-record action "
                        + "can be specified by the actual columns "
                        + "U((i,b),(j,a)) = [j=i] E_i(b). If J embeds a system vector "
                        + "with environment coordinate a and W is the controlled-record "
                        + "isometry, these columns give UJ=W and "
                        + "rho tensor |a><a| = J rho J-adjoint. The "
                        + "environment_marginal_channel identity therefore derives "
                        + "R=recordChannel from the coupling. The (j,a) diagonal entry "
                        + "of U-adjoint U=I also gives sum_b |E_j(b)|^2=1, so record "
                        + "normalization follows from these unitary columns rather "
                        + "than adding an independent premise. Under the remaining "
                        + "strict cross-class overlap premise, apply the "
                        + "frozen estimate to R^N(rho_0). Since the Frobenius norm is "
                        + "at most the trace norm, the actual system's Frobenius error "
                        + "relative to record-class pinching is at most twice the sum "
                        + "of delta_k plus q^N times the initial pinching error. The "
                        + "factor two comes from the half-trace-norm convention for D. "
                        + "This is an application of the existing estimates, not an "
                        + "additional clause of the displayed frozen declaration.")),
                Paragraph(Text(
                    "Exact purity of the actual environment marginal has a stronger "
                        + "consequence than stationarity of a mixed marginal. For a "
                        + "finite positive semidefinite joint matrix X, suppose its "
                        + "actual environment marginal Tr_S X is p=|a><a|. Every "
                        + "environment diagonal outside a is zero. Since it is a sum "
                        + "of nonnegative joint diagonal entries, each summand is zero. "
                        + "The bound CartesianVariance.psd_entry_bound then forces "
                        + "the corresponding joint rows and columns to vanish. The "
                        + "remaining a block is exactly the actual system marginal "
                        + "Tr_E X, giving X=(Tr_E X) tensor p. Here Tr_S and Tr_E "
                        + "are PartialTraceMutualInformation.partialTraceLeft and "
                        + "partialTraceRight, respectively. No global pure-state "
                        + "premise or separately assumed product condition is needed.")),
                Paragraph(Text(
                    "Consequently, fix a finite horizon N and evolve the actual "
                        + "joint states by tau_(k+1)=U tau_k U-adjoint. If tau_k is "
                        + "positive semidefinite and Tr_S tau_k is exactly the same "
                        + "p at every input k<N, the factorization gives "
                        + "tau_k=rho_k tensor p at those inputs. With the reset map "
                        + "R_p(rho)=Tr_E(U(rho tensor p)U-adjoint), induction yields "
                        + "rho_N=R_p^N(rho_0), including N=0. Thus exact purity at "
                        + "the required inputs removes the independent product "
                        + "assumption. The condition k<N does not include the final "
                        + "output: N=1 still permits recording and decoherence there. "
                        + "Preserving p across a transition requires purity at both "
                        + "endpoints and is a stronger condition.")),
                Paragraph(Text(
                    "For that stronger condition, use the same finite controlled "
                        + "columns and pure reference p=|a><a| specified above. Let "
                        + "rho be a positive semidefinite, trace-one system input "
                        + "and S={i:rho_ii>0} its population support in the control "
                        + "basis. An actual input environment marginal p already "
                        + "implies the product input rho tensor p by factorization. "
                        + "If the actual output environment marginal is also p, "
                        + "its diagonal at b distinct from a gives "
                        + "sum_i rho_ii |E_i(b)|^2=0. Every summand is nonnegative, "
                        + "so E_i(b)=0 for i in S. Record normalization then gives "
                        + "E_i=u_i|a> with u_i=E_i(a) and |u_i|=1 on S.")),
                Paragraph(Text(
                    "Thus recordGram E i j=u_i conjugate(u_j) has magnitude one "
                        + "for i,j in S. The environment_marginal_channel identity "
                        + "makes the output entry this coefficient times rho_ij. "
                        + "CartesianVariance.psd_entry_bound also gives "
                        + "|rho_ij|^2<=rho_ii rho_jj, so a zero population forces "
                        + "its entire row and column to vanish. Consequently every "
                        + "entry magnitude |rho_ij| is preserved, including entries "
                        + "outside S. A changing phase or real quadrature is not "
                        + "loss of coherence magnitude. No pure system or joint "
                        + "state, full rank or full population support is assumed; "
                        + "a rank-one superposition can have full population support.")),
                Paragraph(Text(
                    "This restriction is sensitive to the input's population "
                        + "support. If S is the whole system carrier, R_p is "
                        + "conjugation by the diagonal unitary with entries u_i "
                        + "on every system matrix. Deficient support leaves unused "
                        + "record columns unconstrained by this trajectory and "
                        + "does not make the entire reset channel unitary. For "
                        + "example, E_0=E_1=|a> and E_2=|b> with b orthogonal "
                        + "to a preserve a coherent input supported on 0,1 while "
                        + "dephasing coherences involving address 2 on other inputs.")),
                Paragraph(Text(
                    "With the same fixed controlled U, a transition preserving p "
                        + "fixes U(|i> tensor |a>)=u_i(|i> tensor |a>) for i in S. "
                        + "Their span is therefore invariant, populations stay "
                        + "fixed, and later joint steps retain environment p and "
                        + "system entries rho_ij(k)=(u_i conjugate(u_j))^k rho_ij(0) "
                        + "on S. This conclusion needs no new endpoint assumption "
                        + "for those later steps of that fixed U. Changing couplings "
                        + "require the corresponding controlled-column and "
                        + "pure-marginal preservation conditions at each transition. "
                        + "The conclusion does not cover unobserved intermediate "
                        + "times or arbitrary unitaries. For example a system "
                        + "Hadamard tensor environment identity takes the plus "
                        + "state to a basis state while preserving environment p; "
                        + "it rotates basis coherence without dephasing.")),
                Paragraph(Text(
                    "If the displayed literal-vector strict overlap premise is "
                        + "also imposed, two distinct occupied records would have "
                        + "Gram magnitude one and hence could not satisfy q<1. "
                        + "All occupied records must then actually equal, R_p fixes "
                        + "this input, and its record-class pinching error is zero. "
                        + "In the ray formulation the occupied records share one "
                        + "ray and only the coherent phase orbit remains. These "
                        + "are applications of the existing finite-matrix results, "
                        + "not additional frozen clauses. Actual complete "
                        + "environment purity differs from pure conditional records, "
                        + "global joint purity, a pure comparison reference, mixed "
                        + "stationarity and approximate purity. None of those "
                        + "substitutes establishes the stated endpoint premise. "
                        + "The application asserts neither physical validation, "
                        + "mathematical novelty nor an infinite-dimensional result.")),
                Paragraph(Text(
                    "A one-step application compares system coherence loss with "
                        + "the purity of the actual output environment, without "
                        + "choosing a comparison ray. In finite system and environment "
                        + "dimensions d,e, let rho be positive semidefinite with trace "
                        + "one and let each E_i be normalized. Set "
                        + "W((i,b),j)=[j=i] E_i(b), X=W rho W-adjoint, "
                        + "sigma_E=Tr_S X and rho'=Tr_E X. These are both actual "
                        + "marginals of the same recorded joint state. Write "
                        + "p_i=rho_ii and G_ij=sum_b E_i(b) conjugate(E_j(b)), "
                        + "the recordGram convention used above. Normalization "
                        + "makes W an isometry. To identify X with an actual "
                        + "controlled-unitary output, the input must be the product "
                        + "rho tensor |a><a| and U must have the specified columns "
                        + "UJ=W. The coefficient-one bound below is not asserted "
                        + "for a mixed initial environment.")),
                Paragraph(Text(
                    "Define F2(A)=sum_ij |A_ij|^2. The environment marginal has "
                        + "entries sigma_E(b,c)=sum_i p_i E_i(b) conjugate(E_i(c)), "
                        + "so F2(sigma_E)=sum_ij p_i p_j |G_ij|^2. For example, "
                        + "put the record vectors in the columns of B. Then "
                        + "sigma_E=B diag(p) B-adjoint and "
                        + "(B-adjoint B)_ij=conjugate(G_ij); cyclicity of trace "
                        + "gives this identity. The environment_marginal_channel "
                        + "identity supplies rho'_ij=G_ij rho_ij. Thus, with "
                        + "L=F2(rho)-F2(rho') and Delta=1-F2(sigma_E), "
                        + "L=sum_ij |rho_ij|^2(1-|G_ij|^2) and "
                        + "Delta=sum_ij p_i p_j(1-|G_ij|^2). Record normalization "
                        + "gives G_ii=1 and |G_ij|<=1. Applying "
                        + "CartesianVariance.psd_entry_bound to rho gives "
                        + "|rho_ij|^2<=p_i p_j, so termwise comparison yields "
                        + "0<=L<=Delta. No positive lower bound on the populations "
                        + "is required, and zero populations cause no exception.")),
                Paragraph(Text(
                    "The input and both marginals are Hermitian density matrices, "
                        + "so F2(A)=Tr(A^2) for each of them. Hence L is the system "
                        + "purity loss and Delta is the output environment's linear "
                        + "entropy. Since the diagonal entries are unchanged, L is "
                        + "also C2(rho)-C2(rho'), where "
                        + "C2(A)=sum_(i distinct from j) |A_ij|^2 is the squared "
                        + "off-diagonal Frobenius coherence. It is not "
                        + "F2(rho-rho'). For a pure system input, "
                        + "|rho_ij|^2=p_i p_j, so L=Delta. For a maximally mixed "
                        + "qubit with orthogonal records, rho'=rho, L=0 and "
                        + "Delta=1/2; equality therefore does not extend to all "
                        + "mixed system inputs.")),
                Paragraph(Text(
                    "If the actual output environment has purity one, Delta=0. "
                        + "Every occupied pair then has |G_ij|=1, so equality in "
                        + "Cauchy--Schwarz makes all occupied records share one "
                        + "unit output ray: E_i=u_i e with |u_i|=1 on the "
                        + "population support. The system undergoes only the "
                        + "corresponding diagonal phase action on this input. "
                        + "The output ray e need not be the input reference |a>, "
                        + "and rho' need not equal rho. In particular, records "
                        + "E_0=e and E_1=-e take the plus state to the minus "
                        + "state while Delta=0. Their half-trace-norm distance "
                        + "is one, so this coherence-magnitude comparison does "
                        + "not bound the state trace distance by Delta.")),
                Paragraph(Text(
                    "One pure output at a different ray also gives no future "
                        + "retention conclusion for a fixed U. On an environment "
                        + "basis 0,1,2, let U be controlled by a qubit: V_0 swaps "
                        + "0 and 1 and fixes 2, while V_1 cycles 0 to 1 to 2 to 0. "
                        + "From environment |0>, the first records are both |1>; "
                        + "on the second contact they are |0> and |2>. For a plus "
                        + "system input the first environment output is pure, "
                        + "but the second contact removes its system coherence. "
                        + "This differs from the earlier two-endpoint application "
                        + "that preserves the same reference p and hence an "
                        + "invariant occupied subspace.")),
                Paragraph(Text(
                    "Small Delta therefore controls the input-dependent loss "
                        + "of squared coherence magnitude. Its population-weighted "
                        + "sum does not uniformly control every relative pair loss "
                        + "1-|G_ij|^2 when populations can be arbitrarily small. "
                        + "This one-step application supplies no reset "
                        + "identification, monotonic retained-environment "
                        + "trajectory, uniform-in-time estimate or exponential "
                        + "decay law. It makes no mathematical novelty or "
                        + "empirical-support claim.")),
                Paragraph(Text(
                    "A separate near-purity comparison controls the actual defect to a specified "
                        + "pure reference. For any finite positive semidefinite joint "
                        + "X with Tr X=1, fix an environment basis point a and set "
                        + "p=|a><a|, sigma=Tr_E X and "
                        + "epsilon=1-Re((Tr_S X)[a,a]). This leakage lies between zero "
                        + "and one. With the same half-trace-norm convention, "
                        + "D(X,sigma tensor p) is at most "
                        + "sqrt(epsilon)+epsilon/2, independently of both dimensions. "
                        + "The comparison uses the actual system marginal sigma, "
                        + "without assuming a product joint state.")),
                Paragraph(Text(
                    "To obtain the bound, put P=I tensor p, S=sqrt(X) and C=P S. "
                        + "The identity GNSMatrix.gns_matrix_identity gives "
                        + "||S||_F=1, ||C||_F<=1 and ||S-C||_F=sqrt(epsilon). "
                        + "Expand X-PXP as (S-C)S-adjoint plus "
                        + "C(S-adjoint-C-adjoint). The trace-norm triangle inequality "
                        + "and TavakoliMorelliIncompleteEAM.traceNorm_mul_le_hsSq, "
                        + "expressed in Frobenius norms through "
                        + "HilbertSchmidtTraceStability.entryNormSq_eq_hs_sq, bound "
                        + "its trace norm by 2 sqrt(epsilon).")),
                Paragraph(Text(
                    "Let A0 be the a block of X. Then PXP=A0 tensor p, while "
                        + "sigma-A0 is the sum of the other positive semidefinite "
                        + "diagonal environment blocks and has trace epsilon. "
                        + "FiniteTraceDistance.traceNorm_of_posSemidef and the "
                        + "partial-trace and tensor-trace identities therefore give "
                        + "traceNorm((sigma-A0) tensor p)=epsilon. Applying the "
                        + "triangle inequality to X-sigma tensor p through PXP "
                        + "and dividing by two gives the asserted defect bound. "
                        + "This is an application of existing positivity, trace "
                        + "and norm results, with no additional frozen clause.")),
                Paragraph(Text(
                    "For an actual trajectory, define epsilon_k from Tr_S tau_k "
                        + "using this same fixed a. The earlier defect accumulation "
                        + "estimate then gives D(rho_N,R_p^N(rho_0)) at most the "
                        + "sum over k<N of sqrt(epsilon_k)+epsilon_k/2. Only when "
                        + "this R_p is the controlled-record channel identified "
                        + "above can that sum also supply its actual-trajectory "
                        + "pinching error budget. This bound does not identify a "
                        + "reset map R_eta specified with a mixed reference eta "
                        + "with R_p; replacing eta by p requires a separate comparison of "
                        + "the reset maps and their iterates. The bound is a "
                        + "one-step estimate whose trajectory application accumulates "
                        + "over the finite horizon. It proves neither physical "
                        + "smallness of epsilon_k nor accuracy uniform in time.")),
                Paragraph(Text(
                    "Stationarity of an environment marginal is not a bound on "
                        + "the accumulated joint-state defects. For system-controlled X on two qubits, "
                        + "start the system in the plus state and take "
                        + "eta_r=(I+rX)/2 with 0<=r<=1. The actual environment marginal "
                        + "stays eta_r, while the joint unitary has period two and the "
                        + "reset channel multiplies system off-diagonal entries by r. "
                        + "At step 2m, direct matrix calculation gives trace distance "
                        + "(1-r^(2m))/2 between the actual system and the reset iterate. "
                        + "The environment is only (1-r)/2 from the pure plus state. "
                        + "For example r=0.99 gives impurity 0.005 but step-100 "
                        + "discrepancy about 0.316984. At r=1 the discrepancy is zero; "
                        + "the example does not refute an exactly pure unchanged "
                        + "environment premise. It shows why a fixed-step approximation "
                        + "and an estimate uniform in time are separate obligations. "
                        + "Control of the required joint correlations, physical "
                        + "identification of the coupling and experimental support "
                        + "remain outside these mathematical applications."))),
            DescribeRole.Theorem))));

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula Entry(Formula matrix, Formula row, Formula column) =>
        Call("entry", matrix, row, column);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula LessOrEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);

    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);

    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula Power(Formula value, Formula exponent) =>
        new Formula.Power(value, exponent);

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula TheoremFormula()
    {
        Formula d = F.Id("d"), e = F.Id("e"), n = F.Id("N");
        Formula i = F.Id("i"), j = F.Id("j"), a = F.Id("a");
        Formula record = F.Id("E"), q = F.Id("q"), rho = Rho;
        Formula label = F.Id("l"), projector = F.Id("P"), pinching = F.Id("Pch");
        Formula nat = F.Id("Nat"), real = Seq(Mathbb, Grp(F.Id("R")));
        Formula complex = Seq(Mathbb, Grp(F.Id("C")));
        Formula system = Call("Fin", d), environment = Call("Fin", e);
        Formula matrix = Call("Matrix", system, system, complex);
        Formula recordType = Arrow(system, Arrow(environment, complex));
        Formula recordAtI = Apply(record, i), recordAtJ = Apply(record, j);
        Formula gram = Call("recordGram", record, i, j);
        Formula channelIterate = Call("iterate", Call("recordChannel", record), n, rho);
        Formula normalized = Equal(
            Seq(Sum, Underscore, Grp(a, Sp, InMacro, Sp, environment), Sp,
                Multiply(
                    new Formula.Norm(Apply(recordAtI, a)),
                    new Formula.Norm(Apply(recordAtI, a)))),
            D(1));
        Formula normalization = new Formula.BindMany(
            FormulaQuantifier.ForAll, [Bound("i", system)], normalized);
        Formula qType = Call("Ico", D(0), D(1));
        Formula distinctRecords = new Formula.Relation(
            recordAtI, FormulaRelationOperator.NotEqual, recordAtJ);
        Formula gramBound = Seq(
            distinctRecords, Sp, Rightarrow, Sp,
            LessOrEqual(new Formula.Norm(gram), q));
        Formula allGramBounds = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("i", system), Bound("j", system)], gramBound);
        Formula projectorAt = Call("recordClassProjector", record, label);
        Formula pinchingAtRho = Apply(pinching, rho);
        Formula pinchingDefinition = Seq(
            Operatorname, Grp(F.Id("let")), Sp,
            pinching, Colon, Sp, Arrow(matrix, matrix), Comma, Sp,
            rho, Mapsto, Sp,
            Seq(Sum, Underscore, Grp(label, Sp, InMacro, Sp,
                Call("range", record)), Sp,
                Multiply(Multiply(projectorAt, rho), projectorAt)), Semi, Sp);
        Formula iterateClause = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("N", nat), Bound("rho", matrix), Bound("i", system), Bound("j", system)],
            Equal(
                Entry(channelIterate, i, j),
                Multiply(Power(gram, Seq(n)), Entry(rho, i, j))));
        Formula pinchingEntry = Equal(
            Entry(pinchingAtRho, i, j),
            Call("ite", Equal(recordAtI, recordAtJ), Entry(rho, i, j), D(0)));
        Formula pinchingClause = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("rho", matrix), Bound("i", system), Bound("j", system)],
            pinchingEntry);
        Formula contraction = LessOrEqual(
            new Formula.Norm(Subtract(channelIterate, pinchingAtRho)),
            Multiply(Power(Seq(q), Seq(n)),
                new Formula.Norm(Subtract(rho, pinchingAtRho))));
        Formula contractionClause = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("N", nat), Bound("rho", matrix)], contraction);

        Formula conclusion = Seq(
            pinchingDefinition,
            And(iterateClause, And(pinchingClause, contractionClause)));

        return Disp(Seq(
            Forall, Sp, d, Colon, Sp, nat, Comma, Sp,
            e, Colon, Sp, nat, Comma, RowBreak, Grp(),
            record, Colon, Sp, recordType, Comma, RowBreak, Grp(),
            normalization, Comma, RowBreak, Grp(),
            q, Colon, Sp, qType, Comma, RowBreak, Grp(),
            Grp(allGramBounds), Sp, Rightarrow, RowBreak, Grp(),
            conclusion, Dot));
    }
}
