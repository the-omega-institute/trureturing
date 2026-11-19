using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Information;

internal sealed class CorrelatedGibbsEnergyIdentityDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Information/CorrelatedGibbsEnergyIdentity.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Initially correlated states with thermal marginals obey an exact energy-information balance.",
        H("Energy and Information with Initial Correlations"),
        Blocks(
            Paragraph(Text(
                "A and B are arbitrary finite nonempty subsystem index types. HA and HB are "
                + "Hermitian physical Hamiltonians, and betaA and betaB are real inverse temperatures. "
                + "thermalState(H,beta) is the existing Gibbs state exp(-beta H)/Tr(exp(-beta H)); "
                + "E(H,rho) denotes meanEnergy(H,rho) = Re Tr(H rho). S is von Neumann entropy "
                + "and D is quantum relative entropy, with natural logarithms. rhoA and rhoB "
                + "are the actual partial traces marginalRight(rho) and marginalLeft(rho). "
                + "The primed joint state is U rho U*, with U a joint unitary, and its primed "
                + "marginals are obtained by the same partial traces.")),
            Result("local-gibbs-difference", "gibbs_relative_entropy_energy_difference",
                "The local thermal identity",
                "For every initial density equal to gamma = thermalState(H,beta) and every final "
                + "density sigma, the Gibbs variational identity at sigma and gamma has the same "
                + "log partition function. Subtraction cancels it, and D(gamma,gamma) vanishes. "
                + "The final state may be singular and need not commute with H.",
                Disp(Seq(Forall, Sp, F.Id("H"), Comma, Sp, F.Id("beta"), Comma, Sp,
                    F.Id("sigma"), Comma, Sp,
                    Call("D", F.Id("sigma"), F.Id("gamma")), Sp, Eq, Sp,
                    F.Id("beta"), Sp, Cdot, Sp, Open,
                    Call("E", F.Id("H"), F.Id("sigma")), Sp, Minus, Sp,
                    Call("E", F.Id("H"), F.Id("gamma")), Close, Sp, Minus, Sp, Open,
                    Call("S", F.Id("sigma")), Sp, Minus, Sp, Call("S", F.Id("gamma")), Close))),
            Describe.Lean(
                DescribeId.Create("joint-entropy"),
                DeclarationHandle.Create(Module + "von_neumann_entropy_unitary"),
                H("Joint entropy is conserved"),
                StatementSource.FromAuthor(Disp(Seq(Forall, Sp, Rho, Comma, Sp, F.Id("U"),
                    Comma, Sp, Call("S", Call("unitaryConjugateState", F.Id("U"), Rho)),
                    Sp, Eq, Sp, Call("S", Rho)))),
                AssessedProvenance.FromLiterature(
                        LibraryNoteRef.Create("D5/L/Quantum/watrous2018entropicidentities")),
                Blocks(Paragraph(Text(
                    "For every density state and every unitary U, the existing entropy-production "
                    + "identity applied at U and at the identity matrix yields the same pinching "
                    + "relative entropy. Subtracting those equalities gives entropy conservation, "
                    + "including singular states. This argument uses the public entropy theorem."))),
                DescribeRole.Lemma),
            Result("marginal-entropy-information", "marginal_entropy_change_eq_mutual_information_change",
                "Marginal entropy changes measure correlation changes",
                "For every joint density and joint unitary, I(rho) = S(rhoA) + S(rhoB) - S(rho). "
                + "Subtracting initial from final mutual information cancels total entropy. "
                + "Delta always means final minus initial; the initial correlation term remains.",
                Disp(Seq(Forall, Sp, Rho, Comma, Sp, F.Id("U"), Comma, Sp,
                    F.Id("DeltaSA"), Sp, Plus, Sp, F.Id("DeltaSB"), Sp, Eq, Sp,
                    Call("I", F.Id("rhoPrime")), Sp, Minus, Sp, Call("I", Rho)))),
            Result("energy-information-balance", "energy_information_identity",
                "Energy-information identity with correlated initial states",
                "Assume exactly rhoA = thermalState(HA,betaA) and rhoB = thermalState(HB,betaB). "
                + "The initial joint state can have correlations. Add the two local thermal "
                + "identities and substitute the marginal entropy relation. No energy conservation "
                + "assumption is needed for this weighted identity.",
                Disp(Seq(Forall, Sp, Rho, Comma, Sp, F.Id("U"), Comma, Sp,
                    F.Id("rhoA"), Sp, Eq, Sp, F.Id("gammaA"), Sp, Land, Sp,
                    F.Id("rhoB"), Sp, Eq, Sp, F.Id("gammaB"), Sp, Implies, Sp,
                    F.Id("betaA"), Sp, Cdot, Sp, F.Id("DeltaEA"), Sp, Plus, Sp,
                    F.Id("betaB"), Sp, Cdot, Sp, F.Id("DeltaEB"), Sp, Eq, Sp,
                    Call("D", F.Id("rhoAPrime"), F.Id("gammaA")), Sp, Plus, Sp,
                    Call("D", F.Id("rhoBPrime"), F.Id("gammaB")), Sp, Plus, Sp,
                    Call("I", F.Id("rhoPrime")), Sp, Minus, Sp, Call("I", Rho)))),
            new DocumentBlock.Section(H("Product initialization and the Landauer application"), Blocks(
            Paragraph(Text(
                "Let A and B be arbitrary finite nonempty system and bath index types. Fix a "
                + "Hermitian bath Hamiltonian H, a real beta, and gamma = thermalState(H,beta). "
                + "Choose any density sigma on A, including a singular one, and the actual initial "
                + "state rho = productState(sigma,gamma). For any joint unitary U, set rhoPrime = "
                + "unitaryConjugateState(U,rho), sigmaPrime = marginalRight(rhoPrime), and "
                + "gammaPrime = marginalLeft(rhoPrime). Define Q = E(H,gammaPrime) - E(H,gamma) "
                + "using this same H. The product-marginal and product-mutual-information results "
                + "in PartialTraceMutualInformation give the initial marginals sigma and gamma "
                + "and I(rho) = 0. Substituting in the marginal entropy-change identity gives "
                + "S(sigmaPrime) - S(sigma) + S(gammaPrime) - S(gamma) = I(rhoPrime). "
                + "The local Gibbs difference above gives D(gammaPrime,gamma) = beta Q - "
                + "S(gammaPrime) + S(gamma). Eliminating the bath entropy change yields:")),
            new DocumentBlock.DisplayFormula(Disp(Seq(F.Id("beta"), Sp, Cdot, Sp, F.Id("Q"), Sp, Eq, Sp,
                Call("S", F.Id("sigma")), Sp, Minus, Sp, Call("S", F.Id("sigmaPrime")),
                Sp, Plus, Sp, Call("I", F.Id("rhoPrime")), Sp, Plus, Sp,
                Call("D", F.Id("gammaPrime"), F.Id("gamma"))))),
            Paragraph(Text(
                "Both remainders are nonnegative on these same actual states. For mutual "
                + "information, apply StrongSubadditivity.strong_subadditivity after inserting "
                + "a singleton middle index: relabel A times B as A times (Unit times B), whose "
                + "middle entropy is zero. The two remaining partial traces are exactly the "
                + "original marginals up to singleton relabeling. The entropy_toMState and "
                + "entropy_relabelState bridges preserve the matrix and natural-log entropy; "
                + "no marginal invertibility or additional support premise is assumed. For "
                + "the bath relative entropy, gibbs_state_posDef makes gamma positive definite, "
                + "so every kernel-support obligation is automatic. Each positive trace-one "
                + "matrix is bounded above by the identity. Applying "
                + "SpectralCeilingRelativeEntropy.actual_matrix_spectral_ceiling_strong_klein "
                + "at M = 1, cancelling the two unit traces, and discarding its nonnegative "
                + "Hilbert--Schmidt remainder proves D(gammaPrime,gamma) >= 0. The CStarMatrix "
                + "star-algebra equivalence transports the two functional-calculus logarithms "
                + "to the same quantumRelativeEntropy used in the local identity. Consequently:")),
            new DocumentBlock.DisplayFormula(Disp(Seq(F.Id("beta"), Sp, Cdot, Sp, F.Id("Q"), Sp, Ge, Sp,
                Call("S", F.Id("sigma")), Sp, Minus, Sp, Call("S", F.Id("sigmaPrime"))))),
            Paragraph(Text(
                "This is an application of the existing declarations, not a new mathematical "
                + "declaration or an independent novelty claim. It is the finite-real-beta part "
                + "of Reeb and Wolf, An improved Landauer Principle with finite-size corrections, "
                + "Theorem 3 (arXiv:1306.4352v3; DOI 10.1088/1367-2630/16/10/103011). "
                + "Entropies use natural logarithms; zero eigenvalues in the final states are "
                + "permitted, and no commutation with H is needed. The inequality holds for "
                + "every real beta; when beta = 1/(kB T) with kB > 0 and T > 0, division by "
                + "beta gives the usual heat bound. Reading the defined fixed-H bath energy "
                + "change Q as dissipated heat is the operational model premise. The argument "
                + "does not establish an implementation or work cost, attainment, equality-state "
                + "characterization, rank reduction, an infinite-dimensional reservoir, or "
                + "infinite inverse temperature.")))))));

    private static DocumentBlock Result(
        string id, string declaration, string title, string text, Formula statement) =>
        Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Module + declaration), H(title),
            StatementSource.FromAuthor(statement), AssessedProvenance.FromLiterature(
                LibraryNoteRef.Create("D5/L/Quantum/micadei2019correlations")),
            Blocks(Paragraph(Text(text))), DescribeRole.Theorem);
}
