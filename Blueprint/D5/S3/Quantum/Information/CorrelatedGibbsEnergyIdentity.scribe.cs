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
                    F.Id("beta"), Sp, Mul, Sp, Lp,
                    Call("E", F.Id("H"), F.Id("sigma")), Sp, Minus, Sp,
                    Call("E", F.Id("H"), F.Id("gamma")), Rp, Sp, Minus, Sp, Lp,
                    Call("S", F.Id("sigma")), Sp, Minus, Sp, Call("S", F.Id("gamma")), Rp))),
            Describe.Lean(
                DescribeId.Create("joint-entropy"),
                DeclarationHandle.Create(Module + "von_neumann_entropy_unitary"),
                H("Joint entropy is conserved"),
                StatementSource.FromAuthor(Disp(Seq(Forall, Sp, Rho, Comma, Sp, F.Id("U"),
                    Comma, Sp, Call("S", Call("unitaryConjugateState", F.Id("U"), Rho)),
                    Sp, Eq, Sp, Call("S", Rho)))),
                AssessedProvenance.FromRepo(),
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
                    F.Id("rhoA"), Sp, Eq, Sp, F.Id("gammaA"), Sp, And, Sp,
                    F.Id("rhoB"), Sp, Eq, Sp, F.Id("gammaB"), Sp, Implies, Sp,
                    F.Id("betaA"), Sp, Mul, Sp, F.Id("DeltaEA"), Sp, Plus, Sp,
                    F.Id("betaB"), Sp, Mul, Sp, F.Id("DeltaEB"), Sp, Eq, Sp,
                    Call("D", F.Id("rhoAPrime"), F.Id("gammaA")), Sp, Plus, Sp,
                    Call("D", F.Id("rhoBPrime"), F.Id("gammaB")), Sp, Plus, Sp,
                    Call("I", F.Id("rhoPrime")), Sp, Minus, Sp, Call("I", Rho)))))));

    private static DocumentBlock Result(
        string id, string declaration, string title, string text, Formula statement) =>
        Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Module + declaration), H(title),
            StatementSource.FromAuthor(statement), AssessedProvenance.FromLiterature(
                LibraryNoteRef.Create("D5/L/Quantum/micadei2019correlations")),
            Blocks(Paragraph(Text(text))), DescribeRole.Theorem);
}
