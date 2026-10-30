using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Information;

internal sealed class SongKwonScaraniSteadyPriorReversibilityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Information/SongKwonScaraniSteadyPriorReversibility.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Divergence/song2025tabletop");
    private const string Question = "Section V, question 2, page 9: \"In all of the examples we considered, a dynamics appears to be tabletop time-reversible whenever a prior state is a steady state. We do not have a proof that this is true in general, and leave it for a future investigation.\"";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A full-rank steady qutrit prior need not admit fixed-dilation tabletop reversal.",
        H("Stationarity does not imply tabletop time reversibility"),
        Blocks(
            Node("channel", "Forward dilation channel", ChannelFormula(),
                "Equation (1), page 2: \"N(•) = Tr_E[U_SE (• ⊗ ξ_E) U_SE†]\". S and E are finite index types with decidable equality; xi denotes ξ. The product index S × E places the system before the environment. PartialTraceMutualInformation.partialTraceRight traces out the environment.",
                AssessedProvenance.FromLiterature(Source)),
            Node("channelAdjoint", "Hilbert–Schmidt adjoint of the dilation channel", AdjointFormula(),
                "For the channel in equation (1), page 2, the Hilbert–Schmidt adjoint has action Tr_E[U†(Y ⊗ 1)U(1 ⊗ ξ)]. Matrix multiplication has the displayed order; the two identity matrices act on E and S respectively. This expression is derived from the forward dilation by cyclicity of the trace.",
                AssessedProvenance.FromRepo(Source)),
            Node("petz", "Petz recovery map", PetzFormula(),
                "Definition 1, equation (2), page 2: \"N̂_γ^(P)(•) ≡ √γ N†( (1/√N(γ)) • (1/√N(γ)) ) √γ.\" gamma denotes γ. CFC.sqrt is the positive square root; inverse means the matrix inverse. The question below restricts gamma to positive definite matrices and assumes channel U xi gamma = gamma, so these square roots are invertible in the instance used here.",
                AssessedProvenance.FromLiterature(Source)),
            Node("tabletopReverse", "Reverse map with the same interaction", ReverseFormula(),
                "Definition 2, equation (3), page 2: \"N̂_ξ′^(T)(•) ≡ Tr_E[U_SE† (• ⊗ ξ′_E) U_SE].\" eta denotes ξ′. U is the very same interaction used in the forward map; only the environmental state may change.",
                AssessedProvenance.FromLiterature(Source)),
            Node("IsTTR", "Tabletop time reversibility for a prior", TtrFormula(),
                "Definition 2, equation (4), page 2: the channel is tabletop time-reversible for a prior γ \"if there exists ξ′ = ξ′_γ such that its Petz recovery map N̂_γ^(P) is given by N̂_γ^(P) = N̂_ξ′^(T)\". The existential eta is positive semidefinite and has trace one. Equality of the maps means equality on every system matrix X.",
                AssessedProvenance.FromLiterature(Source)),
            Node("claim", "The stationary-prior assertion", new Formula.Logic(Local("claim"), FormulaLogicOperator.Iff, Parenthesized(ClaimBody())),
                Question + " The assertion ranges over finite system and environment types, a unitary U, a positive semidefinite trace-one xi, and a positive definite trace-one gamma fixed by channel U xi. It asks for IsTTR for this fixed U and xi.",
                AssessedProvenance.FromLiterature(Source)),
            Describe.Lean(DescribeId.Create("skt-steady-prior-result"), DeclarationHandle.Create(Prefix + "result"),
                H("A qutrit stationary prior without tabletop reversal"),
                StatementSource.FromAuthor(Disp(new Formula.Not(Parenthesized(ClaimBody())))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Take S = E = Fin 3, xi = Matrix.diagonal ![1/2, 1/3, 1/6], and gamma = Matrix.diagonal ![17/44, 13/44, 14/44]. The unitary exchanges (0,0) with (1,1), (1,0) with (2,2), and (2,0) with (0,2), with coefficient −Complex.I, and fixes (0,1), (1,2), and (2,1). The prior is positive definite, has trace one, and is stationary. For every environmental matrix eta, the tabletop output at (1,1) on Matrix.single 0 0 1 and at (2,2) on Matrix.single 1 1 1 both equal eta 0 0. The corresponding Petz entries are 13/51 and 7/39. Their inequality excludes every eta, including all density matrices. Only this fixed interaction is asserted; no statement about the whole continuous Hamiltonian family is proved here."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("song-kwon-scarani-2025-steady-prior-reversibility"),
                    ResolutionKind.Refuted)))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose, AssessedProvenance provenance) =>
        Describe.Lean(DescribeId.Create("skt-steady-prior-" + name.ToLowerInvariant()), DeclarationHandle.Create(Prefix + name),
            H(title), StatementSource.FromAuthor(Disp(formula)), provenance, Blocks(Paragraph(Text(prose))), DescribeRole.Definition);
    private static Formula X(string name) => F.Id(name);
    private static Formula Q(params string[] names)
    {
        var items = new System.Collections.Generic.List<Formula>();
        foreach (var name in names) { if (items.Count > 0) items.Add(Dot); items.Add(X(name)); }
        return Seq(Operatorname, Grp(Seq([.. items])));
    }
    private static Formula Local(string name) => Q("D5", "S3", "Quantum", "Information", "SongKwonScaraniSteadyPriorReversibility", name);
    private static Formula App(Formula function, params Formula[] arguments) => new Formula.Apply(function, [.. arguments]);
    private static Formula Parenthesized(Formula formula) => Seq(F.Open, formula, F.Close);
    private static Formula All(string name, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Ex(string name, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Eq(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula And(Formula left, Formula right) => new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Imp(Formula left, Formula right) => new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula Mul(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula MatrixType(Formula index) => App(Q("Matrix"), index, index, Seq(Mathbb, Grp(X("C"))));
    private static Formula ProductType() => Parenthesized(Seq(X("S"), Times, Sp, X("E")));
    private static Formula TypedOne(Formula index) => Parenthesized(Seq(D(1), Colon, MatrixType(index)));
    private static Formula Tensor(Formula left, Formula right) => App(Q("Matrix", "kronecker"), left, right);
    private static Formula Adjoint(Formula matrix) => App(Q("Matrix", "conjTranspose"), matrix);
    private static Formula Sqrt(Formula matrix) => App(Q("CFC", "sqrt"), matrix);
    private static Formula Inverse(Formula matrix) => new Formula.Power(Parenthesized(matrix), Seq(Minus, D(1)));
    private static Formula PartialTrace(Formula matrix) => App(Q("D5", "S3", "Quantum", "Information", "PartialTraceMutualInformation", "partialTraceRight"), matrix);
    private static Formula Trace(Formula matrix) => App(Q("Matrix", "trace"), matrix);
    private static Formula Instance(string name, string type, Formula body) => Seq(OpenBracket, App(Q(name), X(type)), CloseBracket, Sp, body);
    private static Formula Carriers(Formula body) => All("S", Q("Type"), All("E", Q("Type"),
        Instance("Fintype", "S", Instance("DecidableEq", "S", Instance("Fintype", "E", Instance("DecidableEq", "E", body))))));
    private static Formula Dilation(Formula body) => All("U", MatrixType(ProductType()), All("xi", MatrixType(X("E")), body));
    private static Formula WithPrior(Formula body) => Dilation(All("gamma", MatrixType(X("S")), body));
    private static Formula ChannelFormula() => Carriers(Dilation(All("X", MatrixType(X("S")),
        Eq(App(Local("channel"), X("U"), X("xi"), X("X")),
            PartialTrace(Mul(Mul(X("U"), Tensor(X("X"), X("xi"))), Adjoint(X("U"))))))));
    private static Formula AdjointFormula() => Carriers(Dilation(All("Y", MatrixType(X("S")),
        Eq(App(Local("channelAdjoint"), X("U"), X("xi"), X("Y")),
            PartialTrace(Mul(Mul(Mul(Adjoint(X("U")), Tensor(X("Y"), TypedOne(X("E")))), X("U")), Tensor(TypedOne(X("S")), X("xi"))))))));
    private static Formula PetzFormula()
    {
        var root = Sqrt(X("gamma"));
        var inverseRoot = Inverse(Sqrt(App(Local("channel"), X("U"), X("xi"), X("gamma"))));
        var middle = App(Local("channelAdjoint"), X("U"), X("xi"), Mul(Mul(inverseRoot, X("X")), inverseRoot));
        return Carriers(WithPrior(All("X", MatrixType(X("S")), Eq(App(Local("petz"), X("U"), X("xi"), X("gamma"), X("X")), Mul(Mul(root, middle), root)))));
    }
    private static Formula ReverseFormula() => Carriers(All("U", MatrixType(ProductType()), All("eta", MatrixType(X("E")), All("X", MatrixType(X("S")),
        Eq(App(Local("tabletopReverse"), X("U"), X("eta"), X("X")), PartialTrace(Mul(Mul(Adjoint(X("U")), Tensor(X("X"), X("eta"))), X("U"))))))));
    private static Formula TtrFormula() => Carriers(WithPrior(new Formula.Logic(
        App(Local("IsTTR"), X("U"), X("xi"), X("gamma")), FormulaLogicOperator.Iff,
        Ex("eta", MatrixType(X("E")), And(App(Q("Matrix", "PosSemidef"), X("eta")),
            And(Eq(Trace(X("eta")), D(1)), All("X", MatrixType(X("S")),
                Eq(App(Local("petz"), X("U"), X("xi"), X("gamma"), X("X")), App(Local("tabletopReverse"), X("U"), X("eta"), X("X"))))))))));
    private static Formula ClaimBody() => Carriers(WithPrior(
        Imp(new Formula.Relation(X("U"), FormulaRelationOperator.MemberOf, App(Q("Matrix", "unitaryGroup"), ProductType(), Seq(Mathbb, Grp(X("C"))))),
        Imp(App(Q("Matrix", "PosSemidef"), X("xi")), Imp(Eq(Trace(X("xi")), D(1)),
        Imp(App(Q("Matrix", "PosDef"), X("gamma")), Imp(Eq(Trace(X("gamma")), D(1)),
        Imp(Eq(App(Local("channel"), X("U"), X("xi"), X("gamma")), X("gamma")),
            App(Local("IsTTR"), X("U"), X("xi"), X("gamma"))))))))));
}
