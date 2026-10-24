using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuantumChannels;

internal sealed class ChannelTimeReversalNoGoDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/QuantumChannels/ChannelTimeReversalNoGo.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/QuantumChannels/chiribellaaurellzyczkowski2021symmetries");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Randomisation and complete positivity obstruct reversal of every unitary channel.",
        H("ChannelTimeReversalNoGo"), Blocks(
            Describe.Lean(DescribeId.Create("ischannelsymmetry"), DeclarationHandle.Create(Prefix + "IsChannelSymmetry"), H("Symmetries of the channel set"),
                StatementSource.FromAuthor(SymmetryDefinition()), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("Definition 3, PDF page 5: \"A symmetry transformation from the operation space Op(Hin , Hout ) to the operation space Op(Kin , Kout ) (an operation space symmetry, for short) is a bijective transformation S : Op(Hin , Hout ) → Op(Kin , Kout )\" that \"is consistent with randomisations, namely S(p Q + (1−p) R) = p S(Q)+(1−p) S(R), for every pair of quantum operations Q and R, and for every probability p ∈ [0, 1]\". On channels the null-operation requirement has no instance. Here Set.BijOn states bijectivity on the set defined by IsCPTP, and the second conjunct states the complete binary randomisation identity for every real probability in [0,1]."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("unitarychannel"), DeclarationHandle.Create(Prefix + "unitaryChannel"), H("Conjugation by a matrix"),
                StatementSource.FromAuthor(Disp(All("d", N, All("U", Mat(V("d")), Eq(Call("unitaryChannel", V("U")), UC(V("U"))))))), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("For every natural dimension d and every complex d by d matrix U, unitaryChannel U is LinearMap.mulRight ℂ (star U) after LinearMap.mulLeft ℂ U. It sends X to U X (star U). For unitary U this is a completely positive trace-preserving map."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("claim"), DeclarationHandle.Create(Prefix + "claim"), H("No time reversal on all channels"),
                StatementSource.FromAuthor(Disp(Eq(V("claim"), ClaimBody()))), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("Section V.B, PDF page 7: \"We conjecture that this assumption can be lifted, and that the no-go theorem to time reversal applies also to symmetries of the set of quantum channels.\" The dimension d ranges over every natural number at least two. IsCPTP is the existing completely positive trace-preserving predicate on complex-linear maps of d by d matrices. For every natural dimension d and every d by d complex matrix U, conjugation by U is LinearMap.mulRight ℂ (star U) after LinearMap.mulLeft ℂ U, equal to LinearMap.mulLeftRight ℂ (U, star U). The displayed claim uses unitaryChannel in both targets. The two targets are conjugation by star U and by Matrix.transpose U. The quantifier ranges over every randomisation-consistent bijection of this channel set."))), DescribeRole.Definition),
            Node("channeltimereversal-density-psd", "Pauli spectral projectors are positive semidefinite", DensityPsdFormula(),
                "For every axis index a in Fin 3 and Boolean sign e, the spectral projector of the Pauli axis a with sign e is positive semidefinite.",
                "density_psd"),
            Node("channeltimereversal-density-trace", "Pauli spectral projectors have trace one", DensityTraceFormula(),
                "For every axis index a in Fin 3 and Boolean sign e, the spectral projector of the Pauli axis a with sign e has trace one.",
                "density_trace"),
            Describe.Lean(DescribeId.Create("result"), DeclarationHandle.Create(Prefix + "result"), H("Time-reversal symmetries do not exist"),
                StatementSource.FromAuthor(Disp(ClaimBody())), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("For dimensions at least three, Bi_basic forces three finite-block identities; diagonal_contradiction makes the positive block have trace zero, contradicting its trace one. For qubits, finite_pauli_identity and unital_reversed identify the action on unital channels. The pure_preimage and pure_density_rotation lemmas supply a unitary rotation of a pure replacement preimage. The forced_witness_output identity then gives diag(9/8, -1/8), whose negative diagonal entry proves inverse_unitary_no_go. Double transposition preserves complete positivity, trace preservation and convex mixtures, is involutive, and sends conjugation by the transpose of U to conjugation by star U. Composing with this transformation reduces the transpose target to the adjoint target."))), DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("chiribella-aurell-zyczkowski-2021-channel-time-reversal"),
                    ResolutionKind.Proved)))));
    private static Formula ClaimBody() => All("d", N, Imp(LE(D(2), V("d")), All("S", Arrow(Map(V("d")), Map(V("d"))),
        Imp(Call("IsChannelSymmetry", V("S")), And(Not(SourceTarget(false)), Not(SourceTarget(true)))))));
    private static Formula SourceTarget(bool transpose) => All("U", Mat(V("d")), Imp(Member(V("U"), App(Q("Matrix", "unitaryGroup"), Fin(V("d")), C)),
        Eq(App(V("S"), Call("unitaryChannel", V("U"))), Call("unitaryChannel", transpose ? App(Q("Matrix", "transpose"), V("U")) : Call("star", V("U"))))));
    private static Formula SymmetryDefinition() => Disp(All("d", N, All("S", Arrow(Map(V("d")), Map(V("d"))), Eq(Call("IsChannelSymmetry", V("S")), Sym(V("d"), V("S"))))));

    private static Formula V(string name) => F.Id(name);
    private static DocumentBlock Node(string id, string title, Formula formula, string prose, string declaration) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(formula), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);
    private static Formula DensityPsdFormula() =>
        Disp(All("a", Call("Fin", D(3)), All("e", V("Bool"),
            QCall("Matrix", "PosSemidef", Spectral(V("a"), V("e"))))));
    private static Formula DensityTraceFormula() =>
        Disp(All("a", Call("Fin", D(3)), All("e", V("Bool"),
            Eq(QCall("Matrix", "trace", Spectral(V("a"), V("e"))), D(1)))));
    private static Formula Spectral(Formula a, Formula e) =>
        QCall("D5.S3.Quantum.Magic.WignerDistanceMinimum", "spectral", App(Axis(), a), BoolIndex(e));
    private static Formula Axis() => Seq(OpenBracket,
        Pauli("X"), Comma, Sp, Pauli("Y"), Comma, Sp, Pauli("Z"), CloseBracket);
    private static Formula Pauli(string name) => Qualified(
        "D5", "S3", "Quantum", "Information", "StabilizerPairLocalUnitaryInequivalence", "Pauli", name);
    private static Formula BoolIndex(Formula e) =>
        Seq(Call("if"), Sp, Eq(e, V("true")), Sp, Call("then"), Sp, D(1), Sp, Call("else"), Sp, D(0));
    private static Formula Named(string name) => Seq(Operatorname, Grp(V(name)));
    private static Formula Q(string owner, string name) => Seq(Named(owner), Dot, Named(name));
    private static Formula Qualified(params string[] parts)
    {
        Formula result = Named(parts[0]);
        for (var i = 1; i < parts.Length; i++) result = Seq(result, Dot, Named(parts[i]));
        return result;
    }
    private static Formula QCall(string owner, string name, params Formula[] args) =>
        App(Qualified([.. owner.Split('.'), name]), args);
    private static Formula App(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula Call(string name, params Formula[] args) => App(Named(name), args);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula All(string name, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula LE(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula Member(Formula a, Formula b) => Seq(a, Sp, InMacro, Sp, b);
    private static Formula Arrow(Formula a, Formula b) => new Formula.TypeArrow(a, b);
    private static Formula N => Seq(Mathbb, Grp(V("N")));
    private static Formula R => Seq(Mathbb, Grp(V("R")));
    private static Formula C => Seq(Mathbb, Grp(V("C")));
    private static Formula Fin(Formula d) => Call("Fin", d);
    private static Formula Mat(Formula d) => Call("Matrix", Fin(d), Fin(d), C);
    private static Formula Map(Formula d) => Call("MatrixMap", Fin(d), Fin(d), C);
    private static Formula CPTP(Formula phi) => Call("IsCPTP", phi);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Scalar(Formula a, Formula b) => Seq(Parenthesized(a), Sp, Cdot, Sp, Parenthesized(b));
    private static Formula Cast(Formula a, Formula type) => Parenthesized(Seq(a, Colon, Sp, type));
    private static Formula Comp(Formula a, Formula b) => Seq(Parenthesized(a), Sp, new Formula.Subscript(Circ, V("l")), Sp, Parenthesized(b));
    private static Formula UC(Formula u) => Comp(App(Q("LinearMap", "mulRight"), C, Call("star", u)), App(Q("LinearMap", "mulLeft"), C, u));
    private static Formula Mix(Formula p, Formula phi, Formula psi) => Add(Scalar(Cast(p, C), phi), Scalar(Cast(Cast(Sub(D(1), p), R), C), psi));
    private static Formula Channels(Formula d) => Seq(OpenBrace, V("Phi"), Colon, Sp, Map(d), Sp, Mid, Sp, CPTP(V("Phi")), CloseBrace);
    private static Formula Sym(Formula d, Formula s) => And(App(Q("Set", "BijOn"), s, Channels(d), Channels(d)),
        All("Phi", Map(d), All("Psi", Map(d), Imp(CPTP(V("Phi")), Imp(CPTP(V("Psi")),
        All("p", R, Imp(LE(D(0), V("p")), Imp(LE(V("p"), D(1)),
            Eq(App(s, Mix(V("p"), V("Phi"), V("Psi"))), Mix(V("p"), App(s, V("Phi")), App(s, V("Psi"))))))))))));
    private static Formula Not(Formula a) => Seq(Neg, Sp, Parenthesized(a));

}
