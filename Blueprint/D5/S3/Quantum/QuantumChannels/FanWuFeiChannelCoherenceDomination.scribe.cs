using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.QuantumChannels;

internal sealed class FanWuFeiChannelCoherenceDominationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/QuantumChannels/FanWuFeiChannelCoherenceDomination.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Divergence/fanwufei2024channelcoherence");
    private const string ConjectureQuotation =
        "Page 8, Section 3: “From the examples in the next section and numerical results, "
        + "it is conjectured that C_{α,1}(φ) ≥ C̃_{α,1}(φ) holds for all quantum channels φ, "
        + "but we have not yet found a proof.”";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A qubit measure-and-prepare channel has Choi coherence below its commutator coherence at alpha = 2.",
        H("A counterexample to Fan–Wu–Fei channel coherence domination"),
        Blocks(
            Paragraph(Text("Complex matrices use the source's computational basis and its product basis. "
                + "MatrixMap denotes the complex linear maps on matrices. Real matrix powers use cfc, "
                + "the real continuous functional calculus. The infimum and supremum range over all "
                + "positive semidefinite matrices of trace one in the displayed spaces. Anonymous square "
                + "brackets give finite enumerations and decidable equality for their index types.")),
            Node("renyiDiv", "The alpha-relative Renyi divergence at z = 1", RenyiFormula(),
                "Page 2, Eqs. (1)–(2): “D_{α,z}(ρ, σ) = (f_{α,z}(ρ, σ)^{1/α} − 1)/(α − 1)”, "
                + "with “f_{α,z}(ρ, σ) = Tr (σ^{(1−α)/2z} ρ^{α/z} σ^{(1−α)/2z})^z”. "
                + "Here z = 1. Matrix powers are cfc applied to the real power function, and RCLike.re "
                + "takes the real part of the complex trace. The displayed formula is defined on all "
                + "complex square matrices; the coherence quantities below restrict to density matrices.",
                AssessedProvenance.FromLiterature(Source)),
            Node("coherence", "Coherence of the normalized Choi matrix", CoherenceFormula(),
                "Page 4, Definition 2, Eq. (7): “C_{α,z}(φ) = min_{φ̃ ∈ IC_AB} D_{α,z}(φ, φ̃) "
                + "= min_{M_φ̃ ∈ I} (f^{1/α}_{α,z}(M_φ, M_φ̃) − 1)/(α − 1)”. "
                + "The formula takes z = 1 and expresses the minimum as a real infimum over diagonal "
                + "density matrices on a × b. The normalized Choi entry at (i,j),(k,l) is "
                + "(card a)⁻¹ φ(single i k 1) j l. Its scalar factor is complex; it equals 1/2 "
                + "for the qubit input used in the counterexample.", AssessedProvenance.FromLiterature(Source)),
            Node("commutativityCoherence", "Coherence from the two orders of dephasing", CommutativityFormula(),
                "Page 7, Definition 4, Eq. (10): “C̃_{α,z}(φ) = sup_ρ D_{α,z}(φ ∘ ∆_A(ρ), "
                + "∆_B ∘ φ(ρ)) … the supremum in Eq. (10) is taken over all quantum states.” "
                + "At z = 1, the input is any density matrix on a. Dephasing retains the diagonal "
                + "entries, as in Eq. (9), and occurs before or after φ in the two arguments.",
                AssessedProvenance.FromLiterature(Source)),
            Node("claim", "The proposed domination for every channel", IffOf(Named("claim"), ClaimBody()),
                ConjectureQuotation + " The finite input and output types are a and b; φ is completely "
                + "positive and preserves the trace of every matrix. The range of α is (0,1) ∪ (1,2], "
                + "as in Eq. (8). The comparison is written with the commutator quantity on the left.",
                AssessedProvenance.FromLiterature(Source)),
            Describe.Lean(DescribeId.Create("fan-wu-fei-result"), DeclarationHandle.Create(Prefix + "result"),
                H("Two prepared outputs refute the universal comparison"),
                StatementSource.FromAuthor(Disp(new Formula.Not(Parenthesized(ClaimBody())))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Take σ_t = [[1/2,t/2],[t/2,1/2]] and "
                    + "φ(X) = X(0,0) σ_{3/4} + X(1,1) σ_{1/2}. Sixteen rational Kraus operators "
                    + "establish complete positivity, and the output trace equals the input trace. "
                    + "The normalized Choi matrix M satisfies re(trace(M M)) = 45/128. The diagonal "
                    + "density matrix I/4 gives coherence(2,φ) ≤ sqrt(45/32) − 1. Every input density "
                    + "matrix gives commutator divergence at most 1/4, and the input diagonal(1,0) "
                    + "attains 1/4. Thus commutativityCoherence(2,φ) ≥ 1/4. Finally "
                    + "sqrt(45/32) − 1 < 1/4, contradicting the displayed universal statement."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("fan-wu-fei-2024-channel-coherence-domination"),
                    ResolutionKind.Refuted)))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        AssessedProvenance provenance) => Describe.Lean(DescribeId.Create("fan-wu-fei-" + name.ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(Disp(formula)),
        provenance, Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula V(string name) => F.Id(name);
    private static Formula Named(string name) => Seq(Operatorname, Grp(V(name)));
    private static Formula Qualified(string owner, string name) => Seq(Named(owner), Dot, Named(name));
    private static Formula Call(string name, params Formula[] arguments) => new Formula.Apply(Named(name), [.. arguments]);
    private static Formula App(Formula function, params Formula[] arguments) => new Formula.Apply(function, [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Sp, Colon, Sp, type));
    private static Formula All(Formula name, Formula type, Formula body) => Seq(Forall, Sp, Typed(name, type), Comma, Sp, Parenthesized(body));
    private static Formula Some(Formula name, Formula type, Formula body) => Seq(Exists, Sp, Typed(name, type), Comma, Sp, Parenthesized(body));
    private static Formula Lam(Formula name, Formula type, Formula body) => Seq(LambdaLower, Sp, Typed(name, type), Sp, Mapsto, Sp, Parenthesized(body));
    private static Formula Instance(string name, Formula type, Formula body) => Seq(OpenBracket, Call(name, type), CloseBracket, Sp, body);
    private static Formula Finite(Formula type, Formula body) => Instance("Fintype", type, Instance("DecidableEq", type, body));
    private static Formula Equal(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula LE(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula LT(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula And(Formula left, Formula right) => new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Or(Formula left, Formula right) => new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Or, Parenthesized(right));
    private static Formula Imp(Formula left, Formula right) => new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula IffOf(Formula left, Formula right) => new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));
    private static Formula Sub(Formula left, Formula right) => new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Subtract, Parenthesized(right));
    private static Formula Mul(Formula left, Formula right) => new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Multiply, Parenthesized(right));
    private static Formula Pow(Formula value, Formula exponent) => new Formula.Power(Parenthesized(value), exponent);
    private static Formula Div(Formula left, Formula right) => new Formula.Fraction(left, right);
    private static Formula Reals() => Seq(Mathbb, Grp(V("R")));
    private static Formula Complexes() => Seq(Mathbb, Grp(V("C")));
    private static Formula Mat(Formula n) => Call("Matrix", n, n, Complexes());
    private static Formula Pair(Formula a, Formula b) => Parenthesized(Seq(a, Sp, Times, Sp, b));
    private static Formula Trace(Formula matrix) => App(Qualified("Matrix", "trace"), matrix);
    private static Formula Diagonal(Formula matrix, Formula n) => App(Qualified("Matrix", "diagonal"), Lam(V("i"), n, App(matrix, V("i"), V("i"))));
    private static Formula State(Formula matrix) => And(App(Qualified("Matrix", "PosSemidef"), matrix), Equal(Trace(matrix), D(1)));
    private static Formula SetOf(Formula name, Formula condition) => Seq(OpenBrace, Typed(name, Reals()), Sp, Mid, Sp, condition, CloseBrace);
    private static Formula MatrixMapType(Formula a, Formula b) => Call("MatrixMap", a, b, Complexes());
    private static Formula ChannelBinders(Formula body) => All(V("a"), V("Type"), All(V("b"), V("Type"), Finite(V("a"), Finite(V("b"), body))));

    private static Formula CfcPower(Formula matrix, Formula exponent) =>
        Call("cfc", Lam(V("x"), Reals(), Pow(V("x"), exponent)), matrix);

    private static Formula RenyiFormula()
    {
        Formula c = V("c"), p = Div(Sub(D(1), Alpha), D(2));
        Formula sandwich = Mul(Mul(CfcPower(SigmaLower, p), CfcPower(Rho, Alpha)), CfcPower(SigmaLower, p));
        Formula value = Div(Sub(Pow(App(Qualified("RCLike", "re"), Trace(sandwich)), Div(D(1), Alpha)), D(1)), Sub(Alpha, D(1)));
        return All(c, V("Type"), Finite(c, All(Alpha, Reals(), All(Rho, Mat(c), All(SigmaLower, Mat(c),
            Equal(Call("renyiDiv", Alpha, Rho, SigmaLower), value))))));
    }

    private static Formula ChoiEntries()
    {
        Formula p = V("p"), q = V("q"), n = Pair(V("a"), V("b"));
        Formula card = Typed(App(Qualified("Fintype", "card"), V("a")), Complexes());
        Formula entry = App(Varphi, App(Qualified("Matrix", "single"), Seq(p, Dot, D(1)), Seq(q, Dot, D(1)), D(1)), Seq(p, Dot, D(2)), Seq(q, Dot, D(2)));
        return Lam(p, n, Lam(q, n, Mul(Pow(card, Seq(Minus, D(1))), entry)));
    }

    private static Formula CoherenceFormula()
    {
        Formula n = Pair(V("a"), V("b")), r = V("r");
        Formula feasible = Some(SigmaLower, Mat(n), And(State(SigmaLower),
            And(Equal(Diagonal(SigmaLower, n), SigmaLower), Equal(r, Call("renyiDiv", Alpha, ChoiEntries(), SigmaLower)))));
        return ChannelBinders(All(Alpha, Reals(), All(Varphi, MatrixMapType(V("a"), V("b")),
            Equal(Call("coherence", Alpha, Varphi), Call("sInf", SetOf(r, feasible))))));
    }

    private static Formula CommutativityFormula()
    {
        Formula a = V("a"), b = V("b"), r = V("r");
        Formula after = App(Qualified("Matrix", "diagonal"), Lam(V("i"), b, App(Varphi, Rho, V("i"), V("i"))));
        Formula feasible = Some(Rho, Mat(a), And(State(Rho), Equal(r, Call("renyiDiv", Alpha, App(Varphi, Diagonal(Rho, a)), after))));
        return ChannelBinders(All(Alpha, Reals(), All(Varphi, MatrixMapType(a, b),
            Equal(Call("commutativityCoherence", Alpha, Varphi), Call("sSup", SetOf(r, feasible))))));
    }

    private static Formula ClaimBody()
    {
        Formula a = V("a"), b = V("b"), x = V("x");
        Formula tp = All(x, Mat(a), Equal(Trace(App(Varphi, x)), Trace(x)));
        Formula range = Or(And(LT(D(0), Alpha), LT(Alpha, D(1))), And(LT(D(1), Alpha), LE(Alpha, D(2))));
        return ChannelBinders(All(Varphi, MatrixMapType(a, b),
            Imp(Call("IsCompletelyPositive", Varphi), Imp(tp, All(Alpha, Reals(), Imp(range,
                LE(Call("commutativityCoherence", Alpha, Varphi), Call("coherence", Alpha, Varphi))))))));
    }
}
