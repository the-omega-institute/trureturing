using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.QuantumChannels;

internal sealed class ChannelAssemblageLOSRRefutationDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/QuantumChannels/ChannelAssemblageLOSRRefutation";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumContext/zjawinschmidhobansainz2023channel");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The controlled-rotation channel assemblage at pi/3 converts by local operations and shared randomness to the assemblage at pi/2, contradicting the proposed angle ordering.",
        H("Controlled-rotation assemblages do not obey the proposed LOSR angle ordering"),
        Blocks(
            Paragraph(Text(
                "Matrices have complex entries and use the computational product bases. "
                    + "MatrixMap(A,B,C) consists of complex linear maps from matrices on A to matrices on B. "
                    + "The tensor product of matrices is the Kronecker product, and a dagger denotes conjugate transpose. "
                    + "Anonymous bracketed assumptions supply finite enumerations and decidable equality. "
                    + "All source line numbers refer to channel-quantum.tex in arXiv:2209.10177v3.")),
            Node("is-cptp", "IsCPTP", "Completely positive trace-preserving maps", CPTPFormula(),
                AssessedProvenance.FromLiterature(Source),
                "A map is completely positive at every finite amplification and preserves the trace of every matrix. "
                    + "Trace preservation is not restricted to normalized states. This is the CPTP notion used for "
                    + "the channels at source lines 175-179 and 217-220."),
            Node("assemblage-type", "Assemblage", "Binary families of qubit matrix maps", AssemblageTypeFormula(),
                AssessedProvenance.FromRepo(Source),
                "An Assemblage is a family of qubit matrix maps indexed first by the binary outcome a and then "
                    + "by the binary measurement choice x. This type supplies the carrier for the binary scenario "
                    + "at source line 316. The type alone imposes no positivity, trace, or no-signalling condition."),
            Node("rotation-y", "rotationY", "The half-angle y rotation", RotationFormula(),
                AssessedProvenance.FromLiterature(Source),
                "The rotation has real cosine and sine entries included explicitly into the complex scalars. "
                    + "It is the lower block of the controlled rotation in Eq. CR, source lines 318-325. "
                    + "The identity cos squared plus sin squared equals one supplies the nonzero condition in "
                    + "the plane-conformal matrix construction. The definition is made for every real angle."),
            Node("assemblage", "assemblage", "The Bell-state controlled-rotation family", AssemblageFormula(),
                AssessedProvenance.FromLiterature(Source),
                "Equation CRfam, source lines 316-333, begins with the Bell density matrix on A and B and an "
                    + "arbitrary input matrix on the third qubit. The associativity equivalence orders the indices "
                    + "as A times (B times the input qubit). The gate acts on the last two qubits with B as control. "
                    + "The displayed permutation then places B last so that the right partial trace removes it. "
                    + "Alice's Pauli-z or Pauli-x measurement effect acts on A, and the left partial trace removes A. "
                    + "The equality specifies the linear map on every matrix, with no density-matrix restriction."),
            Node("losr-convertible", "LOSRConvertible", "Local operations with shared randomness and memory", LOSRFormula(),
                AssessedProvenance.FromLiterature(Source),
                "Equation LOSRtrans-channel, source lines 246-265, combines finite shared randomness Lambda, "
                    + "a finite quantum memory S, Alice's conditional probabilities q, and Bob's CPTP pre- and "
                    + "post-processing maps. The distribution p is nonnegative and sums to one. For each l, a and x', "
                    + "the distribution q over a' and x is nonnegative and normalized. Its marginal over a' is "
                    + "independent of a, which is precisely the no-retrocausation condition at source line 260. "
                    + "Bob sends the input into a qubit and S, applies the chosen source branch tensored with the "
                    + "identity on S, and maps the output qubit and S to the final qubit. The final equality holds "
                    + "on all complex matrices; its scalar action is by the real probability p(l)q(l,a',x,a,x')."),
            Node("claim", "claim", "The proposed angle criterion", ClaimFormula(),
                AssessedProvenance.FromRepo(Source),
                "Conjecture 3, source lines 353-355, proposes that conversion within the family is possible "
                    + "exactly when the source angle is at least the target angle. The displayed proposition uses "
                    + "the literal controlled-rotation family and the finite-memory LOSR formula above. "
                    + "Both real angles lie in the interval with zero excluded and pi/2 included."),
            Describe.Lean(
                DescribeId.Create("result"),
                DeclarationHandle.Create(Module + ".result"),
                H("A conversion from the smaller angle to the larger angle"),
                StatementSource.FromAuthor(Disp(new Formula.Not(Parenthesized(Local("claim"))))),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "First expand the three-qubit construction in the computational basis. Tracing B "
                            + "removes the off-diagonal terms of its control index. The Pauli-z measurement "
                            + "selects one of the two remaining branches, whereas the Pauli-x measurement "
                            + "weights them equally. For every real theta and every input matrix rho this gives:")),
                    new DocumentBlock.DisplayFormula(ExpandedFamilyFormula()),
                    Paragraph(Text(
                        "Take a qubit memory. The pre-processing map E inserts a zero state in the source input "
                            + "and stores rho in memory: E(rho) = |0><0| tensor rho. Its single Kraus operator K "
                            + "has entry K(i,j) equal to the identity entry with row i.2 and column j when i.1 is zero, "
                            + "and zero otherwise. Put V(b) equal to the identity for b = 0 and to rotationY(pi/2) "
                            + "for b = 1. The post-processing map F(b) has Kraus operators indexed by k in Fin 2; "
                            + "their (i,j) entries are V(b)(i,j.2) when j.1 = k and zero otherwise. Thus F(b) "
                            + "traces out the source output and conjugates the memory by V(b).")),
                    Paragraph(Text(
                        "Choose a shared pair l = (b,r) of independent uniform bits. Alice always queries x = 0, "
                            + "ignores a, and outputs a' = b when x' = 0 and a' = r when x' = 1. "
                            + "Her conditional probability is one exactly for this choice of x and a', and zero "
                            + "otherwise. Each pair has probability 1/4.")),
                    Paragraph(Text(
                        "The pre-processing Kraus operator satisfies K dagger K = 1, so its Kraus map is "
                            + "completely positive and trace preserving. For the post-processing, the identity "
                            + "cos squared plus sin squared equals one gives V(b) dagger V(b) = 1 in both cases "
                            + "of b. Summing the products of each post-processing Kraus operator with its adjoint "
                            + "in the order L dagger L gives the identity on the source output and memory. "
                            + "The finite Kraus channel construction therefore proves that both post-processing "
                            + "maps are also completely positive and trace preserving.")),
                    Paragraph(Text(
                        "For any complex linear qubit matrix map Phi, direct expansion of these Kraus operators "
                            + "shows that F(b)((Phi tensor id)(E(rho))) is the trace of Phi(|0><0|) times "
                            + "V(b) rho V(b) dagger. The expanded family and the trigonometric identity give "
                            + "trace(assemblage(theta,a,0)(|0><0|)) = 1/2 for both outcomes a. "
                            + "Consequently each source branch queried by Alice contributes one half of "
                            + "V(b) rho V(b) dagger.")),
                    Paragraph(Text(
                        "At source angle pi/3, summing the two source outcomes and the four shared pairs "
                            + "now gives exactly the expanded family at target angle pi/2: when x' = 0, "
                            + "fixing a' selects b and gives the corresponding conjugation with weight 1/2; "
                            + "when x' = 1, fixing a' selects r and leaves the two conjugations with weight 1/4 each. "
                            + "Checking the binary values of a' and x' establishes this equality on every matrix.")),
                    Paragraph(Text(
                        "Use these data in the definition of LOSRConvertible. The four probabilities 1/4 "
                            + "are nonnegative and sum to one. Alice's probabilities are zero or one and sum "
                            + "to one over a' and x for every l, a and x'. They do not depend on a, so their "
                            + "marginal over a' satisfies no retrocausation. The two CPTP conditions and the "
                            + "matrix equality just proved supply the remaining conditions for the conversion.")),
                    new DocumentBlock.DisplayFormula(ConversionFormula()),
                    Paragraph(Text(
                        "Finally pi is positive, so pi/3 and pi/2 both belong to the required interval, "
                            + "and pi/3 is strictly below pi/2. If claim held, its forward implication applied "
                            + "to this conversion would give pi/3 at least pi/2, a contradiction."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("zjawin-schmid-hoban-sainz-2023-channel-assemblage-losr-refutation"),
                    ResolutionKind.Refuted)))));

    private static DocumentBlock Node(string id, string declaration, string title, Formula formula,
        AssessedProvenance provenance, string prose) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Module + "." + declaration), H(title),
            StatementSource.FromAuthor(Disp(formula)), provenance,
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula CPTPFormula()
    {
        Formula preservation = All("X", Mat(X("A"), X("A")),
            Equal(Trace(At(X("Φ"), X("X"))), Trace(X("X"))));
        Formula body = All("Φ", MapType(X("A"), X("B")), IffOf(LocalCall("IsCPTP", X("Φ")),
            And(At(MapName("IsCompletelyPositive"), X("Φ")), preservation)));
        return All("A", Qualified("Type"), All("B", Qualified("Type"),
            Instance(At(Qualified("Fintype"), X("A")),
            Instance(At(Qualified("DecidableEq"), X("A")),
            Instance(At(Qualified("Fintype"), X("B")), body)))));
    }

    private static Formula AssemblageTypeFormula() => Equal(Typed(Local("Assemblage"), Qualified("Type")),
        Arrow(Qubit(), Arrow(Qubit(), MapType(Qubit(), Qubit()))));

    private static Formula RotationFormula()
    {
        Formula c = At(Qualified("Complex", "ofReal"), At(Qualified("Real", "cos"), Div(X("θ"), D(2))));
        Formula s = At(Qualified("Complex", "ofReal"), At(Qualified("Real", "sin"), Div(X("θ"), D(2))));
        Formula projected = Call("val", At(Qualified("Matrix", "planeConformalMatrix"), c, s));
        Formula matrix = Seq(Begin, Grp(F.Id("pmatrix")), c, Amp, new Formula.Negate(s), RowBreak,
            s, Amp, c, End, Grp(F.Id("pmatrix")));
        return All("θ", Reals(), And(Equal(Typed(LocalCall("rotationY", X("θ")), Mat(Qubit(), Qubit())), projected),
            Equal(projected, matrix)));
    }

    private static Formula AssemblageFormula()
    {
        Formula assoc = At(Qualified("Equiv", "prodAssoc"), Qubit(), Qubit(), Qubit());
        Formula permutation = LambdaOf("p", Product(Product(Qubit(), Qubit()), Qubit()),
            Pair(Projection(Projection(X("p"), 1), 1),
                Pair(Projection(X("p"), 2), Projection(Projection(X("p"), 1), 2))));
        Formula gate = Kron(Identity(), At(Qualified("D5", "S3", "Quantum", "Dynamics", "PositivePauliClockOrder", "controlled"),
            Identity(), LocalCall("rotationY", X("θ"))));
        Formula joint = At(Qualified("Matrix", "reindex"), assoc, assoc,
            Kron(Qualified("D5", "S3", "QuantumBounds", "CHSHWitness", "bellDensity"), X("ρ")));
        Formula evolved = Mul(Mul(X("gate"), X("joint")), Adjoint(X("gate")));
        Formula reduced = At(PartialTrace("partialTraceRight"),
            At(Qualified("Matrix", "submatrix"), X("evolved"), permutation, permutation));
        Formula measurement = At(Qualified("D5", "S3", "QuantumBounds", "StatisticalStrengthMagicSquare", "chshAlice"),
            X("x"), X("a"));
        Formula body = Let("gate", gate, Let("joint", joint, Let("evolved", evolved, Let("reduced", reduced,
            At(PartialTrace("partialTraceLeft"), Mul(Kron(measurement, Identity()), X("reduced")))))));
        return All("θ", Reals(), All("a", Qubit(), All("x", Qubit(), All("ρ", Mat(Qubit(), Qubit()),
            Equal(At(LocalCall("assemblage", X("θ"), X("a"), X("x")), X("ρ")), body)))));
    }

    private static Formula LOSRFormula()
    {
        Formula classicalType = Arrow(X("Λ"), Arrow(Qubit(), Arrow(Qubit(), Arrow(Qubit(), Arrow(Qubit(), Reals())))));
        Formula q = At(X("q"), X("l"), X("a'"), X("x"), X("a"), X("x'"));
        Formula nonnegativeP = All("l", X("Λ"), LE(Typed(D(0), Reals()), At(X("p"), X("l"))));
        Formula normalizedP = Equal(SumOver("l", X("Λ"), At(X("p"), X("l"))), Typed(D(1), Reals()));
        Formula nonnegativeQ = All("l", X("Λ"), All("a'", Qubit(), All("x", Qubit(), All("a", Qubit(),
            All("x'", Qubit(), LE(Typed(D(0), Reals()), q))))));
        Formula normalizedQ = All("l", X("Λ"), All("a", Qubit(), All("x'", Qubit(),
            Equal(SumOver("a'", Qubit(), SumOver("x", Qubit(), q)), Typed(D(1), Reals())))));
        Formula noRetrocausation = All("l", X("Λ"), All("x", Qubit(), All("x'", Qubit(),
            All("a₁", Qubit(), All("a₂", Qubit(), Equal(
                SumOver("a'", Qubit(), At(X("q"), X("l"), X("a'"), X("x"), X("a₁"), X("x'"))),
                SumOver("a'", Qubit(), At(X("q"), X("l"), X("a'"), X("x"), X("a₂"), X("x'")))))))));
        Formula preCPTP = All("l", X("Λ"), LocalCall("IsCPTP", At(X("pre"), X("l"))));
        Formula postCPTP = All("l", X("Λ"), LocalCall("IsCPTP", At(X("post"), X("l"))));
        Formula source = At(X("I"), X("a"), X("x"));
        Formula memoryIdentity = Typed(Qualified("LinearMap", "id"), MapType(X("S"), X("S")));
        Formula mapped = At(At(X("post"), X("l")),
            At(At(MapName("kron"), source, memoryIdentity), At(At(X("pre"), X("l")), X("ρ"))));
        Formula conversion = All("a'", Qubit(), All("x'", Qubit(), All("ρ", Mat(Qubit(), Qubit()),
            Equal(At(At(X("I'"), X("a'"), X("x'")), X("ρ")),
                SumOver("l", X("Λ"), SumOver("a", Qubit(), SumOver("x", Qubit(),
                    Smul(Typed(Mul(At(X("p"), X("l")), q), Reals()), mapped))))))));
        Formula conditions = And(nonnegativeP, And(normalizedP, And(nonnegativeQ,
            And(normalizedQ, And(noRetrocausation, And(preCPTP, And(postCPTP, conversion)))))));
        Formula data = Some("p", Arrow(X("Λ"), Reals()), Some("q", classicalType,
            Some("pre", Arrow(X("Λ"), MapType(Qubit(), Product(Qubit(), X("S")))),
            Some("post", Arrow(X("Λ"), MapType(Product(Qubit(), X("S")), Qubit())), conditions))));
        Formula instances = LetInstance(X("fΛ"), LetInstance(X("fS"), LetInstance(X("dS"), data)));
        Formula existence = Some("Λ", Qualified("Type"), Some("S", Qualified("Type"),
            Some("fΛ", At(Qualified("Fintype"), X("Λ")),
            Some("fS", At(Qualified("Fintype"), X("S")),
            Some("dS", At(Qualified("DecidableEq"), X("S")), instances)))));
        return All("I", Local("Assemblage"), All("I'", Local("Assemblage"),
            IffOf(LocalCall("LOSRConvertible", X("I"), X("I'")), existence)));
    }

    private static Formula ClaimFormula() => IffOf(Local("claim"),
        All("θ₁", Reals(), All("θ₂", Reals(), Imp(InInterval(X("θ₁")), Imp(InInterval(X("θ₂")),
            IffOf(LocalCall("LOSRConvertible", LocalCall("assemblage", X("θ₁")), LocalCall("assemblage", X("θ₂"))),
                new Formula.Relation(X("θ₁"), FormulaRelationOperator.GreaterThanOrEqual, X("θ₂"))))))));

    private static Formula ExpandedFamilyFormula()
    {
        Formula rotated = Mul(Mul(LocalCall("rotationY", X("θ")), X("ρ")), Adjoint(LocalCall("rotationY", X("θ"))));
        Formula half = Typed(Div(D(1), D(2)), Complexes());
        Formula quarter = Typed(Div(D(1), D(4)), Complexes());
        Formula value = Conditional(Equal(X("x"), Typed(D(0), Qubit())),
            Conditional(Equal(X("a"), Typed(D(0), Qubit())), Smul(half, X("ρ")), Smul(half, rotated)),
            Smul(quarter, Add(X("ρ"), rotated)));
        return All("θ", Reals(), All("a", Qubit(), All("x", Qubit(), All("ρ", Mat(Qubit(), Qubit()),
            Equal(At(LocalCall("assemblage", X("θ"), X("a"), X("x")), X("ρ")), value)))));
    }

    private static Formula ConversionFormula() => LocalCall("LOSRConvertible",
        LocalCall("assemblage", Div(Qualified("Real", "pi"), D(3))),
        LocalCall("assemblage", Div(Qualified("Real", "pi"), D(2))));

    private static Formula X(string name) => name switch
    {
        "Φ" => Phi,
        "θ" => Theta,
        "θ₁" => new Formula.Subscript(Theta, D(1)),
        "θ₂" => new Formula.Subscript(Theta, D(2)),
        "ρ" => Rho,
        "Λ" => Lambda,
        "fΛ" => Seq(F.Id("f"), Lambda),
        "a'" => Seq(F.Id("a"), Apos),
        "x'" => Seq(F.Id("x"), Apos),
        "I'" => Seq(F.Id("I"), Apos),
        "a₁" => new Formula.Subscript(F.Id("a"), D(1)),
        "a₂" => new Formula.Subscript(F.Id("a"), D(2)),
        _ => F.Id(name),
    };

    private static Formula Qualified(params string[] parts)
    {
        var items = new System.Collections.Generic.List<Formula>();
        foreach (var part in parts)
        {
            if (items.Count > 0) items.Add(Dot);
            items.Add(F.Id(part));
        }
        return Seq(Operatorname, Grp(Seq([.. items])));
    }

    private static Formula Local(string name) => Qualified("D5", "S3", "Quantum", "QuantumChannels",
        "ChannelAssemblageLOSRRefutation", name);
    private static Formula LocalCall(string name, params Formula[] args) => At(Local(name), args);
    private static Formula MapName(string name) => Qualified("D5", "S3", "Quantum", "Foundation",
        "FiniteKrausChannel", "PhyslibLeaf", "MatrixMap", name);
    private static Formula MapType(Formula a, Formula b) => At(Qualified("D5", "S3", "Quantum", "Foundation",
        "FiniteKrausChannel", "PhyslibLeaf", "MatrixMap"), a, b, Complexes());
    private static Formula Mat(Formula a, Formula b) => At(Qualified("Matrix"), a, b, Complexes());
    private static Formula Qubit() => At(Qualified("Fin"), D(2));
    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Complexes() => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula At(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula Parenthesized(Formula value) => Seq(Left, Open, value, Right, Close);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula Pair(Formula a, Formula b) => Parenthesized(Seq(a, Comma, Sp, b));
    private static Formula Product(Formula a, Formula b) => Parenthesized(Seq(a, Sp, Times, Sp, b));
    private static Formula Projection(Formula value, byte field) => Seq(value, Dot, D(field));
    private static Formula Arrow(Formula domain, Formula codomain) => new Formula.TypeArrow(domain, codomain);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(X(name), type), Comma, Sp, Parenthesized(body));
    private static Formula Some(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, Typed(X(name), type), Comma, Sp, Parenthesized(body));
    private static Formula LambdaOf(string name, Formula type, Formula body) =>
        Seq(LambdaLower, Sp, Typed(X(name), type), Sp, Mapsto, Sp, Parenthesized(body));
    private static Formula Instance(Formula type, Formula body) => Seq(OpenBracket, type, CloseBracket, Sp, body);
    private static Formula Let(string name, Formula value, Formula body) =>
        Seq(Qualified("let"), Sp, X(name), Sp, Colon, Eq, Sp, value, Semi, Sp, Parenthesized(body));
    private static Formula LetInstance(Formula value, Formula body) =>
        Seq(Qualified("letI"), Sp, Colon, Eq, Sp, value, Semi, Sp, Parenthesized(body));
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula IffOf(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Iff, Parenthesized(b));
    private static Formula LE(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Mul(Formula a, Formula b) =>
        new Formula.Binary(Parenthesized(a), FormulaBinaryOperator.Multiply, Parenthesized(b));
    private static Formula Div(Formula a, Formula b) => new Formula.Fraction(a, b);
    private static Formula Smul(Formula a, Formula b) => Seq(Parenthesized(a), Sp, Cdot, Sp, Parenthesized(b));
    private static Formula SumOver(string name, Formula type, Formula body) =>
        Seq(new Formula.Subscript(Sum, Typed(X(name), type)), Sp, Parenthesized(body));
    private static Formula Trace(Formula value) => At(Qualified("Matrix", "trace"), value);
    private static Formula Adjoint(Formula value) => At(Qualified("Matrix", "conjTranspose"), value);
    private static Formula Identity() => Typed(D(1), Mat(Qubit(), Qubit()));
    private static Formula Kron(Formula a, Formula b) => At(Qualified("Matrix", "kronecker"), a, b);
    private static Formula PartialTrace(string name) => Qualified("D5", "S3", "Quantum", "Information",
        "PartialTraceMutualInformation", name);
    private static Formula InInterval(Formula value) => new Formula.Relation(value, FormulaRelationOperator.MemberOf,
        At(Qualified("Set", "Ioc"), Typed(D(0), Reals()), Div(Qualified("Real", "pi"), D(2))));
    private static Formula Conditional(Formula condition, Formula yes, Formula no) =>
        Seq(Qualified("if"), Sp, Parenthesized(condition), Sp, Qualified("then"), Sp, Parenthesized(yes),
            Sp, Qualified("else"), Sp, Parenthesized(no));
}
