using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Information;

internal sealed class SingerQuadricQubitDistanceCeilingDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Information/SingerQuadricQubitDistanceCeiling.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumStates/kulhandjian2026singer");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Kulhandjian and Hanzo (arXiv:2610.02392) build qubit stabilizer codes Q(2,d) from a Singer difference set and the quadric Tr(z^3) = 0 in PG(d,2), prove numerically for d <= 6 that the cross-correlation u = M_Q tau_H is the all-ones vector, and conjecture (Conjecture 24) that this and the resulting minimum distance 2 hold for every d >= 2. For every d >= 2 and every primitive element of GF(2^(d+1)), u is all-ones, every Z_i Z_j with i != j lies in the centralizer and not in the stabilizer row space, and no element of the centralizer outside the stabilizers has weight below 2.",
        H("The q = 2 Singer-quadric qubit codes have minimum distance 2 for every d >= 2"),
        Blocks(
            Node("field", "The field", FieldFormula(),
                "K(d) is the Galois field GF(2^(d+1)), the field K of the paper at q = 2.",
                "K", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("length", "The code length", LengthFormula(),
                "The number of qubits n = (q^(d+1) - 1)/(q - 1) of the paper at q = 2, which is 2^(d+1) - 1, the order of the multiplicative group of K(d).",
                "n", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("trace", "The absolute trace", TraceFormula(),
                "The trace of K(d) over its prime field ZMod 2, the trace Tr from K to F of the paper.",
                "tr", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("tauh", "The hyperplane indicator", HyperplaneFormula(),
                "Appendix A, Step 2: the i-th entry is 1 when the trace of alpha^i vanishes and 0 otherwise, for i in Fin(n(d)). Here ite(c, a, b) is a if c holds and b otherwise.",
                "tauH", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("tauq", "The quadric indicator", QuadricFormula(),
                "Appendix A, Step 3 with xi = q + 1 = 3: the i-th entry is 1 when the trace of alpha^(3i) vanishes and 0 otherwise.",
                "tauQ", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("hz", "The Z block", HzFormula(),
                "H_z = A is the Singer incidence matrix circ(tau_H). Mathlib's circulant(v) has entries v(i - j), with subtraction in Fin(n(d)), the paper's (M)_{i,j} = v_{(i-j) mod n}.",
                "Hz", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("hx", "The X block", HxFormula(),
                "H_x = M_Q A, the product of the quadric circulant M_Q = circ(tau_Q) and A, with matrix multiplication over ZMod 2.",
                "Hx", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("centralizer", "The centralizer", CentralizerFormula(),
                "The paper's centralizer: pairs (a, b) of vectors over ZMod 2 indexed by Fin(n(d)) with a H_x^T = b H_z^T, where a is the Z part and b the X part and vecMul(c, M) is the row vector c times M.",
                "centralizer", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("stabilizers", "The stabilizer row space", StabilizerFormula(),
                "The row space of H = (H_z | H_x): the pairs (c H_z, c H_x) for all row vectors c over ZMod 2.",
                "stabilizers", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("weight", "The symplectic weight", WeightFormula(),
                "The number of positions i at which (a_i, b_i) is not (0, 0), the weight of a Pauli operator. For the weight-two witness it equals the Hamming weight of (a, b), and every lower bound for it is a lower bound for that Hamming weight.",
                "wt", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "Conjecture 24", ClaimFormula(),
                "Proposition 23 for every d >= 2 and every primitive element alpha (an element of order n(d)): u = M_Q tau_H is the all-ones vector; for every pair of distinct positions i, j the operator Z_i Z_j, written (e_i + e_j, 0), lies in the centralizer and not in the stabilizer row space; and every element of the centralizer outside the stabilizers has weight at least 2. Together these give d_min = 2.",
                "claim", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "The q = 2 distance ceiling holds for every d >= 2", Disp(F.Id("claim")),
                "Put m = d + 1 >= 3 and n = 2^m - 1 >= 7. Power sums over the units of K(d) vanish except when n divides the exponent, and no exponent 2^r, 3 2^s or 3 2^s - 2^r with r, s < m is divisible by n: the last would give 2^t = 3 modulo n with t < m. Writing the trace as the sum of the Frobenius powers x^(2^i), the entry u_k is the sum over x in the units of (1 + Tr(x))(1 + Tr(alpha^(3k) x^(-3))); every non-constant term is a multiple of a vanishing power sum and the constant term is n = 1 in ZMod 2, so u is all-ones and H_x is the all-ones matrix. For b != 0, x -> Tr(b x) is a nonzero linear functional, so each of its fibers has 2^(m-1) elements. Every vector in the row space of A has entries c + Tr(b alpha^(-j)), so its weight is 0, n, 2^(m-1) or 2^(m-1) - 1, never 2; hence Z_i Z_j is not a stabilizer, while H_x = J puts it in the centralizer. A centralizer element of weight 1 would make the all-ones vector, a column of A, or its complement zero, but every column of A has weight 2^(m-1) - 1, strictly between 0 and n.",
                "result", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("kulhandjian-hanzo-2026-q2-distance-ceiling"),
                    ResolutionKind.Proved))),
        []));

    private static DocumentBlock Node(
        string id, string title, Formula formula, string prose,
        string declaration, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(
            DescribeId.Create("singerceiling-" + id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(formula), provenance,
            Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Named(name), [.. args]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Equal(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula NotEqual(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.NotEqual, b);
    private static Formula Leq(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Member(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.MemberOf, b);
    private static Formula NotMember(Formula a, Formula b) => new Formula.Not(Parenthesized(Member(a, b)));
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Or(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Or, Parenthesized(b));
    private static Formula Implies(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula Iff(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Iff, Parenthesized(b));
    private static Formula All(Formula a, Formula type, Formula body) =>
        Seq(Forall, Sp, a, Sp, Colon, Sp, type, Comma, Sp, body);
    private static Formula Some(Formula a, Formula type, Formula body) =>
        Seq(Exists, Sp, a, Sp, Colon, Sp, type, Comma, Sp, body);
    private static Formula MinusOf(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula PlusOf(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula TimesOf(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Power(Formula b, Formula e) => Seq(b, Caret, Grp(e));
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Dim() => F.Id("d");
    private static Formula Field() => Call("K", Dim());
    private static Formula Length() => Call("n", Dim());
    private static Formula Two() => Call("ZMod", F.D(2));
    private static Formula Index() => Call("Fin", Length());
    private static Formula Vectors() => Seq(Index(), Sp, To, Sp, Two());
    private static Formula Pairs() => Seq(Parenthesized(Vectors()), Sp, Times, Sp, Parenthesized(Vectors()));
    private static Formula Trace(Formula x) => Call("tr", x);
    private static Formula Primitive() => Alpha;

    private static Formula FieldFormula() =>
        Disp(All(Dim(), Naturals(), Equal(Field(), Call("GaloisField", F.D(2), PlusOf(Dim(), F.D(1))))));

    private static Formula LengthFormula() =>
        Disp(All(Dim(), Naturals(), Equal(Length(), MinusOf(Power(F.D(2), PlusOf(Dim(), F.D(1))), F.D(1)))));

    private static Formula TraceFormula()
    {
        Formula x = F.Id("x");
        return Disp(All(Dim(), Naturals(), All(x, Field(),
            Equal(Trace(x), Call("trace", Two(), Field(), x)))));
    }

    private static Formula Indicator(string name, Formula exponent)
    {
        Formula i = F.Id("i");
        Formula entry = new Formula.Apply(Call(name, Primitive()), [i]);
        Formula value = Call("ite", Equal(Trace(Power(Primitive(), exponent)), F.D(0)), F.D(1), F.D(0));
        return Disp(All(Dim(), Naturals(), All(Primitive(), Field(), All(i, Index(), Equal(entry, value)))));
    }

    private static Formula HyperplaneFormula() => Indicator("tauH", F.Id("i"));

    private static Formula QuadricFormula() => Indicator("tauQ", TimesOf(F.D(3), F.Id("i")));

    private static Formula Circulant(string name) => Call("circulant", Call(name, Primitive()));

    private static Formula HzFormula() =>
        Disp(All(Dim(), Naturals(), All(Primitive(), Field(),
            Equal(Call("Hz", Primitive()), Circulant("tauH")))));

    private static Formula HxFormula() =>
        Disp(All(Dim(), Naturals(), All(Primitive(), Field(),
            Equal(Call("Hx", Primitive()), TimesOf(Circulant("tauQ"), Circulant("tauH"))))));

    private static Formula CentralizerFormula()
    {
        Formula a = F.Id("a"), b = F.Id("b");
        Formula condition = Equal(Call("vecMul", a, Call("transpose", Call("Hx", Primitive()))),
            Call("vecMul", b, Call("transpose", Call("Hz", Primitive()))));
        return Disp(All(Dim(), Naturals(), All(Primitive(), Field(), All(a, Vectors(), All(b, Vectors(),
            Iff(Member(Parenthesized(Seq(a, Comma, Sp, b)), Call("centralizer", Primitive())), condition))))));
    }

    private static Formula StabilizerFormula()
    {
        Formula a = F.Id("a"), b = F.Id("b"), c = F.Id("c");
        Formula span = Some(c, Vectors(), And(Equal(a, Call("vecMul", c, Call("Hz", Primitive()))),
            Equal(b, Call("vecMul", c, Call("Hx", Primitive())))));
        return Disp(All(Dim(), Naturals(), All(Primitive(), Field(), All(a, Vectors(), All(b, Vectors(),
            Iff(Member(Parenthesized(Seq(a, Comma, Sp, b)), Call("stabilizers", Primitive())), span))))));
    }

    private static Formula WeightFormula()
    {
        Formula a = F.Id("a"), b = F.Id("b"), i = F.Id("i");
        Formula support = Call("filter", Seq(i, Sp, Mapsto, Sp,
            Or(NotEqual(new Formula.Apply(a, [i]), F.D(0)), NotEqual(new Formula.Apply(b, [i]), F.D(0)))),
            Call("univ", Index()));
        return Disp(All(Dim(), Naturals(), All(a, Vectors(), All(b, Vectors(),
            Equal(Call("wt", Parenthesized(Seq(a, Comma, Sp, b))), Call("card", support))))));
    }

    private static Formula ClaimFormula()
    {
        Formula i = F.Id("i"), j = F.Id("j"), v = F.Id("v");
        Formula pair = Parenthesized(Seq(PlusOf(Call("single", i, F.D(1)), Call("single", j, F.D(1))), Comma, Sp, F.D(0)));
        Formula u = Equal(Call("mulVec", Circulant("tauQ"), Call("tauH", Primitive())), F.D(1));
        Formula pairs = All(i, Index(), All(j, Index(), Implies(NotEqual(i, j),
            And(Member(pair, Call("centralizer", Primitive())), NotMember(pair, Call("stabilizers", Primitive()))))));
        Formula distance = All(v, Pairs(), Implies(Member(v, Call("centralizer", Primitive())),
            Implies(NotMember(v, Call("stabilizers", Primitive())), Leq(F.D(2), Call("wt", v)))));
        Formula body = Implies(Equal(Call("orderOf", Primitive()), Length()), And(u, And(pairs, distance)));
        return Disp(Iff(F.Id("claim"), All(Dim(), Naturals(), Implies(Leq(F.D(2), Dim()),
            All(Primitive(), Field(), body)))));
    }
}
