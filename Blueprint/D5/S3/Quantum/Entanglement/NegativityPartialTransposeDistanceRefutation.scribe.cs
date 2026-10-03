using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement;

internal sealed class NegativityPartialTransposeDistanceRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/NegativityPartialTransposeDistanceRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumStates/ganardi2022hierarchy");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Ganardi, Miller, Paterek and Zukowski (arXiv:2111.11887, Quantum 6, 654) conjecture that the partial transpose distance d_T(rho, sigma) = ||rho^{T_B} - sigma^{T_B}||_1 / 2 from every state rho to the PPT states has infimum equal to the negativity N(rho) = (||rho^{T_B}||_1 - 1)/2. The equality fails: a rank-five two-qutrit state has negativity 1/34, while its distance to every PPT state is at least 2/51.",
        H("Negativity is not the partial transpose distance to the PPT states"),
        Blocks(
            Node("claim", "The conjectured equality", ClaimFormula(),
                "For a state rho on C^d (x) C^d, rho^{T_B} is the partial transposition on the second factor (the existing partialTransposeB) and ||A||_1 = Re Tr sqrt(A^dagger A) is the existing trace norm. The partial transpose distance is d_T(rho, sigma) = ||rho^{T_B} - sigma^{T_B}||_1 / 2, the PPT states are the density matrices sigma with sigma^{T_B} positive semidefinite, and the negativity is N(rho) = (||rho^{T_B}||_1 - 1)/2. Conjecture 1 of the paper states that the infimum of d_T(rho, sigma) over the PPT states equals N(rho) for every density matrix rho; the displayed statement is its case of equal local dimensions.",
                "claim", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("witness", "The counterexample state", WitnessFormula(),
                "The state is R/34 on two qutrits, with R = |v><v| + 4 (|02><02| + |20><20| + |12><12| + |21><21|) and v = |00> + |11> + 4 |22>. It is positive semidefinite with trace one and rank five.",
                "witness", DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("result", "The conjectured equality fails", Disp(new Formula.Not(F.Id("claim"))),
                "Let c = |01> - |10>. The partial transpose of the state is P - |c><c|/68, where P is a sum of positive rank-one and diagonal terms of trace 35/34, so the triangle inequality bounds its trace norm by 36/34 and the negativity by 1/34. The matrices U_1 (the signs -1 on 00, 01, 10, 11, 22 and +1 on 02, 20, 12, 21), U_2 (equal to -1 except for the swaps of 02 with 20 and of 12 with 21) and U_3 (equal to U_2 except for +1 on 22) are unitary, so Re Tr(U_k X) is at most ||X||_1 for every X, and so is Re Tr(F X) for F = U_1/3 + U_2/6 + U_3/2. Against the partial transpose of the state, F has trace 7/17. With b = 2|00> + 2|11> - |22>, every matrix sigma satisfies Tr(F sigma^{T_B}) = Tr(sigma)/3 - <b|sigma|b>/3 - 4<c|sigma^{T_B}|c>/3, so for every PPT state the real part is at most 1/3. Hence the partial transpose distance to every PPT state is at least (7/17 - 1/3)/2 = 2/51, the set of PPT states contains |00><00|, and the infimum is at least 2/51 > 1/34.",
                "result", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("ganardi-2022-negativity-ppt-distance"),
                    ResolutionKind.Refuted))),
        []));

    private static DocumentBlock Node(
        string id, string title, Formula formula, string prose,
        string declaration, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(
            DescribeId.Create("nptd-" + id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(formula), provenance,
            Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula Named(Formula name) => Seq(Operatorname, Grp(name));
    private static Formula Call(Formula name, params Formula[] arguments) =>
        new Formula.Apply(Named(name), [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Rel(Formula left, FormulaRelationOperator op, Formula right) =>
        new Formula.Relation(left, op, right);
    private static Formula EqTo(Formula left, Formula right) =>
        Rel(left, FormulaRelationOperator.Equal, right);
    private static Formula Logic(Formula left, FormulaLogicOperator op, Formula right) =>
        new Formula.Logic(Parenthesized(left), op, Parenthesized(right));
    private static Formula Imp(Formula left, Formula right) =>
        Logic(left, FormulaLogicOperator.Implies, right);
    private static Formula And(Formula left, Formula right) =>
        Logic(left, FormulaLogicOperator.And, right);
    private static Formula All(Formula variable, Formula domain, Formula body) =>
        Seq(Forall, Sp, variable, Sp, Colon, Sp, domain, Comma, Sp, body);
    private static Formula Some(Formula variable, Formula domain, Formula body) =>
        Seq(Exists, Sp, variable, Sp, Colon, Sp, domain, Comma, Sp, body);
    private static Formula Sub(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Mul(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Frac(Formula top, Formula bottom) => new Formula.Fraction(top, bottom);
    private static Formula NumberSet(Formula name) => Seq(Mathbb, Grp(name));
    private static Formula Pairs(Formula d) =>
        Seq(Call(F.Id("Fin"), d), Sp, F.Times, Sp, Call(F.Id("Fin"), d));
    private static Formula Square(Formula d) =>
        Call(F.Id("Matrix"), Parenthesized(Pairs(d)), Parenthesized(Pairs(d)),
            NumberSet(F.Id("C")));
    private static Formula Pt(Formula x) => Call(F.Id("partialTransposeB"), x);
    private static Formula TraceNorm(Formula x) => Call(F.Id("traceNorm"), x);
    private static Formula Ket(Formula index) => Seq(Bar, index, Rangle);
    private static Formula Bra(Formula index) => Seq(Langle, index, Bar);
    private static Formula Proj(Formula index) => Seq(Ket(index), Bra(index));

    private static Formula ClaimFormula()
    {
        Formula d = F.Id("d"), rho = F.Id("rho"), sigma = F.Id("sigma"), t = F.Id("t");
        Formula distance = Frac(TraceNorm(Sub(Pt(rho), Pt(sigma))), D(2));
        Formula condition = Some(sigma, Square(d),
            And(Call(F.Id("IsDensity"), sigma),
                And(Call(F.Id("PosSemidef"), Pt(sigma)), EqTo(t, distance))));
        Formula set = Seq(Esc, OpenBrace, t, Sp, Mid, Sp, condition, Esc, CloseBrace);
        Formula negativity = Frac(Sub(TraceNorm(Pt(rho)), D(1)), D(2));
        Formula body = Imp(Call(F.Id("IsDensity"), rho),
            EqTo(Call(F.Id("sInf"), set), negativity));
        return Disp(Logic(F.Id("claim"), FormulaLogicOperator.Iff,
            All(d, NumberSet(F.Id("N")), All(rho, Square(d), body))));
    }

    private static Formula WitnessFormula()
    {
        Formula kets = Add(Add(Ket(D(0, 0)), Ket(D(1, 1))), Mul(D(4), Ket(D(2, 2))));
        Formula bras = Add(Add(Bra(D(0, 0)), Bra(D(1, 1))), Mul(D(4), Bra(D(2, 2))));
        Formula diagonal = Add(Add(Add(Proj(D(0, 2)), Proj(D(2, 0))), Proj(D(1, 2))),
            Proj(D(2, 1)));
        Formula r = Add(Seq(Parenthesized(kets), Parenthesized(bras)),
            Mul(D(4), Parenthesized(diagonal)));
        return Disp(EqTo(F.Id("witness"), Mul(Frac(D(1), D(3, 4)), Parenthesized(r))));
    }
}
