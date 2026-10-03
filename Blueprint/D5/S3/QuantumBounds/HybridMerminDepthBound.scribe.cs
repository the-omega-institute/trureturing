using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuantumBounds;

internal sealed class HybridMerminDepthBoundDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/QuantumBounds/HybridMerminDepthBound.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumBounds/bernards2023nonlocalitydepth");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The sharp Bernards--Gühne classical bound holds for two cells of arbitrary sizes k,m >= 2, including the conjectured range m > 2.",
        H("Bernards--Gühne hybrid classical bound"),
        Blocks(
            Node("phase", "The sign in the Bell functional", PhaseFormula(),
                "The sign is (-1)^(1+ceil(h/2)), as in Eq. (28), PDF p. 5. NatDiv(a,b) denotes natural-number division, rounded down; hence NatDiv(h+1,2) is ceil(h/2). The values at residues 0,1,2,3 modulo 4 are respectively -1,1,1,-1.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("hybridValue", "Two arbitrary deterministic cell responses", HybridFormula(),
                "Section II, PDF p. 2, states: “Every cell c_i of the partition is considered as one system. The measurement settings are all combinations of measurement settings that apply to each subsystem within a cell. However, no restrictions apply to the correlations between subsystems within a cell, since the cell is regarded as one system. In particular, this allows for signaling to take place between the parties within one cell.” A Boolean setting string uses false for setting 1 and true for setting 2. hammingDist(x,const(Fin k,false)) counts its true coordinates. const(T,b) is the standard Function.const T b, the constant-b function on T. Fin k labels the k parties by 0,...,k-1. Thus the product of the outcomes of a cell may be any function of that cell's entire setting string. Integer units encode exactly the outcomes +1 and -1; val takes their integer value and IntCast embeds a natural number in the integers. Section II, PDF p. 3, defines M_h by Eq. (11) as the convex hull of the local models of the partitions with cardinality tuple h. A linear functional has the same maximum over this convex hull as over its deterministic points. The same page states: “where ’party permutations’ only includes permutations that yield different terms.” In particular (1122) consists of six terms. Accordingly each Boolean string occurs once in the displayed double sum; the string of weight zero contributes zero. The paper considers inequalities symmetric under permutation of the parties, so changing the assignment of parties to the two cells leaves F_n unchanged.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "The conjectured sharp classical bound", ClaimFormula(),
                "Section III.F, Eq. (28), PDF p. 5, displays: “F_n = ∑_{ℓ=1}^n (−1)^{1+⌈ℓ/2⌉} ℓ (1…1 2…2) ≤ n 2^{n−2}.” The bracket has n−ℓ settings labelled 1 and ℓ settings labelled 2 and sums over distinct permutations. Section V, PDF p. 8, states verbatim: “For (k, m) models with m > 2, we have a conjecture for the classical bound. Proving this bound or finding a counterexample remains an open problem.” The encoded sizes satisfy n=k+m and k,m >= 2; IsGreatest states both universal boundedness and attainment. NatSub is truncated natural-number subtraction, and all sums are finite sums over the indicated finite types.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "The maximum is attained and equals the bound", Disp(F.Id("claim")),
                "Distribute the weight over the k+m marked coordinates. Fixing a marked coordinate to true removes it and replaces the sign s(h+1) by t(h)=(-1)^NatDiv(h,2). Both remaining cells are nonempty because k,m >= 2. Fix all but one setting in each of these cells. Each resulting four-term block is a CHSH expression up to local sign changes, so its absolute value is at most 2. There are 2^(r+s-2) such blocks for remaining cell sizes r,s; their sum is at most 2^(r+s-1). Each marked-coordinate contribution is therefore at most 2^(k+m-2). The responses A(x)=t(hammingDist(x,const(Fin k,false))) and B(y)=t(hammingDist(y,const(Fin m,false))) make every four-term block equal to 2, attaining all marked-coordinate bounds simultaneously. The exact sharp value follows. The formal assertion concerns the deterministic correlator functional; the passage to the convex hybrid model uses the linearity and symmetry described above. Models with a singleton cell and sharp bounds for more cells are outside this assertion.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("bernards-guhne-2022-hybrid-nonlocality-depth-bound"),
                    ResolutionKind.Proved))),
        []));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
        DescribeId.Create("hybrid-mermin-" + name.ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
        provenance, Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(F.Id(name), [.. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Ex(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Equal(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula LessEq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Logic(Formula a, FormulaLogicOperator op, Formula b) =>
        new Formula.Logic(Parenthesized(a), op, Parenthesized(b));
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Nats() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Ints() => Seq(Mathbb, Grp(F.Id("Z")));
    private static Formula Settings(Formula n) => Parenthesized(new Formula.TypeArrow(Call("Fin", n), F.Id("Bool")));
    private static Formula Responses(Formula n) => Parenthesized(new Formula.TypeArrow(Settings(n), Call("Units", Ints())));
    private static Formula Summation(string name, Formula type, Formula body) =>
        Seq(Sum, Underscore, Grp(F.Id(name), Colon, type), Sp, Parenthesized(body));

    private static Formula PhaseFormula()
    {
        Formula h = F.Id("h");
        return Disp(All("h", Nats(), Equal(Call("phase", h),
            new Formula.Power(Parenthesized(new Formula.Negate(D(1))),
                Add(D(1), Call("NatDiv", Add(h, D(1)), D(2)))))));
    }

    private static Formula HybridFormula()
    {
        Formula k = F.Id("k"), m = F.Id("m"), x = F.Id("x"), y = F.Id("y");
        Formula weight = Add(Call("hammingDist", x, Call("const", Call("Fin", k), F.Id("false"))), Call("hammingDist", y, Call("const", Call("Fin", m), F.Id("false"))));
        Formula value = Mul(Mul(Mul(Call("IntCast", weight), Call("phase", weight)),
            Call("val", Call("A", x))), Call("val", Call("B", y)));
        return Disp(All("k", Nats(), All("m", Nats(), All("A", Responses(k), All("B", Responses(m),
            Equal(Call("hybridValue", k, m, F.Id("A"), F.Id("B")),
                Summation("x", Settings(k), Summation("y", Settings(m), value))))))));
    }

    private static Formula ClaimFormula()
    {
        Formula k = F.Id("k"), m = F.Id("m"), v = F.Id("v");
        Formula membership = Ex("A", Responses(k), Ex("B", Responses(m),
            Equal(v, Call("hybridValue", k, m, F.Id("A"), F.Id("B")))));
        Formula set = Seq(OpenBrace, v, Colon, Ints(), Sp, Mid, Sp, membership, CloseBrace);
        Formula n = Add(k, m);
        Formula maximum = Call("IntCast", Mul(Parenthesized(n),
            new Formula.Power(D(2), Call("NatSub", n, D(2)))));
        Formula assertion = All("k", Nats(), All("m", Nats(),
            Logic(LessEq(D(2), k), FormulaLogicOperator.Implies,
                Logic(LessEq(D(2), m), FormulaLogicOperator.Implies, Call("IsGreatest", set, maximum)))));
        return Disp(Logic(F.Id("claim"), FormulaLogicOperator.Iff, assertion));
    }
}
