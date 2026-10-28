using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence;

internal sealed class MatveevaGlobalBoundednessDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S1/Recurrence/MatveevaGlobalBoundedness";
    private static LibraryNoteRef Source => LibraryNoteRef.Create("D5/L/RecurrenceComposition/matveeva2025precursive");
    private static Formula Nats => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Rats => Seq(Mathbb, Grp(F.Id("Q")));
    private static Formula Ints => Seq(Mathbb, Grp(F.Id("Z")));
    private static Formula Reals => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Complexes => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula Sequence => Seq(Nats, To, Rats);
    private static Formula S => F.Id("s");
    private static Formula N => F.Id("n");
    private static Formula C => F.Id("C");
    private static Formula R => F.Id("R");
    private static Formula Z => F.Id("z");
    private static Formula K => F.Id("k");
    private static Formula Aone => Seq(F.Id("a"), Underscore, Grp(D(1)));
    private static Formula Atwo => Seq(F.Id("a"), Underscore, Grp(D(2)));
    private static Formula Bzero => Seq(F.Id("b"), Underscore, Grp(D(0)));
    private static Formula Bone => Seq(F.Id("b"), Underscore, Grp(D(1)));
    private static Formula Btwo => Seq(F.Id("b"), Underscore, Grp(D(2)));
    private static Formula Par(Formula f) => Seq(Left, Open, f, Right, Close);
    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, Formula arg) => Seq(Named(name), Par(arg));
    private static Formula At(Formula s, Formula index) => Seq(s, Par(index));
    private static Formula Cast(Formula f, Formula type) => Par(Seq(f, Colon, type));
    private static Formula All(Formula v, Formula type, Formula body) => Seq(Forall, Sp, v, Colon, type, Comma, Sp, body);
    private static Formula Some(Formula v, Formula type, Formula body) => Seq(Exists, Sp, v, Colon, type, Comma, Sp, body);
    private static Formula Pow(Formula f, Formula n) => new Formula.Power(f, n);
    private static Formula Norm(Formula f) => Seq(Vert, Sp, f, Vert, Sp);
    private static Formula Scaling => All(S, Sequence, Seq(Call("integralScaling", S), Iff, Par(
        Some(C, Ints, Seq(C, Neq, Sp, D(0), Sp, Land, Sp,
            Par(All(N, Nats, Seq(D(1), Le, N, Implies, Sp,
                Some(K, Ints, Seq(Pow(Cast(C, Rats), N), Cdot, Sp, At(S, N), Eq, Cast(K, Rats)))))))))));
    private static Formula Radius => All(S, Sequence, Seq(Call("positiveComplexRadius", S), Iff, Par(
        Some(R, Reals, Seq(D(0), Lt, R, Sp, Land, Sp,
            Par(All(Z, Complexes, Seq(Norm(Z), Lt, R, Implies, Sp,
                Call("Summable", Par(Seq(N, Colon, Nats, Mapsto,
                    Cast(At(S, N), Complexes), Cdot, Sp, Pow(Z, N))))))))))));
    private static Formula Bounded => All(S, Sequence, Seq(Call("globallyBounded", S), Iff,
        Par(Seq(Call("integralScaling", S), Sp, Land, Sp, Call("positiveComplexRadius", S)))));
    private static Formula Recurrence => All(N, Nats, Seq(D(2), Le, N, Implies, Sp,
        Par(Seq(Cast(N, Rats), Plus, Bzero)), Cdot, Sp, At(S, N), Plus,
        Par(Seq(Aone, Cdot, Sp, Cast(N, Rats), Plus, Bone)), Cdot, Sp, At(S, Seq(N, Minus, D(1))), Plus,
        Par(Seq(Atwo, Cdot, Sp, Cast(N, Rats), Plus, Btwo)), Cdot, Sp, At(S, Seq(N, Minus, D(2))), Eq, D(0)));
    private static Formula Expression => Seq(Aone, Cdot, Sp, Atwo, Cdot, Sp, Bzero, Plus,
        Aone, Cdot, Sp, Btwo, Minus, D(2), Cdot, Sp, Atwo, Cdot, Sp, Bone);
    private static Formula ClaimBody => All(Seq(Aone, Sp, Atwo, Sp, Bzero, Sp, Bone, Sp, Btwo), Rats,
        Seq(Aone, Neq, Sp, D(0), Implies, Sp, Atwo, Neq, Sp, D(0), Implies, Sp,
            Par(All(N, Nats, Seq(D(2), Le, N, Implies, Sp, Bzero, Neq, Sp, Minus, Cast(N, Rats)))), Implies, Sp,
            All(S, Sequence, Seq(Par(Recurrence), Implies, Sp, Expression, Neq, Sp, D(0), Implies, Sp,
                Neg, Sp, Call("globallyBounded", S)))));
    private static Formula Claim => Seq(Named("claim"), Iff, Par(ClaimBody));
    private static Formula Witness => All(N, Nats, Seq(Call("witness", N), Eq, Cast(N, Rats), Plus, D(1)));
    private static Formula Result => Seq(Neg, Sp, Named("claim"));

    private static ScribeNode Description(string id, string declaration, string title, Formula formula,
        string prose, bool definition = true) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Module + "." + declaration), H(title),
            StatementSource.FromAuthor(Disp(formula)),
            definition && declaration != "witness" ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), definition ? DescribeRole.Definition : DescribeRole.Theorem);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A rational linear solution contradicts the literal nonzero-parameter assertion about global boundedness.",
        H("Matveeva's Literal Global Boundedness Claim"),
        Blocks(
            Description("integral-scaling", "integralScaling", "Integral scaling of positive coefficients", Scaling,
                "A single nonzero integer C clears all positive-index coefficients after scaling the variable. The integer k may depend on n. No integrality condition is imposed on the constant coefficient. This is Definition 1.4."),
            Description("positive-complex-radius", "positiveComplexRadius", "Summability on a positive complex disk", Radius,
                "A positive real R gives summability of the entire complex series at every z of norm less than R. The natural summation index includes zero. This expresses the convergence clause of Definition 1.5."),
            Description("global-boundedness", "globallyBounded", "The two clauses of global boundedness", Bounded,
                "Global boundedness is the conjunction of integral scaling and a positive complex radius, as in Definition 1.5."),
            Description("literal-claim", "claim", "The full rational-parameter assertion", Claim,
                "All five parameters are rational, a1 and a2 are nonzero, and b0 excludes every negative integer at most minus two. Every rational sequence is allowed, with arbitrary rational initial pair. The recurrence holds at every natural n at least two. The only further hypothesis is that a1*a2*b0 + a1*b2 - 2*a2*b1 is nonzero. Section 4.2 and the explicit inequality in Section 7 give this literal parameter reading. No minimal order, nonrationality, normalized initial values, or persistence of an exponential after simplification is required. Subtraction in sequence indices is natural subtraction."),
            Description("linear-sequence", "witness", "The rational sequence n plus one", Witness,
                "At natural index n the rational coefficient is n plus one. Its initial values are one and two."),
            Description("literal-refutation", "result", "Negation of the entire literal claim", Result,
                "Take (b0, a1, b1, a2, b2) = (1, -3, -1, 2, 1) and s(n) = n + 1. The recurrence becomes (n+1)^2 + (-3*n-1)*n + (2*n+1)*(n-1) = 0 for every n at least two. The parameter expression is minus five. Integral scaling uses C = 1 and integer coefficient n + 1 at every positive index. The complex series is summable for every z of norm less than R = 1, by the k = 1 complex instance of summable_choose_mul_geometric_of_norm_lt_one. These facts contradict the universally quantified conclusion. The result concerns the literal parameter condition; Conjecture 4.1 is a separate assertion. A requirement that an exponential survive simplification would define a different claim.", false))));
}
