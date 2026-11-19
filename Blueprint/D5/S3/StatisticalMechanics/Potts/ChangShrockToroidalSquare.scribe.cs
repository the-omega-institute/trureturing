using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.Potts;

internal sealed class ChangShrockToroidalSquareDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/StatisticalMechanics/Potts/ChangShrockToroidalSquare.";
    private static LibraryNoteRef Source =>
        LibraryNoteRef.Create("D5/L/Eigenstructure/changshrock2005toroidal");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every native toroidal square degree L-1 block has eigenvalue v^(L-1)(v+q).",
        H("An alternating vector for toroidal square strips"),
        Blocks(
            Paragraph(Text(
                "The coefficient ring, native labelled states, join and detach maps, vertical "
                + "operator and alternating vector are those of "
                + "D5.S3.StatisticalMechanics.Potts.ChangShrockToroidalHoneycomb. "
                + "In the formulas their original declaration names retain that namespace. "
                + "Coeff is MvPolynomial (Fin 2) ℤ; q and v are respectively "
                + "MvPolynomial.X 0 and MvPolynomial.X 1. Space L is State L →₀ Coeff. "
                + "All products act by composition of Coeff-linear endomorphisms.")),
            Describe.Lean(DescribeId.Create("horizontal"),
                DeclarationHandle.Create(Prefix + "horizontal"), H("All cyclic bonds"),
                StatementSource.FromAuthor(Disp(Width(Eq(Call("horizontal", X("L")),
                    At(Q("List", "prod"), At(Q("List", "ofFn"),
                        Fn("i", Sites(), Add(D(1), Smul(N("v"), Call("join", X("i"),
                            At(Q("Fin", "ofNat"), X("L"),
                                Add(Val(X("i")), D(1))))))))))))),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "This is H in equation (2.34). The function bound by List.ofFn has domain "
                    + "Fin L and codomain Module.End Coeff (Space L). Its 1 is the identity "
                    + "endomorphism. HSMul.hSMul is scalar multiplication, and Fin.val is "
                    + "the explicit coercion of a site to ℕ. Fin.ofNat L n has value "
                    + "Nat.mod n L, the nonnegative remainder. Thus the last factor joins "
                    + "L-1 to 0. List.prod retains increasing site order and all L factors. "
                    + "At L=2 the two endpoint pairs are reversed descriptions of the same "
                    + "bond; both factors are retained. Nat.div is natural quotient "
                    + "division; no quotient or half-width convention enters this H."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("transfer"),
                DeclarationHandle.Create(Prefix + "transfer"), H("The square transfer map"),
                StatementSource.FromAuthor(Disp(Width(Eq(Call("transfer", X("L")),
                    Mul(Call("vertical", X("L")), Call("horizontal", X("L"))))))),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "Equation (2.35) gives T=VH. Multiplication in Module.End is composition, "
                    + "so H acts first. The reused vertical operator is literally "
                    + "List.prod (List.ofFn (fun i : Fin L => v • 1 + detach i)). "
                    + "The operators act on the full native labelled degree L-1 space, "
                    + "including adjacent marked double blocks."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("result"),
                DeclarationHandle.Create(Prefix + "result"), H("The eigenvalue at every width"),
                StatementSource.FromAuthor(Disp(All("L", Nat(), Arrow(
                    new Formula.Relation(D(2), FormulaRelationOperator.LessThanOrEqual, X("L")),
                    Ex("w", Call("Space", X("L")), And(Ne(X("w"), D(0)),
                        Eq(At(Call("transfer", X("L")), X("w")),
                            Smul(Mul(Power(N("v"), Sub(X("L"), D(1))),
                                Add(N("v"), N("q"))), X("w"))))))))),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "The premise 2 ≤ L supplies the local NeZero L instance in the Lean "
                        + "statement. Natural subtraction L-1 is therefore ordinary predecessor "
                        + "subtraction. The witness is the original alternatingVector L. "
                        + "Its identity-permutation coefficient is one, so "
                        + "alternatingVector_ne_zero supplies nonzeroness over ℤ[q,v].")),
                    Paragraph(Text(
                        "For every i : Fin L, i differs from Fin.ofNat L (i.val+1): "
                        + "away from the seam their values differ by one; at the seam the "
                        + "values are L-1 and zero. The owner theorem join_alternating "
                        + "therefore annihilates the witness at every cyclic bond, for odd "
                        + "and even L alike. Every factor of H fixes it. Applying the owner "
                        + "list_prod_on_vector with constant scalar one proves H fixes it, "
                        + "including both factors at width two.")),
                    Paragraph(Text(
                        "The owner theorem vertical_alternating gives "
                        + "Vw=v^(L-1)(v+q) • w. Together with H w=w this proves the displayed "
                        + "statement. Equation (5.18) expresses the corresponding Tutte "
                        + "eigenvalue x; equation (5.21) gives precisely this Potts form. "
                        + "The polynomial theorem uses no division or specialization. "
                        + "It makes no claim about amplitudes or the second eigenvalue y."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("changshrock2005square"), ResolutionKind.Proved)))));

    private static Formula Width(Formula body) => All("L", Nat(),
        Seq(OpenBracket, Call("NeZero", X("L")), CloseBracket, Sp, body));
    private static Formula Sites() => Call("Fin", X("L"));
    private static Formula Nat() => Seq(Mathbb, Grp(X("N")));
    private static Formula X(string name) => F.Id(name);
    private static Formula N(string name) => Seq(Operatorname, Grp(X(name)));
    private static Formula Call(string name, params Formula[] args) => At(N(name), args);
    private static Formula Q(params string[] parts) => Seq(parts.SelectMany((part, index) =>
        index == 0 ? new[] { N(part) } : new[] { Dot, N(part) }).ToArray());
    private static Formula At(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula Val(Formula f) => At(Q("Fin", "val"), f);
    private static Formula Smul(Formula a, Formula b) => At(Q("HSMul", "hSMul"), a, b);
    private static Formula Parenthesized(Formula f) => Seq(Open, f, Close);
    private static Formula Eq(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Ne(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.NotEqual, b);
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Arrow(Formula a, Formula b) =>
        new Formula.TypeArrow(Parenthesized(a), Parenthesized(b));
    private static Formula Add(Formula a, Formula b) =>
        new Formula.Binary(Parenthesized(a), FormulaBinaryOperator.Add, Parenthesized(b));
    private static Formula Sub(Formula a, Formula b) =>
        new Formula.Binary(Parenthesized(a), FormulaBinaryOperator.Subtract, Parenthesized(b));
    private static Formula Mul(Formula a, Formula b) =>
        new Formula.Binary(Parenthesized(a), FormulaBinaryOperator.Multiply, Parenthesized(b));
    private static Formula Power(Formula a, Formula b) =>
        new Formula.Power(Parenthesized(a), Parenthesized(b));
    private static Formula Bound(string name, Formula type) =>
        Parenthesized(Seq(X(name), Colon, Sp, type));
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Bound(name, type), Comma, Sp, Parenthesized(body));
    private static Formula Ex(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, Bound(name, type), Comma, Sp, Parenthesized(body));
    private static Formula Fn(string name, Formula type, Formula body) =>
        Parenthesized(Seq(Bound(name, type), Sp, Mapsto, Sp, body));
}
