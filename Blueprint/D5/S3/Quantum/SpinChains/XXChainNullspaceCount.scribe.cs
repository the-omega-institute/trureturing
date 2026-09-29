using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.SpinChains;

internal sealed class XXChainNullspaceCountDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/SpinChains/XXChainNullspaceCount.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Quantum/posske2026a392387");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For every odd prime p, the number of subsets K of {1, ..., 2p} whose cosines at the angles (2j + (1 + (-1)^|K|)/2) pi/(2p), j in K, sum to zero is 2 (6^((p-1)/2) + 1). By the Jordan-Wigner transformation this count is the dimension of the zero-energy subspace of the periodic spin-1/2 XX Heisenberg chain on 2p sites (OEIS A392387).",
        H("The nullspace of the periodic XX chain on 2p sites has dimension 2(6^((p-1)/2) + 1)"),
        Blocks(
            Node("count", "The zero cosine-sum subsets", CountFormula(),
                "OEIS A392387, COMMENTS: \"Also, the number of subsets K of {1,...,n} such that the sum of cosines of the angles in {(2j + (1 + (-1)^|K|)/2 )*Pi/n | j in K} is zero.\" The entry identifies this number with the dimension of the zero-energy subspace of the periodic spin-1/2 XX Heisenberg chain on n > 1 sites: after the Jordan-Wigner transformation the chain is a system of free fermions whose momenta are 2 j Pi/n for an odd number |K| of fermions and (2 j + 1) Pi/n for an even number, with energy the sum of the cosines. The definition is the subset count; the empty set, whose cosine sum is zero, is counted.",
                "nullspaceCount", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "The conjecture of OEIS A392387", ClaimDefinitionFormula(),
                "OEIS A392387, FORMULA: \"Conjecture: a(2*p) = 2*(6^((p-1)/2)+1) for odd prime p.\" The statement quantifies over every prime p that is odd.",
                "claim", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "The count at twice an odd prime", ClaimFormula(),
                "Write p = 2m + 1, let eta be a primitive p-th root of unity with -eta = exp(i pi/p), and omega = exp(i pi/(2p)), so omega^2 = -eta. A subset K of {1, ..., 2p} is determined by its class-state function w on the residues r modulo p: for each r, which of the two elements of {1, ..., 2p} congruent to r modulo p, one even and one odd, lie in K. With z(r) the number of taken even elements minus the number of taken odd elements of the class r, the cosine sum at the odd-parity angles is the real part of Z = sum_r z(r) eta^r and at the even-parity angles the real part of omega Z. Since the only rational linear relation among 1, eta, ..., eta^(p-1) is that their sum vanishes (the cyclotomic polynomial is the minimal polynomial of eta), the real part of Z vanishes exactly when z(r) + z(-r) = 2 z(0) for all r, and that of omega Z exactly when z(-r) - z(r - 1) = z(0) - z(-1) for all r, which, since r -> -1 - r fixes m, is the symmetry z(r) = z(-1 - r). For odd |K| the first relation forces z to be constantly 1 or constantly -1, the even and the odd elements of {1, ..., 2p}: two subsets. For even |K| the symmetric class-state functions are counted over the fundamental domain 0, ..., m - 1 of r -> -1 - r: each pair of classes has 6 states with equal z, and the parity condition forces the fixed class m to be empty or full, 2 states. The total is 2 + 2 6^m.",
                "result", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("posske-2026-a392387-xx-chain-nullspace-2p"),
                    ResolutionKind.Proved))),
        []));

    private static DocumentBlock Node(
        string id, string title, Formula formula, string prose,
        string declaration, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(
            DescribeId.Create("xx-nullspace-" + id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(formula), provenance,
            Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Named(string name)
    {
        var tokens = new List<Formula>();
        foreach (var part in name.Split('.'))
        {
            if (tokens.Count > 0) tokens.Add(Dot);
            tokens.Add(F.Id(part));
        }
        return Seq(Operatorname, Grp(Seq([.. tokens])));
    }
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Named(name), [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Member(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.MemberOf, right);
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Mul(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula All(string variable, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(variable), domain, body);

    private static Formula CountFormula()
    {
        Formula n = F.Id("n"), k = F.Id("K"), j = F.Id("j");
        Formula sign = new Formula.Power(Parenthesized(new Formula.Negate(D(1))), Call("card", k));
        Formula shift = new Formula.Fraction(Add(D(1), sign), D(2));
        Formula angle = new Formula.Fraction(Mul(Parenthesized(Add(Mul(D(2), j), shift)), Pi), n);
        Formula sum = Seq(Sum, Underscore, Grp(Member(j, k)), Sp, Call("cos", angle));
        Formula subsets = Call("powerset", Call("Icc", D(1), n));
        Formula filtered = Seq(OpenBrace, Member(k, subsets), Sp, Mid, Sp, Equal(sum, D(0)), CloseBrace);
        return Disp(All("n", Naturals(), Equal(Call("nullspaceCount", n), Call("card", filtered))));
    }

    private static Formula ClaimBody()
    {
        Formula p = F.Id("p");
        Formula exponent = Call("NatDiv", Subtract(p, D(1)), D(2));
        Formula value = Mul(D(2), Parenthesized(Add(new Formula.Power(D(6), exponent), D(1))));
        return All("p", Naturals(), Implies(Call("Prime", p),
            Implies(Call("Odd", p), Equal(Call("nullspaceCount", Mul(D(2), p)), value))));
    }

    private static Formula ClaimDefinitionFormula() => Disp(
        new Formula.Logic(F.Id("claim"), FormulaLogicOperator.Iff, Parenthesized(ClaimBody())));

    private static Formula ClaimFormula() => Disp(F.Id("claim"));
}
