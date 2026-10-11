using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.SpinChains;

internal sealed class EclecticTwoWallUniversalityDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumStates/ahn2022eclectic");
    private static Formula A => F.Id("a");
    private static Formula B => F.Id("b");
    private static Formula K => F.Id("k");
    private static Formula Xi => F.Id("xi");
    private static Formula Nats => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Complexes => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula Length => PlusOf(PlusOf(A, B), D(2));
    private static Formula Classes => Call("Fin", Length);
    private static Formula Couplings => new Formula.TypeArrow(Call("Fin", D(3)), Complexes);
    private static Formula Eigenvalue => Call("eigenvalue", A, B, K);
    private static Formula Sector => Call("sector", A, B, K);
    private static Formula X0 => Call("vector3", D(0), D(0), D(1));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every two-wall cyclicity class has maximal hypereclectic power ranks, attained generically by the eclectic operator.",
        H("Two-wall universality in power-rank form"),
        Blocks(
            Paragraph(Text("Work over the complex numbers. A filling contains a letters 1, b letters 2 and two walls 3, so L = a+b+2. Cyclicity indices k range over Fin(L), with val(k) in {0,...,L−1}. The space retains literal periodic words; its cyclicity class is the eigenspace of the one-site right shift. The three coupling coordinates xi(0), xi(1), xi(2) multiply F1, F2, F3, respectively. Thus vector3(0,0,1) is the hypereclectic point with coefficient one on F3.")),
            Node("eigenvalue", "Cyclicity eigenvalue", ABK(Eq(Eigenvalue,
                Call("exp", new Formula.Fraction(Mul(Mul(Mul(D(2), F.Pi), F.Id("i")),
                    Call("val", K)), Length)))), true,
                "The symbol i in the exponential is the imaginary unit. Natural and real scalars in this expression are cast into the complex numbers."),
            Node("sector", "The cyclicity class", ABK(Eq(Sector,
                Call("eigenspace", Call("U", Complexes, A, B), Eigenvalue))), true,
                "This is a complex submodule of Space(C,a,b), including the possibility of a zero-dimensional eigenspace."),
            Node("sectorF", "Restricted bond operators", ABK(All("j", Call("Fin", D(3)),
                Eq(Call("sectorF", A, B, K, F.Id("j")),
                    Call("restrict", Call("F", Complexes, A, B, F.Id("j")), Sector)))), true,
                "Each bond sum commutes with U and therefore preserves the eigenspace. The index 2 selects F3, the literal 21 to 12 bond sum."),
            Node("sectorT", "The restricted eclectic operator", ABK(All("xi", Couplings,
                Eq(Call("sectorT", A, B, K, Xi),
                    Call("restrict", Call("T", Complexes, A, B, Xi), Sector)))), true,
                "The coupled operator also commutes with U. Its restriction is the same linear combination of the three restricted bond sums."),
            Node("claim", "Universality for every filling with a,b at least two",
                Iff(Call("claim"), Universality()), true,
                "§5, Eq. (5.1), arXiv:2112.04506v1: \"we claim a universality hypothesis: The Jordan block spectrum of the eclectic model for generic couplings ξ1, ξ2, ξ3 is identical to that of the hypereclectic model, provided L, M, K satisfy L1 = L−M ≥ K, M1 = M−K ≥ K. (5.1)\" Here K = 2, L = a+b+2 and M = b+2, so the two inequalities become a,b at least two. The statement is the power-rank form: all couplings satisfy an upper bound, and a single polynomial for the filling certifies equality simultaneously in every cyclicity class and every natural power. Normalization at the hypereclectic point implies that this polynomial is nonzero.", true)),
        []));

    private static DocumentBlock.Describe Node(string name, string title, Formula formula,
        bool definition, string prose, bool literature = false) =>
        Describe.Lean(DescribeId.Create("eclectic-two-wall-universality-" + name.ToLowerInvariant()),
            DeclarationHandle.Create("D5/S3/Quantum/SpinChains/EclecticTwoWallUniversality." + name),
            H(title), StatementSource.FromAuthor(Disp(formula)),
            literature ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), definition ? DescribeRole.Definition : DescribeRole.Theorem);

    private static Formula Call(string name, params Formula[] args) => args.Length == 0
        ? Seq(Operatorname, Grp(F.Id(name)))
        : new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. args]);
    private static Formula Parenthesized(Formula x) => Seq(Open, x, Close);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name),
            type is Formula.TypeArrow ? Parenthesized(type) : type, body);
    private static Formula Some(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Eq(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.Equal, y);
    private static Formula Le(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.LessThanOrEqual, y);
    private static Formula Ne(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.NotEqual, y);
    private static Formula And(Formula x, Formula y) => new Formula.Logic(Parenthesized(x), FormulaLogicOperator.And, Parenthesized(y));
    private static Formula Iff(Formula x, Formula y) => new Formula.Logic(Parenthesized(x), FormulaLogicOperator.Iff, Parenthesized(y));
    private static Formula Implies(Formula x, Formula y) => new Formula.Logic(Parenthesized(x), FormulaLogicOperator.Implies, Parenthesized(y));
    private static Formula Mul(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Multiply, y);
    private static Formula PlusOf(Formula x, Formula y) => Seq(x, Sp, Plus, Sp, y);
    private static Formula AB(Formula body) => All("a", Nats, All("b", Nats, body));
    private static Formula ABK(Formula body) => AB(All("k", Classes, body));
    private static Formula Rank(Formula op) => Call("finrank", Complexes,
        Call("range", new Formula.Power(Parenthesized(op), F.Id("r"))));
    private static Formula Universality()
    {
        var t = Rank(Call("sectorT", A, B, K, Xi));
        var f = Rank(Call("sectorF", A, B, K, D(2)));
        var upper = All("xi", Couplings, All("k", Classes, All("r", Nats, Le(t, f))));
        var p = F.Id("P");
        var generic = Some("P", Call("MvPolynomial", Call("Fin", D(3)), Complexes),
            And(Eq(Call("eval", X0, p), D(1)), All("xi", Couplings,
                Implies(Ne(Call("eval", Xi, p), D(0)),
                    All("k", Classes, All("r", Nats, Eq(t, f)))))));
        return AB(Implies(Le(D(2), A), Implies(Le(D(2), B), And(upper, generic))));
    }
}
