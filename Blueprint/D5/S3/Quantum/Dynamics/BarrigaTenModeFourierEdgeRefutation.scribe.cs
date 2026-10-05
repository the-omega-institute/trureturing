using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Dynamics;

internal sealed class BarrigaTenModeFourierEdgeRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Dynamics/BarrigaTenModeFourierEdgeRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumChannels/barriga2026dftbosonic");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Barriga et al. (arXiv:2609.05644) realize the discrete Fourier transform F_N with one waveguide array, Phi_out exp(-i H) Phi_in = F_N, and conjecture edge ranges for the coupling graphs; for N = 10 their third conjecture, with l = 5, requires at least 25 edges. A connected real symmetric coupling matrix with nonnegative couplings and 23 edges realizes F_10 exactly, so the bound fails.",
        H("A 23-edge coupling realizes the ten-mode Fourier transform"),
        Blocks(
            Node("fourier", "The ten-mode Fourier transform", FourierFormula(),
                "The discrete Fourier transform on ten modes, with entries exp(-2 pi i x y / 10) / sqrt 10 for x, y in Fin 10, the paper's F_N with omega = exp(-2 i pi / N).",
                "F10", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("edges", "Number of edges", EdgeCountFormula(),
                "The number of unordered pairs x < y of modes with a nonzero coupling H x y: the edges of the coupling graph, whose vertices are the waveguides.",
                "edgeCount", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("graph", "The coupling graph", GraphFormula(),
                "The simple graph on Fin 10 in which distinct modes x and y are adjacent when H x y or H y x is nonzero.",
                "supportGraph", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("phases", "Phase shifters", PhaseFormula(),
                "A diagonal matrix whose diagonal entries are complex numbers of modulus 1, the input and output phase shifters of the paper.",
                "IsUnimodularDiagonal", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "The conjectured bound for N = 10", ClaimFormula(),
                "The third conjecture of the paper for N = 10 with l = 5, read for the most restrictive notion of solution: every real symmetric coupling matrix with nonnegative off-diagonal entries and connected coupling graph whose propagator exp(-i H) gives F10 after input and output phase shifters has at least 25 edges. The propagator is the frozen hamiltonianPropagator at time 1, applied to the complex matrix map(H, ofReal) obtained by casting each real entry of H to a complex number.",
                "claim", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "The bound fails", Disp(new Formula.Not(F.Id("claim"))),
                "Let s = sqrt 5 and let C0 be the symmetric circulant on Z_5 with a = pi (35 - 13 s)/25 at distance 1 and b = pi (35 + 13 s)/25 at distance 2. Its Fourier eigenvalues are 28 pi/5, -4 pi, 6 pi/5, 6 pi/5 and -4 pi, so exp(-i C0) has entries (w/sqrt 5) w^(4 (j - k)^2) with w = exp(2 pi i/5). With q = (21 s - 65)/20 and g = q + i sqrt(1 - q^2), the matrix P with entries (Re(g w^(j + k - 1)) + cos(2 pi (j - k)/5))/5 is a rank-one projector onto a vector of the -4 pi eigenspace. Hence K = C0 + 2 pi P commutes with C0 and exp(-i K) = exp(-i C0) exp(-2 pi i P) = exp(-i C0). The value of q makes K 0 1 = 0, and every other off-diagonal entry of K is positive. Through x -> (x mod 2, x mod 5) the ten-mode matrix is H = (pi/4) X (x) I + I (x) K. Its exponential is w D F10 D for the unimodular diagonal D with entries (-i)^(x mod 2) w^(4 (x mod 5)^2), by the congruence 5ab + 4jk = -xy mod 10. The coupling graph consists of the cliques on the even and on the odd modes without the edges {0, 6} and {1, 5}, together with the five edges {x, x + 5}. It is connected and has 23 < 25 edges.",
                "result", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("barriga-2026-dft-ten-mode-edge-bound"),
                    ResolutionKind.Refuted))),
        []));

    private static DocumentBlock Node(
        string id, string title, Formula formula, string prose,
        string declaration, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(
            DescribeId.Create("dftten-" + id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(formula), provenance,
            Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Named(name), [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula NotEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);
    private static Formula Less(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula LessEq(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);
    private static Formula Or(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Or, right);
    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Iff, Parenthesized(right));
    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula All(string variable, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(variable), domain, body);
    private static Formula Some(string variable, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(variable), domain, body);
    private static Formula Modes() => Call("Fin", D(1, 0));
    private static Formula RealMatrices() => Call("Matrix", Modes(), Modes(), Seq(Mathbb, Grp(F.Id("R"))));
    private static Formula ComplexMatrices() => Call("Matrix", Modes(), Modes(), Seq(Mathbb, Grp(F.Id("C"))));
    private static Formula Entry(Formula m, Formula x, Formula y) => new Formula.Apply(m, [x, y]);

    private static Formula FourierFormula()
    {
        Formula x = F.Id("x"), y = F.Id("y");
        Formula exponent = new Formula.Negate(Seq(D(2), Pi, Sp, F.Id("i"), Sp, x, Sp, y, Sp, Slash, Sp, D(1, 0)));
        Formula value = Seq(Call("exp", exponent), Sp, Slash, Sp, Call("sqrt", D(1, 0)));
        return Disp(All("x", Modes(), All("y", Modes(), Equal(Entry(Named("F10"), x, y), value))));
    }

    private static Formula EdgeCountFormula()
    {
        Formula h = F.Id("H"), x = F.Id("x"), y = F.Id("y");
        Formula pairs = Call("filter", Seq(Open, x, Comma, Sp, y, Close, Sp, Mapsto, Sp,
            And(Less(x, y), NotEqual(Entry(h, x, y), D(0)))), Call("univ", Seq(Modes(), Sp, Times, Sp, Modes())));
        return Disp(All("H", RealMatrices(), Equal(Call("edgeCount", h), Call("card", pairs))));
    }

    private static Formula GraphFormula()
    {
        Formula h = F.Id("H"), x = F.Id("x"), y = F.Id("y");
        Formula adjacency = Iff(Call("Adj", Call("supportGraph", h), x, y),
            And(NotEqual(x, y), Or(NotEqual(Entry(h, x, y), D(0)), NotEqual(Entry(h, y, x), D(0)))));
        return Disp(All("H", RealMatrices(), All("x", Modes(), All("y", Modes(), adjacency))));
    }

    private static Formula PhaseFormula()
    {
        Formula phi = F.Id("Phi"), z = F.Id("z"), x = F.Id("x");
        Formula body = Some("z", Seq(Modes(), Sp, To, Sp, Seq(Mathbb, Grp(F.Id("C")))),
            And(All("x", Modes(), Equal(Seq(Bar, new Formula.Apply(z, [x]), Bar), D(1))),
                Equal(phi, Call("diagonal", z))));
        return Disp(All("Phi", ComplexMatrices(), Iff(Call("IsUnimodularDiagonal", phi), body)));
    }

    private static Formula ClaimFormula()
    {
        Formula h = F.Id("H"), x = F.Id("x"), y = F.Id("y"), po = F.Id("Q"), pi = F.Id("R");
        Formula symmetric = Call("IsSymm", h);
        Formula nonnegative = All("x", Modes(), All("y", Modes(),
            Implies(NotEqual(x, y), LessEq(D(0), Entry(h, x, y)))));
        Formula connected = Call("Connected", Call("supportGraph", h));
        Formula propagator = Call("hamiltonianPropagator", Call("map", h, Named("ofReal")), D(1));
        Formula realizes = Some("Q", ComplexMatrices(), Some("R", ComplexMatrices(),
            And(And(Call("IsUnimodularDiagonal", po), Call("IsUnimodularDiagonal", pi)),
                Equal(Seq(po, Sp, Cdot, Sp, propagator, Sp, Cdot, Sp, pi), Named("F10")))));
        Formula body = All("H", RealMatrices(), Implies(symmetric, Implies(nonnegative,
            Implies(connected, Implies(realizes, LessEq(D(2, 5), Call("edgeCount", h)))))));
        return Disp(Iff(F.Id("claim"), body));
    }
}
