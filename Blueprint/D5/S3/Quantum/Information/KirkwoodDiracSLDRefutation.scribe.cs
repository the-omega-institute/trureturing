using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Information;

internal sealed class KirkwoodDiracSLDRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Information/KirkwoodDiracSLDRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/HilbertOperators/sprietlangrenez2026kdreal");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A faithful nine-dimensional mixed state has a KD-real symmetric logarithmic derivative with nonzero quantum Fisher information, refuting the mixed-state exclusion conjecture.",
        H("A mixed-state KD-real SLD counterexample"),
        Blocks(
            Node("qLeft", "The left Kirkwood–Dirac distribution", QLeftFormula(),
                "The left KD distribution is the conjugate overlap multiplied by the matrix coefficient between the two orthonormal eigenbases.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("symbolLeft", "The left KD symbol", SymbolLeftFormula(),
                "The left symbol is the inverse overlap multiplied by the same matrix coefficient.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("IsKDReal", "KD-real Hermitian matrices", IsKDRealFormula(),
                "A matrix is left KD-real when it is Hermitian and the imaginary part of its left KD symbol vanishes at every pair of basis labels.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "The mixed-state conjecture", Disp(IffTo(F.Id("claim"), ClaimBody())),
                "Section 6.3, immediately after equation (6.23), states verbatim: \"In view of what precedes, it is tempting to conjecture that, if \\hat \\rho and \\hat X are both KD real, the optimal observable \\hat L must not be KD-real itself, provided \\rm I_{QF} does not vanish.\" The encoding quantifies over every positive finite dimension, two unitary bases with nonzero overlaps, every density matrix and Hermitian observable in the KD-real sector, and every Hermitian SLD solution. The source QFI is 4 times fisherSLD.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Describe.Lean(
                DescribeId.Create("slbd-result"), DeclarationHandle.Create(Prefix + "result"),
                H("The conjecture is false"),
                StatementSource.FromAuthor(Disp(new Formula.Not(Parenthesized(ClaimBody())))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "The explicit p = 3, dimension-nine witness uses the identity basis and an explicit Fourier basis, a faithful density matrix rho, the Hermitian observable X and the Hermitian matrix L. The coefficient calculations make rho, X and L KD-real; L solves the SLD equation; and the source-normalized QFI is 1/6, so the universal conclusion that every nonzero-QFI SLD is not KD-real fails."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("slbd2026"), ResolutionKind.Refuted))),
        []));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance) => Describe.Lean(
        DescribeId.Create("slbd-" + name.ToLowerInvariant()), DeclarationHandle.Create(Prefix + name),
        H(title), StatementSource.FromAuthor(Disp(formula)), provenance,
        Blocks(Paragraph(Text(prose))), role);

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Named(string name) => Seq(Operatorname, Grp(name.Split('.').SelectMany((part, index) =>
        index == 0 ? new[] { F.Id(part) } : new Formula[] { Dot, F.Id(part) }).ToArray()));
    private static Formula Call(string name, params Formula[] arguments) => new Formula.Apply(Named(name), [.. arguments]);
    private static Formula At(Formula function, params Formula[] arguments) => new Formula.Apply(function, [.. arguments]);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Exists(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula EqTo(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula NeTo(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);
    private static Formula Less(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula Both(Formula left, Formula right) => new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Imp(Formula left, Formula right) => new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula IffTo(Formula left, Formula right) => new Formula.Logic(left, FormulaLogicOperator.Iff, Parenthesized(right));
    private static Formula Mul(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Fin(Formula n) => Call("Fin", n);
    private static Formula Nat() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Complexes() => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula Matrix(Formula n) => Call("Matrix", Fin(n), Fin(n), Complexes());
    private static Formula UnitMatrix(Formula n) => Call("Matrix.unitaryGroup", Fin(n), Complexes());
    private static Formula MatrixEntry(Formula matrix, Formula i, Formula j) => At(matrix, i, j);
    private static Formula ConjTranspose(Formula matrix) => Call("conjTranspose", matrix);
    private static Formula Overlap(Formula a, Formula b, Formula x, Formula k) =>
        MatrixEntry(Mul(ConjTranspose(Call("val", a)), Call("val", b)), x, k);
    private static Formula Coefficient(Formula a, Formula c, Formula b, Formula x, Formula k) =>
        MatrixEntry(Mul(Mul(ConjTranspose(Call("val", a)), c), Call("val", b)), x, k);
    private static Formula Symbol(Formula a, Formula b, Formula c, Formula x, Formula k) =>
        Mul(Call("Inv.inv", Overlap(a, b, x, k)), Coefficient(a, c, b, x, k));
    private static Formula KDReal(Formula a, Formula b, Formula c) =>
        Call("IsKDReal", a, b, c);
    private static Formula QLeftFormula()
    {
        Formula d = F.Id("d"), a = F.Id("a"), b = F.Id("b"), c = F.Id("C"), x = F.Id("x"), k = F.Id("k");
        Formula lhs = At(Call("qLeft", a, b, c), x, k);
        Formula rhs = Mul(Call("star", Overlap(a, b, x, k)), Coefficient(a, c, b, x, k));
        return All("d", Nat(), All("a", UnitMatrix(d), All("b", UnitMatrix(d),
            All("C", Matrix(d), All("x", Fin(d), All("k", Fin(d), EqTo(lhs, rhs)))))));
    }
    private static Formula SymbolLeftFormula()
    {
        Formula d = F.Id("d"), a = F.Id("a"), b = F.Id("b"), c = F.Id("C"), x = F.Id("x"), k = F.Id("k");
        Formula lhs = At(Call("symbolLeft", a, b, c), x, k);
        return All("d", Nat(), All("a", UnitMatrix(d), All("b", UnitMatrix(d),
            All("C", Matrix(d), All("x", Fin(d), All("k", Fin(d), EqTo(lhs, Symbol(a, b, c, x, k))))))));
    }
    private static Formula IsKDRealFormula()
    {
        Formula d = F.Id("d"), a = F.Id("a"), b = F.Id("b"), c = F.Id("C"), x = F.Id("x"), k = F.Id("k");
        Formula hermitian = Call("IsHermitian", c);
        Formula imaginary = EqTo(Call("Complex.im", Symbol(a, b, c, x, k)), D(0));
        Formula body = Both(hermitian, All("x", Fin(d), All("k", Fin(d), imaginary)));
        return All("d", Nat(), All("a", UnitMatrix(d), All("b", UnitMatrix(d),
            All("C", Matrix(d), EqTo(KDReal(a, b, c), body)))));
    }
    private static Formula ClaimBody()
    {
        Formula d = F.Id("d"), a = F.Id("a"), b = F.Id("b"), rho = F.Id("rho"), x = F.Id("X"), l = F.Id("L"), k = F.Id("k");
        Formula nonzero = All("x", Fin(d), All("k", Fin(d), NeTo(Overlap(a, b, F.Id("x"), k), D(0))));
        Formula density = Call("D5.S3.Quantum.Information.SLDSpectralEnergy.IsDensity", rho);
        Formula sld = Call("D5.S3.Quantum.Information.FisherDiscord.Defs.IsSLD", rho, x, l);
        Formula qfi = NeTo(Mul(D(4), Call("D5.S3.Quantum.Information.FisherDiscord.Defs.fisherSLD", rho, l)), D(0));
        Formula conclusion = Both(
            Exists("L", Matrix(d), Call("IsSLD", rho, x, l)),
            All("L", Matrix(d), Imp(sld, Imp(qfi, new Formula.Not(Parenthesized(KDReal(a, b, l)))))));
        Formula inner = All("rho", Matrix(d), All("X", Matrix(d),
            Imp(density, Imp(KDReal(a, b, rho), Imp(KDReal(a, b, x), conclusion)))));
        return All("d", Nat(), Imp(Less(D(0), d), All("a", UnitMatrix(d), All("b", UnitMatrix(d),
            Imp(nonzero, inner)))));
    }
}
