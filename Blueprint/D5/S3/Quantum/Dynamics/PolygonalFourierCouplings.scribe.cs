using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Dynamics;

internal sealed class PolygonalFourierCouplingsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Dynamics/PolygonalFourierCouplings.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumChannels/barriga2026dftbosonic");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The polygonal coupling model uses real symmetric circulant matrices with zero diagonal. Diagonal phase shifts act before and after the Hamiltonian evolution.",
        H("Polygonal couplings and the discrete Fourier transform"),
        Blocks(
            Node("fourier", "The Fourier matrix", FourierFormula(),
                "The indices are the residues represented by 0 through N - 1. The Fourier matrix uses the negative exponential convention and the normalization by the square root of N.",
                "fourier", DescribeRole.Definition),
            Node("unimodular", "Diagonal phase shifts", UnimodularFormula(),
                "A diagonal phase matrix has an entry of modulus one at every index.",
                "IsUnimodularDiagonal", DescribeRole.Definition),
            Node("polygonal", "Polygonal coupling matrices", PolygonalFormula(),
                "The coupling between i and j depends on j - i modulo N. Reversing this residue preserves the coupling, and the zero residue has zero coupling.",
                "IsPolygonalCoupling", DescribeRole.Definition),
            Node("claim", "The polygonal Fourier question", Disp(Iff(F.Id("claim"), ClaimBody())),
                "For every positive dimension, the question asks for strictly positive off-diagonal couplings and two diagonal phase matrices whose product with the propagator at time one equals the Fourier matrix exactly.",
                "claim", DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("polygonal-fourier-result"),
                DeclarationHandle.Create(Prefix + "result"), H("Positive couplings in every dimension"),
                StatementSource.FromAuthor(Disp(ClaimBody())), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("A periodic quadratic phase on the residues factors a symmetric circulant unitary as a diagonal phase, the Fourier matrix, and the same diagonal phase. Character orthogonality makes the normalized Fourier matrix unitary. Fourier conjugation diagonalizes the circulant: its eigenvalue vector is the discrete Fourier transform of its first column. The negatives of its eigenvalue arguments are real spectral angles of absolute value at most pi, and they agree at opposite residues. Their inverse Fourier kernel is therefore real and symmetric. Subtracting the mean of the angles removes the diagonal. Adding 2 pi times the quantity N minus one on the constant Fourier mode and subtracting 2 pi on every other mode preserves the exponential and raises every off-diagonal coupling by 2 pi. The original kernel has modulus at most pi, so every resulting off-diagonal coupling is strictly positive. The common phase from subtracting the mean is absorbed into the input diagonal phase."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("barriga-2026-polygonal-fourier-couplings"), ResolutionKind.Proved))),
        []));

    private static DocumentBlock Node(string id, string title, Formula formula, string prose,
        string declaration, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("polygonal-fourier-" + id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(formula), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), role);

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Field(string letter) => Seq(Mathbb, Grp(F.Id(letter)));
    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(Named(name), [.. args]);
    private static Formula Eq(Formula l, Formula r) => new Formula.Relation(l, FormulaRelationOperator.Equal, r);
    private static Formula Lt(Formula l, Formula r) => new Formula.Relation(l, FormulaRelationOperator.LessThan, r);
    private static Formula And(Formula l, Formula r) => new Formula.Logic(Parenthesized(l), FormulaLogicOperator.And, Parenthesized(r));
    private static Formula Iff(Formula l, Formula r) => new Formula.Logic(l, FormulaLogicOperator.Iff, Parenthesized(r));
    private static Formula Imp(Formula l, Formula r) => new Formula.Logic(Parenthesized(l), FormulaLogicOperator.Implies, Parenthesized(r));
    private static Formula All(string x, Formula domain, Formula body) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(x), domain, body);
    private static Formula Exists(string x, Formula domain, Formula body) => new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(x), domain, body);
    private static Formula Mul(Formula l, Formula r) => new Formula.Binary(Parenthesized(l), FormulaBinaryOperator.Multiply, Parenthesized(r));
    private static Formula Sub(Formula l, Formula r) => new Formula.Binary(Parenthesized(l), FormulaBinaryOperator.Subtract, Parenthesized(r));
    private static Formula Neg(Formula value) => new Formula.Negate(Parenthesized(value));
    private static Formula Fin(Formula n) => Call("Fin", n);
    private static Formula Mat(Formula n, Formula field) => Call("Matrix", Fin(n), Fin(n), field);
    private static Formula Fun(Formula n, Formula field) => Parenthesized(Seq(Fin(n), Sp, To, Sp, field));
    private static Formula Entry(Formula m, Formula j, Formula k) => new Formula.Subscript(Parenthesized(m), Seq(j, Comma, Sp, k));
    private static Formula Apply(Formula f, Formula x) => new Formula.Apply(f, [x]);
    private static Formula Nonzero(Formula n) => new Formula.Not(Parenthesized(Eq(n, D(0))));

    private static Formula FourierFormula()
    {
        Formula n = F.Id("N"), j = F.Id("j"), k = F.Id("k");
        Formula exponent = new Formula.Fraction(Neg(Mul(Mul(Mul(Mul(D(2), Pi), F.Id("i")), j), k)), n);
        Formula value = new Formula.Fraction(Call("exp", exponent), Call("sqrt", n));
        return Disp(All("N", Field("N"), All("j", Fin(n), All("k", Fin(n),
            Eq(Entry(Call("fourier", n), j, k), value)))));
    }

    private static Formula UnimodularFormula()
    {
        Formula n = F.Id("N"), phi = F.Id("Phi"), z = F.Id("z"), x = F.Id("x");
        Formula body = Exists("z", Fun(n, Field("C")),
            And(All("x", Fin(n), Eq(Call("norm", Apply(z, x)), D(1))), Eq(phi, Call("diagonal", z))));
        return Disp(All("N", Field("N"), All("Phi", Mat(n, Field("C")),
            Iff(Call("IsUnimodularDiagonal", phi), body))));
    }

    private static Formula PolygonalFormula()
    {
        Formula n = F.Id("N"), c = F.Id("c"), matrix = F.Id("C");
        Formula l = F.Id("l"), i = F.Id("i"), j = F.Id("j");
        Formula body = Exists("c", Fun(n, Field("R")), And(Eq(Apply(c, D(0)), D(0)),
            And(All("l", Fin(n), Eq(Apply(c, Neg(l)), Apply(c, l))),
                All("i", Fin(n), All("j", Fin(n), Eq(Entry(matrix, i, j), Apply(c, Sub(j, i))))))));
        return Disp(All("N", Field("N"), Imp(Nonzero(n), All("C", Mat(n, Field("R")),
            Iff(Call("IsPolygonalCoupling", matrix), body)))));
    }

    private static Formula ClaimBody()
    {
        Formula n = F.Id("N"), c = F.Id("C"), i = F.Id("i"), j = F.Id("j");
        Formula output = F.Id("Phiout"), input = F.Id("Phiin");
        Formula positivity = All("i", Fin(n), All("j", Fin(n),
            Imp(new Formula.Not(Parenthesized(Eq(i, j))), Lt(D(0), Entry(c, i, j)))));
        Formula cast = Call("map", c, Named("ofReal"));
        Formula evolution = Eq(Mul(Mul(output, Call("hamiltonianPropagator", cast, D(1))), input), Call("fourier", n));
        Formula phases = Exists("Phiout", Mat(n, Field("C")), Exists("Phiin", Mat(n, Field("C")),
            And(Call("IsUnimodularDiagonal", output), And(Call("IsUnimodularDiagonal", input), evolution))));
        return All("N", Field("N"), Imp(Nonzero(n), Exists("C", Mat(n, Field("R")),
            And(Call("IsPolygonalCoupling", c), And(positivity, phases)))));
    }
}
