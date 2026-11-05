using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Tomography;

internal sealed class KanachovaLiuTuPureStateDetectionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Tomography/KanachovaLiuTuPureStateDetection.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuadraticForms/kanachova2026qubitqutrit");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The fixed qubit-qutrit reconstruction has a negative real eigenvalue for every normalized entangled pure state.",
        H("Kanachova–Liu–Tu pure-state detection"),
        Blocks(
            Node("U", "The fixed local matrix", Equal(X("U"), Cast(FixedU(), MatrixType(Fin(3)))),
                "Equation (S18) in the ordered basis +1, 0, -1.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("localConjugation", "The local unitary conjugation", LocalConjugationFormula(),
                "Equation (S19): conjugation by the tensor product of the qubit identity and U.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("measured", "The measured reconstruction", MeasuredFormula(),
                """Equation (3), p. 2, with Eqs. (S18)–(S19), p. 9: the reconstruction is the average of the input and its second-factor partial transpose conjugated by the fixed local matrix. The source says: “Let @ denote the density matrix obtained by setting the 23 measured parameters to their observed values and the inaccessible 12 to zero, which is the most complete reconstruction available from the decay angular distributions alone.” The first coordinate is the qubit; qutrit indices 0, 1, 2 correspond to +1, 0, −1. The displayed literal matrix is U of Eq. (S18). Matrix.kronecker and Matrix.conjTranspose have their usual complex-matrix meanings; partialTranspose is the second-factor transpose from AbsolutePPT.Bipartite.""",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "The pure-state detection conjecture", ClaimFormula(),
                """Appendix §.7, p. 9, immediately after Proposition 1, verbatim: “We therefore *conjecture*, without proof, that @ detects every pure entangled state of this system.” The amplitude vector psi ranges over all six complex coordinates. Its squared norm is one, and it has no product factorization into a two-coordinate vector and a three-coordinate vector. Detection means that measured(rankOneDensity psi) has a strictly negative real eigenvalue with a nonzero complex eigenvector. rankOneDensity is the existing PureStateHandshake construction Matrix.vecMulVec psi (star psi). No Schmidt basis is fixed.""",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "Every entangled pure state is detected", ClaimFormula(),
                "Writing the two rows of psi as u and v, the vector (U conjugate(v), −U conjugate(u)) has expectation equal to minus the sum of the squared absolute values of the three two-by-two minors. A non-product input has a nonzero minor, so this expectation is strictly negative. The reconstruction is Hermitian. The Hermitian spectral theorem therefore supplies a negative real eigenvalue and a nonzero eigenvector. The result concerns arbitrary complex amplitudes, including zero coordinates; it imposes no restriction on either Schmidt basis.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance) => Describe.Lean(
        DescribeId.Create("klt-pure-state-" + name.ToLowerInvariant()), DeclarationHandle.Create(Prefix + name),
        H(title), StatementSource.FromAuthor(Disp(formula)), provenance,
        Blocks(SourceParagraph(prose)), role);

    private static DocumentBlock SourceParagraph(string prose)
    {
        var parts = prose.Split('@');
        return parts.Length == 1 ? Paragraph(Text(prose)) : Paragraph(
            Text(parts[0]), Math(new Formula.Subscript(Rho, Seq(Mathrm, Grp(X("meas"))))), Text(parts[1]));
    }

    private static Formula X(string name) => F.Id(name);
    private static Formula Parenthesized(Formula body) => Seq(Open, body, Close);
    private static Formula Named(string owner, string name) =>
        Seq(Operatorname, Grp(Seq(X(owner), Dot, X(name))));
    private static Formula App(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula Call(string name, params Formula[] args) => App(X(name), args);
    private static Formula Qualified(string owner, string name, params Formula[] args) => App(Named(owner, name), args);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Parenthesized(Seq(X(name), Colon, Sp, type)), Comma, Sp, body);
    private static Formula Some(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, Parenthesized(Seq(X(name), Colon, Sp, type)), Comma, Sp, body);
    private static Formula Imp(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Complex() => Seq(Mathbb, Grp(X("C")));
    private static Formula Real() => Seq(Mathbb, Grp(X("R")));
    private static Formula Fin(byte n) => Call("Fin", D(n));
    private static Formula Sites() => Parenthesized(Seq(Fin(2), Times, Sp, Fin(3)));
    private static Formula Vector() => new Formula.TypeArrow(Sites(), Complex());
    private static Formula MatrixType(Formula indices) => Call("Matrix", indices, indices, Complex());
    private static Formula Cast(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula FixedU() => Seq(Bang, Bang, OpenBracket,
        D(0), Comma, D(0), Comma, Minus, D(1), Semi,
        D(0), Comma, D(1), Comma, D(0), Semi,
        Minus, D(1), Comma, D(0), Comma, D(0), CloseBracket);

    private static Formula LocalConjugationFormula()
    {
        var rho = X("rho");
        var k = X("K");
        var rhs = Seq(Operatorname, Grp(X("let")), Sp, k, Colon, F.Eq, Sp,
            Qualified("Matrix", "kronecker", Cast(D(1), MatrixType(Fin(2))), X("U")),
            Semi, Sp, Multiply(Multiply(k, rho), Qualified("Matrix", "conjTranspose", k)));
        return All("rho", MatrixType(Sites()), Equal(Call("localConjugation", rho), rhs));
    }

    private static Formula MeasuredFormula()
    {
        var rho = X("rho");
        var rhs = Qualified("SMul", "smul", Cast(new Formula.Fraction(D(1), D(2)), Complex()),
            Add(rho, Call("localConjugation", Call("partialTranspose", rho))));
        return All("rho", MatrixType(Sites()), Equal(Call("measured", rho), rhs));
    }

    private static Formula ClaimFormula()
    {
        var psi = X("psi");
        var product = Some("a", new Formula.TypeArrow(Fin(2), Complex()),
            Some("b", new Formula.TypeArrow(Fin(3), Complex()),
                All("i", Fin(2), All("j", Fin(3),
                    Equal(App(psi, Parenthesized(Seq(X("i"), Comma, X("j")))),
                        Multiply(Call("a", X("i")), Call("b", X("j"))))))));
        var eigenpair = Some("eigenvalue", Real(), Some("w", Vector(),
            And(Seq(X("eigenvalue"), Lt, D(0)), And(NotEqual(X("w"), D(0)),
                Equal(Qualified("Matrix", "mulVec", Call("measured", Call("rankOneDensity", psi)), X("w")),
                    Qualified("SMul", "smul", Cast(X("eigenvalue"), Complex()), X("w")))))));
        return All("psi", Vector(), Imp(Equal(Call("dotProduct", Call("star", psi), psi), D(1)),
            Imp(new Formula.Not(Parenthesized(product)), eigenpair)));
    }
}
